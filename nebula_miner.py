"""
================================================================
  NEBULA BLOCKCHAIN — nebula_miner.py
  Production-Grade Proof-of-Work Miner

  Architecture:
    - True parallel mining via multiprocessing (bypasses GIL)
    - Each CPU core runs an independent mining process
    - Shared memory for inter-process coordination
    - Automatic nonce range partitioning per worker
    - Real-time hash rate measurement via ctypes shared memory
    - Difficulty-aware target comparison (256-bit integer)
    - Halving-aware reward calculation

  Author  : Zayn Quantum
  License : MIT — Open to All Humanity
  Launch  : 2025-03-16
================================================================
"""

import multiprocessing as mp
import threading
import time
import struct
import hashlib
import ctypes
import os
from typing import Optional, Callable, List
from dataclasses import dataclass, field

from nebula_core import (
    Block, BlockHeader, Transaction, MerkleTree,
    NEBULABlockchain, mining_reward, halving_era,
    bits_to_target, sha256d, DECIMALS, CHAIN_NAME,
    MAX_NONCE, TARGET_BLOCK_TIME, INITIAL_BITS,
    INITIAL_BLOCK_REWARD, HALVING_INTERVAL,
)

# ================================================================
#  CONSTANTS
# ================================================================
MAX_WORKERS     = mp.cpu_count()
HASH_BATCH      = 50_000      # hashes per batch before checking stop
STATS_INTERVAL  = 2.0         # seconds between stats emission
NONCE_MAX       = 0xFFFF_FFFF # 32-bit nonce space

# ================================================================
#  WORKER — runs in separate OS process (no GIL)
# ================================================================
def _worker(header76: bytes, target32: bytes,
            n_start: int, n_end: int,
            q: mp.Queue, stop: mp.Value, counter: mp.Value):
    """
    Pure mining loop — one process per CPU core.
    Uses raw hashlib.sha256 with struct for maximum speed.
    """
    sha  = hashlib.sha256
    tgt  = int.from_bytes(target32, 'big')
    buf  = bytearray(header76 + b'\x00\x00\x00\x00')
    n    = n_start
    cnt  = 0

    while n <= n_end:
        if stop.value:
            return
        # Batch loop — avoid Python overhead per hash
        end = min(n + HASH_BATCH, n_end + 1)
        while n < end:
            struct.pack_into('<I', buf, 76, n)
            # SHA256d — identical to Bitcoin
            h = sha(sha(buf).digest()).digest()
            if int.from_bytes(h, 'big') < tgt:
                q.put(n)
                with stop.get_lock():
                    stop.value = 1
                return
            n += 1
        cnt += HASH_BATCH
        with counter.get_lock():
            counter.value += HASH_BATCH

# ================================================================
#  STATS
# ================================================================
class MiningStats:
    def __init__(self):
        self._total   = mp.Value(ctypes.c_uint64, 0)
        self._blocks  = mp.Value(ctypes.c_uint32, 0)
        self._t0      = time.time()
        self._snap    = 0
        self._snap_t  = time.time()
        self._rate    = 0.0
        self._lock    = threading.Lock()

    def counter(self):            # shared with workers
        return self._total

    def add_block(self):
        with self._blocks.get_lock():
            self._blocks.value += 1

    def hash_rate(self) -> float:
        with self._lock:
            now = time.time()
            dt  = now - self._snap_t
            if dt >= STATS_INTERVAL:
                cur        = self._total.value
                self._rate = (cur - self._snap) / dt
                self._snap   = cur
                self._snap_t = now
        return self._rate

    def to_dict(self) -> dict:
        hr = self.hash_rate()
        return {
            "hash_rate_khs" : hr / 1e3,
            "hash_rate_mhs" : hr / 1e6,
            "hashes_total"  : self._total.value,
            "blocks_found"  : self._blocks.value,
            "uptime_secs"   : time.time() - self._t0,
        }

# ================================================================
#  BLOCK TEMPLATE
# ================================================================
@dataclass
class BlockTemplate:
    height        : int
    prev_hash     : str
    merkle_root   : str
    timestamp     : int
    bits          : int
    reward_neb    : int
    miner_address : str
    transactions  : list = field(default_factory=list)

    def header76(self) -> bytes:
        return struct.pack(
            '<I32s32sIII',
            1,
            bytes.fromhex(self.prev_hash),
            bytes.fromhex(self.merkle_root),
            self.timestamp,
            self.bits,
            0,           # nonce placeholder — workers overwrite at offset 76
        )

    def target32(self) -> bytes:
        return bits_to_target(self.bits).to_bytes(32, 'big')

# ================================================================
#  PRODUCTION MINER
# ================================================================
class NEBULAMiner:
    """
    Multi-process PoW miner for NEBULA mainnet.

    One OS process per CPU core — each owns a nonce partition.
    True parallelism: no GIL, no shared interpreter state.
    """

    def __init__(
        self,
        blockchain    : NEBULABlockchain,
        miner_address : str,
        num_workers   : int = 0,
        on_block      : Optional[Callable] = None,
        on_stats      : Optional[Callable] = None,
    ):
        self.blockchain    = blockchain
        self.miner_address = miner_address
        self.num_workers   = num_workers or MAX_WORKERS
        self.on_block      = on_block
        self.on_stats      = on_stats
        self.stats         = MiningStats()
        self._running      = False
        self._stop_ev      = threading.Event()
        self._coord        : Optional[threading.Thread] = None
        self._procs        : List[mp.Process] = []

    # ── Public ────────────────────────────────────────────────
    def start(self):
        if self._running:
            return
        self._running = True
        self._stop_ev.clear()
        self._coord = threading.Thread(
            target=self._loop, name="NEB-Coord", daemon=True)
        self._coord.start()

    def stop(self):
        self._running = False
        self._stop_ev.set()
        self._kill()
        if self._coord:
            self._coord.join(timeout=5)

    def is_running(self) -> bool:
        return self._running

    def get_stats(self) -> dict:
        return self.stats.to_dict()

    # ── Coordinator ───────────────────────────────────────────
    def _loop(self):
        while self._running and not self._stop_ev.is_set():
            try:
                tmpl = self._template()
                if tmpl is None:
                    time.sleep(1)
                    continue
                nonce = self._mine(tmpl)
                if nonce is not None and self._running:
                    blk = self._assemble(tmpl, nonce)
                    if blk and self._submit(blk):
                        self.stats.add_block()
                        if self.on_block:
                            self.on_block(blk, self.stats.to_dict())
            except Exception as e:
                if self._running:
                    print(f"[Miner] Error: {e}")
                    time.sleep(2)

    def _mine(self, tmpl: BlockTemplate) -> Optional[int]:
        n        = self.num_workers
        h76      = bytes(tmpl.header76())
        t32      = tmpl.target32()
        q        = mp.Queue()
        stop     = mp.Value(ctypes.c_uint8, 0)
        counter  = self.stats.counter()

        # Partition nonce space evenly
        step   = NONCE_MAX // n
        ranges = [(i * step, (i+1)*step - 1) for i in range(n)]
        ranges[-1] = (ranges[-1][0], NONCE_MAX)

        self._procs = []
        for s, e in ranges:
            p = mp.Process(
                target=_worker,
                args=(h76, t32, s, e, q, stop, counter),
                daemon=True,
            )
            p.start()
            self._procs.append(p)

        # Stats thread
        threading.Thread(
            target=self._emit_stats, daemon=True).start()

        nonce = None
        while True:
            if self._stop_ev.is_set():
                with stop.get_lock():
                    stop.value = 1
                break
            try:
                nonce = q.get(timeout=0.5)
                break
            except Exception:
                if all(not p.is_alive() for p in self._procs):
                    break

        self._kill()
        return nonce

    def _emit_stats(self):
        while self._running and not self._stop_ev.is_set():
            if self.on_stats:
                self.on_stats(self.stats.to_dict())
            time.sleep(STATS_INTERVAL)

    def _kill(self):
        for p in self._procs:
            try:
                if p.is_alive():
                    p.terminate()
                    p.join(timeout=2)
            except Exception:
                pass
        self._procs.clear()

    # ── Block assembly ────────────────────────────────────────
    def _template(self) -> Optional[BlockTemplate]:
        try:
            chain  = self.blockchain
            height = chain.height + 1
            cb_tx  = chain.build_coinbase(
                height=height, miner_address=self.miner_address,
                extra_data=b'NEBULA/' + str(height).encode())
            txs    = [cb_tx] + chain.mempool_top(max_count=2999)
            root   = MerkleTree.compute_root([tx.txid() for tx in txs])
            return BlockTemplate(
                height=height,
                prev_hash=chain.tip_hash(),
                merkle_root=root,
                timestamp=int(time.time()),
                bits=chain.next_bits(),
                reward_neb=mining_reward(height),
                miner_address=self.miner_address,
                transactions=txs,
            )
        except Exception as e:
            print(f"[Miner] Template error: {e}")
            return None

    def _assemble(self, tmpl: BlockTemplate, nonce: int) -> Optional[Block]:
        try:
            hdr = BlockHeader(
                version=1, prev_hash=tmpl.prev_hash,
                merkle_root=tmpl.merkle_root,
                timestamp=tmpl.timestamp,
                bits=tmpl.bits, nonce=nonce)
            return Block(header=hdr, transactions=tmpl.transactions)
        except Exception as e:
            print(f"[Miner] Assemble error: {e}")
            return None

    def _submit(self, block: Block) -> bool:
        try:
            ok, msg = self.blockchain.add_block(block)
            h   = block.header.block_hash()
            r   = block.transactions[0].outputs[0].value / 10**DECIMALS
            ht  = self.blockchain.height
            if ok:
                print(f"[Miner] BLOCK #{ht} | {h[:16]}... | {r:.9f} NBL")
            else:
                print(f"[Miner] Rejected #{ht}: {msg}")
            return ok
        except Exception as e:
            print(f"[Miner] Submit error: {e}")
            return False

# ================================================================
#  DEMO — single-process, for CLI testing
# ================================================================
def mine_one_block_demo(
    blockchain   : NEBULABlockchain,
    miner_address: str,
    timeout_secs : int = 60,
) -> Optional[Block]:
    height  = blockchain.height + 1
    prev    = blockchain.tip_hash()
    bits    = blockchain.next_bits()
    ts      = int(time.time())
    cb_tx   = blockchain.build_coinbase(height=height, miner_address=miner_address)
    root    = MerkleTree.compute_root([cb_tx.txid()])
    target  = bits_to_target(bits)
    buf     = bytearray(struct.pack('<I32s32sIII', 1,
                bytes.fromhex(prev), bytes.fromhex(root), ts, bits, 0))
    t0      = time.time()
    for nonce in range(NONCE_MAX + 1):
        if time.time() - t0 > timeout_secs:
            return None
        struct.pack_into('<I', buf, 76, nonce)
        h = hashlib.sha256(hashlib.sha256(buf).digest()).digest()
        if int.from_bytes(h, 'big') < target:
            hdr = BlockHeader(1, prev, root, ts, bits, nonce)
            return Block(header=hdr, transactions=[cb_tx])
    return None

# ================================================================
#  HALVING SCHEDULE
# ================================================================
def halving_schedule(height: int = 0) -> dict:
    schedule = []
    for era in range(10):
        reward = INITIAL_BLOCK_REWARD >> era
        if reward == 0:
            break
        schedule.append({
            "era"        : era + 1,
            "start_block": era * HALVING_INTERVAL,
            "end_block"  : (era + 1) * HALVING_INTERVAL - 1,
            "reward_nbl" : reward / 10**DECIMALS,
            "active"     : era == height // HALVING_INTERVAL,
            "year_start" : 2025 + era * 4,
            "year_end"   : 2029 + era * 4,
        })
    era_now = height // HALVING_INTERVAL
    return {
        "schedule"        : schedule,
        "current_height"  : height,
        "current_era"     : era_now + 1,
        "current_reward"  : (INITIAL_BLOCK_REWARD >> era_now) / 10**DECIMALS,
        "next_halving_at" : (era_now + 1) * HALVING_INTERVAL,
        "blocks_to_next"  : HALVING_INTERVAL - (height % HALVING_INTERVAL),
    }

# ================================================================
if __name__ == "__main__":
    print(f"NEBULA Miner — use nebula_cli.py mine")
    print(f"CPU cores: {MAX_WORKERS}")
    s = halving_schedule(0)
    print(f"Era {s['current_era']} | Reward: {s['current_reward']} NBL")
    print(f"Next halving: block {s['next_halving_at']:,}")
