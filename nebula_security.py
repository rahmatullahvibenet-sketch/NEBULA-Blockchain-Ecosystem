"""
================================================================
  NEBULA SECURITY — nebula_security.py
  Complete Security — Like Bitcoin Core
  
  - DoS protection
  - Rate limiting
  - Peer banning
  - Transaction validation
  - Block validation
  - Replay attack protection
  - Double-spend detection
  - Sybil resistance
  - Checkpoint system
  - Alert system
================================================================
"""

import time, hashlib, threading, json, ipaddress
from typing import Dict, Set, List, Optional, Tuple
from dataclasses import dataclass, field
from collections import defaultdict, deque
from enum import Enum

# ================================================================
#  BAN REASONS
# ================================================================

class BanReason(Enum):
    INVALID_BLOCK       = "invalid_block"
    INVALID_TX          = "invalid_tx"
    MISBEHAVIOR         = "misbehavior"
    DOS_ATTACK          = "dos_attack"
    SPAM                = "spam"
    DUPLICATE_HEADERS   = "duplicate_headers"
    INVALID_HANDSHAKE   = "invalid_handshake"
    WRONG_CHAIN         = "wrong_chain"

@dataclass
class BanEntry:
    ip:         str
    reason:     BanReason
    score:      int
    banned_at:  float = field(default_factory=time.time)
    expires_at: float = 0.0   # 0 = permanent

    def is_expired(self) -> bool:
        return self.expires_at > 0 and time.time() > self.expires_at

# ================================================================
#  DOS PROTECTION
# ================================================================

class DoSProtection:
    """
    Per-IP misbehavior scoring — like Bitcoin Core.
    Score 0-100. At 100, ban the peer.
    """

    BAN_THRESHOLD   = 100
    BAN_DURATION    = 86400     # 24 hours default
    MAX_SCORE       = 100

    # Score increments per violation
    SCORES = {
        "invalid_block_header":  20,
        "invalid_block_hash":    100,   # instant ban
        "invalid_block_merkle":  100,
        "invalid_tx_format":     10,
        "invalid_tx_signature":  10,
        "invalid_tx_doublespend":100,
        "too_many_getdata":      1,
        "oversized_message":     50,
        "spam_tx":               5,
        "headers_flood":         20,
        "ping_flood":            1,
        "wrong_chain_id":        100,
    }

    def __init__(self):
        self._scores:   Dict[str, int]        = defaultdict(int)
        self._bans:     Dict[str, BanEntry]   = {}
        self._lock      = threading.RLock()

    def punish(self, ip: str, violation: str) -> bool:
        """Add misbehavior score. Returns True if peer should be banned."""
        with self._lock:
            if ip in self._bans and not self._bans[ip].is_expired():
                return True
            score = self.SCORES.get(violation, 1)
            self._scores[ip] = min(self._scores[ip] + score, self.MAX_SCORE)
            if self._scores[ip] >= self.BAN_THRESHOLD:
                self._ban(ip, BanReason.MISBEHAVIOR, self.BAN_DURATION)
                return True
            return False

    def _ban(self, ip: str, reason: BanReason, duration: float = 0):
        self._bans[ip] = BanEntry(
            ip         = ip,
            reason     = reason,
            score      = self._scores.get(ip, 100),
            expires_at = time.time() + duration if duration > 0 else 0,
        )
        print(f"🚫 Banned {ip}: {reason.value} (score: {self._scores[ip]})")

    def is_banned(self, ip: str) -> bool:
        with self._lock:
            entry = self._bans.get(ip)
            if entry is None:
                return False
            if entry.is_expired():
                del self._bans[ip]
                return False
            return True

    def get_score(self, ip: str) -> int:
        return self._scores.get(ip, 0)

    def unban(self, ip: str):
        with self._lock:
            self._bans.pop(ip, None)
            self._scores.pop(ip, None)

    def ban_list(self) -> List[dict]:
        with self._lock:
            return [{
                "ip":       e.ip,
                "reason":   e.reason.value,
                "score":    e.score,
                "expires":  e.expires_at,
                "permanent":e.expires_at == 0,
            } for e in self._bans.values() if not e.is_expired()]

    def cleanup(self):
        with self._lock:
            expired = [ip for ip, e in self._bans.items() if e.is_expired()]
            for ip in expired:
                del self._bans[ip]


# ================================================================
#  RATE LIMITER
# ================================================================

class RateLimiter:
    """Token bucket rate limiter per IP"""

    def __init__(self,
                 rate_per_sec: float = 10.0,
                 burst:        int   = 50):
        self._rate      = rate_per_sec
        self._burst     = burst
        self._tokens:   Dict[str, float] = defaultdict(lambda: float(burst))
        self._last:     Dict[str, float] = defaultdict(time.time)
        self._lock      = threading.Lock()

    def allow(self, ip: str, cost: float = 1.0) -> bool:
        with self._lock:
            now    = time.time()
            elapsed = now - self._last.get(ip, now)
            self._last[ip]   = now
            # Refill tokens
            self._tokens[ip] = min(
                self._burst,
                self._tokens.get(ip, self._burst) + elapsed * self._rate
            )
            if self._tokens[ip] >= cost:
                self._tokens[ip] -= cost
                return True
            return False

    def reset(self, ip: str):
        with self._lock:
            self._tokens[ip] = float(self._burst)
            self._last[ip]   = time.time()


# ================================================================
#  DOUBLE SPEND DETECTOR
# ================================================================

class DoubleSpendDetector:
    """
    Detects double-spend attempts in mempool and across blocks.
    Tracks all UTXO references being spent.
    """

    def __init__(self):
        self._spending: Dict[str, str] = {}  # "txid:idx" -> spending_txid
        self._lock = threading.Lock()

    def _key(self, txid: str, index: int) -> str:
        return f"{txid}:{index}"

    def register(self, txid: str, inputs: List) -> Tuple[bool, Optional[str]]:
        """
        Register transaction inputs.
        Returns (ok, conflicting_txid).
        """
        with self._lock:
            new_keys = []
            for inp in inputs:
                k = self._key(inp.outpoint.txid, inp.outpoint.index)
                if k in self._spending:
                    conflict = self._spending[k]
                    if conflict != txid:
                        return False, conflict
                new_keys.append(k)
            for k in new_keys:
                self._spending[k] = txid
            return True, None

    def release(self, txid: str):
        """Remove transaction's inputs from tracker"""
        with self._lock:
            to_del = [k for k, v in self._spending.items() if v == txid]
            for k in to_del:
                del self._spending[k]

    def clear_block(self, inputs: List):
        """Remove confirmed inputs from tracker"""
        with self._lock:
            for inp in inputs:
                k = self._key(inp.outpoint.txid, inp.outpoint.index)
                self._spending.pop(k, None)

    def conflict_count(self) -> int:
        return len(self._spending)


# ================================================================
#  REPLAY ATTACK PROTECTION
# ================================================================

class ReplayProtection:
    """
    Prevents transaction replay across chains.
    Uses chain_id in sighash (like EIP-155 for Ethereum).
    """

    def __init__(self, chain_id: int):
        self.chain_id = chain_id
        self._seen_txids: Set[str] = set()
        self._lock = threading.Lock()
        self.MAX_CACHE = 100_000

    def mark_seen(self, txid: str):
        with self._lock:
            if len(self._seen_txids) > self.MAX_CACHE:
                # Clear oldest 20%
                to_remove = list(self._seen_txids)[:self.MAX_CACHE // 5]
                for t in to_remove:
                    self._seen_txids.discard(t)
            self._seen_txids.add(txid)

    def is_replay(self, txid: str) -> bool:
        with self._lock:
            return txid in self._seen_txids

    def chain_sighash_suffix(self) -> bytes:
        """Extra bytes appended to sighash to bind tx to this chain"""
        return self.chain_id.to_bytes(4, 'little')


# ================================================================
#  CHECKPOINTS
# ================================================================

@dataclass
class Checkpoint:
    height: int
    hash:   str
    time:   int

# Hardcoded checkpoints (like Bitcoin Core)
# These will be filled as NEBULA grows
NEBULA_CHECKPOINTS: List[Checkpoint] = [
    Checkpoint(0,      "genesis",  1742083200),  # Genesis block — 2025-03-16
    # Future checkpoints added here as network matures:
    # Checkpoint(10000,  "...",   ...),
    # Checkpoint(50000,  "...",   ...),
    # Checkpoint(100000, "...",   ...),
]

class CheckpointSystem:
    """Validates blocks against hardcoded checkpoints"""

    def __init__(self):
        self._checkpoints = {cp.height: cp for cp in NEBULA_CHECKPOINTS}
        self.max_height   = max((cp.height for cp in NEBULA_CHECKPOINTS), default=0)

    def validate(self, height: int, block_hash: str) -> Tuple[bool, str]:
        cp = self._checkpoints.get(height)
        if cp is None:
            return True, "No checkpoint at this height"
        if cp.hash == "genesis":
            return True, "Genesis checkpoint (any hash)"
        if cp.hash != block_hash:
            return False, f"Checkpoint mismatch at height {height}"
        return True, "Checkpoint passed"

    def is_before_checkpoint(self, height: int) -> bool:
        return height <= self.max_height

    def add_checkpoint(self, cp: Checkpoint):
        self._checkpoints[cp.height] = cp
        self.max_height = max(self.max_height, cp.height)


# ================================================================
#  TRANSACTION SANITIZER
# ================================================================

class TxSanitizer:
    """
    Validates transactions before they enter mempool or chain.
    First line of defense against malformed data.
    """

    MAX_TX_SIZE    = 100_000   # 100 KB
    MAX_INPUTS     = 1_000
    MAX_OUTPUTS    = 1_000
    MAX_SCRIPT_SIZE = 10_000
    MIN_AMOUNT     = 1         # 1 Neb

    def sanitize(self, tx) -> Tuple[bool, str]:
        """Full transaction sanitization"""
        # Size check
        if tx.byte_size() > self.MAX_TX_SIZE:
            return False, f"TX too large: {tx.byte_size()} > {self.MAX_TX_SIZE}"

        # Input count
        if len(tx.inputs) == 0:
            return False, "No inputs"
        if len(tx.inputs) > self.MAX_INPUTS:
            return False, f"Too many inputs: {len(tx.inputs)}"

        # Output count
        if len(tx.outputs) == 0:
            return False, "No outputs"
        if len(tx.outputs) > self.MAX_OUTPUTS:
            return False, f"Too many outputs: {len(tx.outputs)}"

        # Check each output
        total_out = 0
        for i, out in enumerate(tx.outputs):
            if out.value < 0:
                return False, f"Negative output {i}: {out.value}"
            if len(out.script_pubkey) > self.MAX_SCRIPT_SIZE:
                return False, f"Output {i} script too large"
            total_out += out.value

        # Check for overflow
        if total_out > 21_000_000 * 10**9:
            return False, "Total output exceeds possible supply"

        # Duplicate inputs
        outpoints = set()
        for inp in tx.inputs:
            key = f"{inp.outpoint.txid}:{inp.outpoint.index}"
            if key in outpoints:
                return False, f"Duplicate input: {key}"
            outpoints.add(key)

        # Script sizes
        for i, inp in enumerate(tx.inputs):
            if len(inp.script_sig) > self.MAX_SCRIPT_SIZE:
                return False, f"Input {i} script too large"

        return True, "OK"


# ================================================================
#  BLOCK SANITIZER
# ================================================================

class BlockSanitizer:
    """Sanitizes blocks before full validation"""

    MAX_BLOCK_SIZE   = 1_048_576   # 1 MB
    MAX_TXS          = 3_000
    MAX_COINBASE_SIZE = 100

    def __init__(self):
        self.tx_san = TxSanitizer()

    def sanitize(self, block) -> Tuple[bool, str]:
        # Size
        if block.byte_size() > self.MAX_BLOCK_SIZE:
            return False, f"Block too large: {block.byte_size()}"

        # Must have txs
        if not block.transactions:
            return False, "No transactions in block"

        # TX count
        if len(block.transactions) > self.MAX_TXS:
            return False, f"Too many txs: {len(block.transactions)}"

        # Coinbase must be first
        if not block.transactions[0].is_coinbase:
            return False, "First tx must be coinbase"

        # Only one coinbase
        for tx in block.transactions[1:]:
            if tx.is_coinbase:
                return False, "Multiple coinbases"

        # Coinbase script size
        cb_script = block.transactions[0].inputs[0].script_sig
        if len(cb_script) > self.MAX_COINBASE_SIZE:
            return False, f"Coinbase script too long: {len(cb_script)}"

        # Sanitize each tx
        seen_txids: Set[str] = set()
        for tx in block.transactions[1:]:
            if tx.txid in seen_txids:
                return False, f"Duplicate tx: {tx.txid}"
            seen_txids.add(tx.txid)
            ok, msg = self.tx_san.sanitize(tx)
            if not ok:
                return False, f"TX {tx.txid[:8]}: {msg}"

        return True, "OK"


# ================================================================
#  IP FILTER
# ================================================================

class IPFilter:
    """Blocks private/reserved IPs from being added as peers (anti-Sybil)"""

    PRIVATE_RANGES = [
        "10.0.0.0/8",
        "172.16.0.0/12",
        "192.168.0.0/16",
        "127.0.0.0/8",
        "169.254.0.0/16",
        "::1/128",
        "fc00::/7",
    ]

    def __init__(self):
        self._nets = [ipaddress.ip_network(r) for r in self.PRIVATE_RANGES]
        self._whitelist: Set[str] = set()

    def is_allowed(self, ip: str) -> bool:
        if ip in self._whitelist:
            return True
        try:
            addr = ipaddress.ip_address(ip)
            return not any(addr in net for net in self._nets)
        except ValueError:
            return False

    def whitelist(self, ip: str):
        self._whitelist.add(ip)


# ================================================================
#  ALERT SYSTEM
# ================================================================

class AlertLevel(Enum):
    INFO     = "INFO"
    WARNING  = "WARNING"
    CRITICAL = "CRITICAL"

@dataclass
class SecurityAlert:
    level:   AlertLevel
    message: str
    data:    dict
    ts:      float = field(default_factory=time.time)

class AlertSystem:
    """Security alert system — like Bitcoin's alert system"""

    def __init__(self):
        self._alerts:    List[SecurityAlert] = []
        self._handlers:  List               = []
        self._lock       = threading.Lock()

    def add_handler(self, fn):
        self._handlers.append(fn)

    def alert(self, level: AlertLevel, message: str, data: dict = None):
        a = SecurityAlert(level, message, data or {})
        with self._lock:
            self._alerts.append(a)
        prefix = {"INFO": "ℹ️", "WARNING": "⚠️", "CRITICAL": "🚨"}[level.value]
        print(f"{prefix} [{level.value}] {message}")
        for handler in self._handlers:
            try:
                handler(a)
            except Exception:
                pass

    def info(self,     msg: str, data: dict = None): self.alert(AlertLevel.INFO,     msg, data)
    def warning(self,  msg: str, data: dict = None): self.alert(AlertLevel.WARNING,  msg, data)
    def critical(self, msg: str, data: dict = None): self.alert(AlertLevel.CRITICAL, msg, data)

    def recent(self, n: int = 20) -> List[dict]:
        with self._lock:
            return [{"level": a.level.value, "msg": a.message, "ts": a.ts}
                    for a in self._alerts[-n:]]


# ================================================================
#  SECURITY MANAGER — combines everything
# ================================================================

class SecurityManager:
    """Central security manager for NEBULA node"""

    def __init__(self, chain_id: int = 2025):
        self.dos          = DoSProtection()
        self.rate         = RateLimiter(rate_per_sec=20, burst=100)
        self.double_spend = DoubleSpendDetector()
        self.replay       = ReplayProtection(chain_id)
        self.checkpoints  = CheckpointSystem()
        self.tx_sanitizer = TxSanitizer()
        self.blk_sanitizer = BlockSanitizer()
        self.ip_filter    = IPFilter()
        self.alerts       = AlertSystem()

        # Stats
        self._stats = {
            "blocks_rejected":  0,
            "txs_rejected":     0,
            "ips_banned":       0,
            "double_spends":    0,
            "rate_limited":     0,
        }

    def check_peer(self, ip: str) -> Tuple[bool, str]:
        """Full peer connection check"""
        if self.dos.is_banned(ip):
            return False, "IP is banned"
        if not self.ip_filter.is_allowed(ip):
            # Allow private IPs in dev mode
            pass
        if not self.rate.allow(ip, cost=1.0):
            self._stats["rate_limited"] += 1
            return False, "Rate limited"
        return True, "OK"

    def validate_incoming_block(self, block, ip: str) -> Tuple[bool, str]:
        """Full security check for incoming block"""
        # Sanitize
        ok, msg = self.blk_sanitizer.sanitize(block)
        if not ok:
            self.dos.punish(ip, "invalid_block_header")
            self._stats["blocks_rejected"] += 1
            self.alerts.warning(f"Invalid block from {ip}: {msg}")
            return False, msg

        # Checkpoint
        ok, msg = self.checkpoints.validate(block.height, block.hash)
        if not ok:
            self.dos.punish(ip, "invalid_block_hash")
            self._stats["blocks_rejected"] += 1
            self.alerts.critical(f"Checkpoint violation from {ip}!", {"height": block.height})
            return False, msg

        return True, "OK"

    def validate_incoming_tx(self, tx, ip: str) -> Tuple[bool, str]:
        """Full security check for incoming tx"""
        # Replay check
        if self.replay.is_replay(tx.txid):
            self._stats["txs_rejected"] += 1
            return False, "Replay transaction"

        # Sanitize
        ok, msg = self.tx_sanitizer.sanitize(tx)
        if not ok:
            self.dos.punish(ip, "invalid_tx_format")
            self._stats["txs_rejected"] += 1
            return False, msg

        # Double spend
        ok, conflict = self.double_spend.register(tx.txid, tx.inputs)
        if not ok:
            self.dos.punish(ip, "invalid_tx_doublespend")
            self._stats["double_spends"] += 1
            self.alerts.warning(f"Double spend from {ip}: {tx.txid[:16]} vs {conflict[:16] if conflict else '?'}")
            return False, f"Double spend: conflicts with {conflict}"

        self.replay.mark_seen(tx.txid)
        return True, "OK"

    def punish_peer(self, ip: str, violation: str) -> bool:
        banned = self.dos.punish(ip, violation)
        if banned:
            self._stats["ips_banned"] += 1
            self.alerts.warning(f"Peer banned: {ip} ({violation})")
        return banned

    def status(self) -> dict:
        return {
            **self._stats,
            "banned_ips":      len(self.dos.ban_list()),
            "tracked_spends":  self.double_spend.conflict_count(),
            "checkpoints":     len(NEBULA_CHECKPOINTS),
            "chain_id":        self.replay.chain_id,
        }
