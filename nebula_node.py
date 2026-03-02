"""
================================================================
  NEBULA NODE — nebula_node.py
  Complete Node — Blockchain + Mining + P2P + Wallet + Explorer
  
  How to run:
    python3 nebula_node.py                  # full node
    python3 nebula_node.py --mine           # mine blocks
    python3 nebula_node.py --wallet         # wallet only
    python3 nebula_node.py --info           # chain info
================================================================
"""

import sys, os, json, time, threading, argparse
from pathlib import Path

# Add current directory to path
sys.path.insert(0, os.path.dirname(__file__))

from nebula_core   import NEBULABlockchain, CHAIN_NAME, CHAIN_SYMBOL, DECIMALS, halving_era, mining_reward
from nebula_miner  import NEBULAMiner
from nebula_network import P2PNode, DEFAULT_PORT
from nebula_wallet import NEBULAWallet, BIP39

BANNER = """
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║   🌌  N E B U L A   B L O C K C H A I N                     ║
║                                                              ║
║   No Government · No Bank · No Permission Needed            ║
║   Created by Zayn Quantum — Open to the Entire World 🌍   ║
║   Open Source · Permissionless · Borderless               ║
║                                                              ║
║   Supply : 10,700,000 NBL (fixed forever)                   ║
║   Halving: Every 210,000 blocks (like Bitcoin)              ║
║   Reward : 50 → 25 → 12.5 → 6.25 NBL                       ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
"""

# ================================================================
#  BLOCK EXPLORER (in-memory)
# ================================================================

class BlockExplorer:
    """Simple block explorer — search blocks, txs, addresses"""

    def __init__(self, bc: NEBULABlockchain):
        self.bc = bc

    def block_info(self, height_or_hash: str) -> Optional[dict]:
        try:
            height = int(height_or_hash)
            blk = self.bc.get_block(height)
        except ValueError:
            blk = self.bc.get_block_by_hash(height_or_hash)
        return blk.to_dict() if blk else None

    def tx_info(self, txid: str) -> Optional[dict]:
        for blk in reversed(self.bc._chain[-100:]):
            for tx in blk.transactions:
                if tx.txid == txid:
                    d = tx.to_dict()
                    d["block_hash"]   = blk.hash
                    d["block_height"] = blk.height
                    d["confirmations"] = self.bc.height - blk.height + 1
                    return d
        return None

    def address_info(self, address: str) -> dict:
        balance = self.bc.utxo.balance(address)
        utxos   = self.bc.utxo.get_by_address(address)
        return {
            "address":     address,
            "balance_nbl": f"{balance/10**DECIMALS:.{DECIMALS}f}",
            "balance_neb": balance,
            "utxo_count":  len(utxos),
            "utxos": [{
                "txid":   u.txid,
                "index":  u.index,
                "value_nbl": f"{u.value/10**DECIMALS:.{DECIMALS}f}",
                "height": u.height,
            } for u in utxos],
        }

    def recent_blocks(self, count: int = 10) -> List[dict]:
        start = max(0, self.bc.height - count + 1)
        result = []
        for h in range(self.bc.height, start - 1, -1):
            blk = self.bc.get_block(h)
            if blk:
                result.append({
                    "height":    blk.height,
                    "hash":      blk.hash[:16] + "...",
                    "txs":       blk.tx_count,
                    "size":      blk.byte_size(),
                    "timestamp": blk.header.timestamp,
                    "miner":     blk.transactions[0].outputs[0].address if blk.transactions else "?",
                })
        return result

    def supply_info(self) -> dict:
        from nebula_core import MAX_SUPPLY
        issued = self.bc.utxo.total_supply()
        era    = halving_era(self.bc.height)
        return {
            "max_supply":      f"{MAX_SUPPLY/10**DECIMALS:,.0f} NBL",
            "issued":          f"{issued/10**DECIMALS:.{DECIMALS}f} NBL",
            "percentage":      f"{issued/MAX_SUPPLY*100:.4f}%",
            "current_reward":  era["reward_nbl"] + " NBL",
            "era":             era["era_name"],
            "next_halving":    era["next_halving_at"],
            "blocks_remaining":era["blocks_remaining"],
        }

    def print_dashboard(self):
        info  = self.bc.chain_info()
        sup   = self.supply_info()
        recnt = self.recent_blocks(5)

        print("\n" + "═"*60)
        print(f"  NEBULA Blockchain Dashboard")
        print("═"*60)
        print(f"  Height        : {info['height']:,}")
        print(f"  Best Block    : {info['best_hash'][:32]}...")
        print(f"  Difficulty    : {info['bits']}")
        print(f"  Block Reward  : {info['reward_nbl']} NBL")
        print(f"  Era           : {info['era']}")
        print(f"  Next Halving  : block #{info['next_halving']:,}")
        print(f"  Supply Issued : {sup['issued']}")
        print(f"  Max Supply    : {sup['max_supply']}")
        print(f"  UTXO Set      : {info['utxo_set_size']:,} entries")
        print(f"  Mempool       : {info['mempool_txs']} txs")
        print("\n  Recent Blocks:")
        for b in recnt:
            print(f"    #{b['height']:>6} | {b['hash']} | {b['txs']} txs | {b['size']} bytes")
        print("═"*60)

# ================================================================
#  NEBULA FULL NODE
# ================================================================

class NEBULAFullNode:
    """
    Complete NEBULA full node.
    Runs blockchain + P2P + optional miner + wallet.
    """

    def __init__(self,
                 data_dir:      str  = "./nebula_data",
                 port:          int  = DEFAULT_PORT,
                 mine:          bool = False,
                 miner_address: str  = None,
                 threads:       int  = None):

        self.data_dir = Path(data_dir)
        self.data_dir.mkdir(exist_ok=True)

        print(BANNER)

        # Core blockchain
        self.bc       = NEBULABlockchain()
        self.explorer = BlockExplorer(self.bc)

        # P2P network
        self.p2p = P2PNode(self.bc, port=port)
        self.p2p.on_new_block = self._on_new_block
        self.p2p.on_new_tx    = self._on_new_tx

        # Miner
        self.miner = None
        if mine:
            addr = miner_address or self._load_or_create_miner_address()
            self.miner = NEBULAMiner(self.bc, addr, threads=threads)

        # Wallet
        self.wallet = None

        self._running = False

    def _load_or_create_miner_address(self) -> str:
        wallet_file = self.data_dir / "miner_wallet.json"
        if wallet_file.exists():
            data = json.loads(wallet_file.read_text())
            return data["address"]
        # Create new wallet
        w = NEBULAWallet.create_new()
        wallet_file.write_text(json.dumps({
            "address":  w.first_address,
            "mnemonic": w.mnemonic,   # ⚠️ Keep safe!
        }, indent=2))
        print(f"⚠️  Miner wallet saved to {wallet_file}")
        print(f"    BACK UP YOUR MNEMONIC!")
        return w.first_address

    def start(self):
        """Start all node services"""
        self._running = True
        self.p2p.start()

        if self.miner:
            self.miner.start()

        # Status thread
        threading.Thread(target=self._status_loop, daemon=True, name="Status").start()

        # Save chain periodically
        threading.Thread(target=self._save_loop, daemon=True, name="SaveChain").start()

        self.explorer.print_dashboard()
        print(f"\n✅ NEBULA Full Node running")
        print(f"   Data dir : {self.data_dir}")
        print(f"   Port     : {self.p2p.port}")
        print(f"   Mining   : {'yes' if self.miner else 'no'}")
        print(f"\n   Press Ctrl+C to stop\n")

    def stop(self):
        self._running = False
        if self.miner:
            self.miner.stop()
        self.p2p.stop()
        self.save_chain()
        print("\n🛑 NEBULA node stopped. Chain saved.")

    def _on_new_block(self, block):
        print(f"📦 New block #{block.height}: {block.hash[:16]}...")

    def _on_new_tx(self, tx):
        print(f"📨 New tx: {tx.txid[:16]}...")

    def _status_loop(self):
        while self._running:
            time.sleep(60)
            self.explorer.print_dashboard()
            if self.miner:
                s = self.miner.get_stats()
                print(f"  ⛏️  Mining: {s['hash_rate']} | {s['blocks_found']} found")

    def _save_loop(self):
        while self._running:
            time.sleep(300)   # every 5 min
            self.save_chain()

    def save_chain(self):
        path = self.data_dir / "nebula_chain.json"
        self.bc.export(str(path))

    def interactive_wallet(self):
        """Simple CLI wallet interface"""
        print("\n" + "─"*50)
        print("  NEBULA Wallet")
        print("─"*50)
        print("  1. Create new wallet")
        print("  2. Restore from mnemonic")
        print("  3. Check balance")
        print("  4. Send NBL")
        print("  5. Show address")
        print("─"*50)

        choice = input("  Choice: ").strip()

        if choice == "1":
            self.wallet = NEBULAWallet.create_new(self.bc.utxo)
            print(f"\n  ✅ Wallet created!")
            print(f"  Address : {self.wallet.first_address}")
            print(f"\n  ⚠️  WRITE DOWN YOUR 12-WORD MNEMONIC:")
            print(f"  {self.wallet.mnemonic}")

        elif choice == "2":
            mnemonic = input("  Enter 12-word mnemonic: ").strip()
            self.wallet = NEBULAWallet.from_mnemonic(mnemonic, utxo_set=self.bc.utxo)
            print(f"  Restored: {self.wallet.first_address}")

        elif choice == "3":
            if not self.wallet:
                addr = input("  Enter address: ").strip()
                info = self.explorer.address_info(addr)
            else:
                info = self.explorer.address_info(self.wallet.first_address)
            print(f"\n  Balance: {info['balance_nbl']}")
            print(f"  UTXOs  : {info['utxo_count']}")

        elif choice == "4":
            if not self.wallet:
                print("  ❌ No wallet loaded")
                return
            to_addr  = input("  To address: ").strip()
            amount   = float(input("  Amount (NBL): ").strip())
            tx = self.wallet.build_transaction(to_addr, amount)
            if tx:
                ok, msg = self.bc.mempool.submit(tx)
                print(f"  {'✅' if ok else '❌'} {msg}: {tx.txid[:20]}...")

        elif choice == "5":
            if self.wallet:
                print(f"  Address: {self.wallet.first_address}")
            else:
                print("  No wallet loaded")

    def run_interactive(self):
        """Interactive CLI"""
        self.start()
        try:
            while True:
                cmd = input("\nNBL> ").strip().lower()
                if cmd in ("exit", "quit", "q"):
                    break
                elif cmd == "info":
                    self.explorer.print_dashboard()
                elif cmd == "wallet":
                    self.interactive_wallet()
                elif cmd.startswith("block "):
                    h = cmd[6:].strip()
                    info = self.explorer.block_info(h)
                    print(json.dumps(info, indent=2) if info else "Not found")
                elif cmd.startswith("tx "):
                    txid = cmd[3:].strip()
                    info = self.explorer.tx_info(txid)
                    print(json.dumps(info, indent=2) if info else "Not found")
                elif cmd.startswith("addr "):
                    addr = cmd[5:].strip()
                    info = self.explorer.address_info(addr)
                    print(json.dumps(info, indent=2))
                elif cmd == "peers":
                    peers = self.p2p.all_peers()
                    print(json.dumps(peers, indent=2))
                elif cmd == "supply":
                    print(json.dumps(self.explorer.supply_info(), indent=2))
                elif cmd == "miner":
                    if self.miner:
                        print(json.dumps(self.miner.get_stats(), indent=2))
                    else:
                        print("Mining not enabled. Restart with --mine")
                elif cmd == "help":
                    print("  Commands: info, wallet, block <h|hash>, tx <txid>,")
                    print("            addr <address>, peers, supply, miner, help, quit")
                else:
                    print(f"  Unknown command: {cmd}. Type 'help'")
        except KeyboardInterrupt:
            pass
        finally:
            self.stop()


# ================================================================
#  DEMO — Quick Demonstration
# ================================================================

def run_demo():
    """Quick demo — creates node, mines 3 blocks, shows info"""
    print(BANNER)

    bc       = NEBULABlockchain()
    explorer = BlockExplorer(bc)

    # Create demo wallet
    wallet = NEBULAWallet.create_new(bc.utxo)
    print(f"\n📬 Demo miner address: {wallet.first_address}")

    # Mine 3 blocks with easy difficulty
    miner = NEBULAMiner(bc, wallet.first_address, threads=1)
    for i in range(3):
        block = miner.mine_demo_block(easy_bits=0x1f0fffff)
        if block:
            ok, msg = bc.add_block(block)
            print(f"   Block #{block.height}: {msg}")

    # Show dashboard
    explorer.print_dashboard()

    # Show supply
    print("\n📊 Supply Info:")
    for k, v in explorer.supply_info().items():
        print(f"   {k:20}: {v}")

    # Save
    bc.export("nebula_demo_chain.json")
    print(f"\n✅ Demo complete! Chain saved to nebula_demo_chain.json")


# ================================================================
#  MAIN
# ================================================================

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="NEBULA Blockchain Node")
    parser.add_argument("--mine",    action="store_true", help="Enable mining")
    parser.add_argument("--demo",    action="store_true", help="Run quick demo")
    parser.add_argument("--wallet",  action="store_true", help="Wallet mode only")
    parser.add_argument("--info",    action="store_true", help="Show chain info and exit")
    parser.add_argument("--port",    type=int, default=DEFAULT_PORT)
    parser.add_argument("--threads", type=int, default=None)
    parser.add_argument("--address", type=str, default=None, help="Miner address")
    parser.add_argument("--datadir", type=str, default="./nebula_data")
    args = parser.parse_args()

    if args.demo:
        run_demo()
    elif args.info:
        bc = NEBULABlockchain()
        for k, v in bc.chain_info().items():
            print(f"  {k:20}: {v}")
    elif args.wallet:
        bc     = NEBULABlockchain()
        node   = NEBULAFullNode(data_dir=args.datadir, port=args.port)
        node.interactive_wallet()
    else:
        node = NEBULAFullNode(
            data_dir      = args.datadir,
            port          = args.port,
            mine          = args.mine,
            miner_address = args.address,
            threads       = args.threads,
        )
        node.run_interactive()
