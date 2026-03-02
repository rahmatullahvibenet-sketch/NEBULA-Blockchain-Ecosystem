"""
================================================================
  NEBULA CLI — nebula_cli.py
  Complete Command Line Interface
  
  Commands:
    node      — Start full node
    mine      — Start mining
    wallet    — Wallet operations
    send      — Send NBL
    balance   — Check balance
    block     — Block info
    tx        — Transaction info
    addr      — Address info
    peers     — Peer list
    mempool   — Mempool info
    supply    — Supply info
    halving   — Halving info
    test      — Run tests
    version   — Version info
================================================================
"""

import sys, os, json, time, argparse, threading, getpass
sys.path.insert(0, os.path.dirname(__file__))

from pathlib import Path
from nebula_core import (
    NEBULABlockchain, CHAIN_NAME, CHAIN_SYMBOL, CHAIN_ID,
    DECIMALS, MAX_SUPPLY, halving_era, mining_reward,
    INITIAL_BLOCK_REWARD, HALVING_INTERVAL, TARGET_BLOCK_TIME,
    DEFAULT_PORT
)
from nebula_wallet   import NEBULAWallet, BIP39
from nebula_miner    import NEBULAMiner
from nebula_network  import P2PNode
from nebula_security import SecurityManager

# ================================================================
#  COLORS
# ================================================================

class C:
    RESET  = '\033[0m'
    BOLD   = '\033[1m'
    RED    = '\033[91m'
    GREEN  = '\033[92m'
    YELLOW = '\033[93m'
    BLUE   = '\033[94m'
    PURPLE = '\033[95m'
    CYAN   = '\033[96m'
    WHITE  = '\033[97m'
    GOLD   = '\033[33m'

def c(text, color): return f"{color}{text}{C.RESET}"
def ok(msg):    print(c(f"✅ {msg}", C.GREEN))
def err(msg):   print(c(f"❌ {msg}", C.RED))
def info(msg):  print(c(f"ℹ️  {msg}", C.CYAN))
def warn(msg):  print(c(f"⚠️  {msg}", C.YELLOW))
def bold(msg):  print(c(msg, C.BOLD))

# ================================================================
#  BANNER
# ================================================================

BANNER = f"""
{C.GOLD}╔══════════════════════════════════════════════════════════╗
║                                                          ║
║   🌌  N E B U L A  (NBL)  v1.0.0                        ║
║                                                          ║
║   Chain ID : {CHAIN_ID}                                      ║
║   Supply   : 10,700,000 NBL (fixed forever)             ║
║   Block    : 600 seconds target (10 min)                          ║
║   Halving  : Every 210,000 blocks                       ║
║   Access   : Open to All Humanity Worldwide 🌍       ║
║                                                          ║
║   No Government · No Bank · No Permission               ║
║   Created by  : Zayn Quantum                            ║
╚══════════════════════════════════════════════════════════╝{C.RESET}
"""

# ================================================================
#  NODE RUNNER
# ================================================================

class NodeRunner:
    """Manages node lifecycle"""

    def __init__(self, data_dir: str = "./nebula_data", port: int = DEFAULT_PORT):
        self.data_dir = Path(data_dir)
        self.data_dir.mkdir(exist_ok=True)
        self.bc       = None
        self.p2p      = None
        self.miner    = None
        self.security = None
        self.wallet   = None
        self.port     = port
        self._running = False

    def init(self):
        self.bc       = NEBULABlockchain()
        self.p2p      = P2PNode(self.bc, port=self.port)
        self.security = SecurityManager(CHAIN_ID)
        self._load_wallet()

    def _load_wallet(self):
        wf = self.data_dir / "wallet.json"
        if wf.exists():
            try:
                d = json.loads(wf.read_text())
                self.wallet = NEBULAWallet.from_mnemonic(d["mnemonic"], utxo_set=self.bc.utxo)
                info(f"Wallet loaded: {self.wallet.first_address}")
            except Exception as e:
                warn(f"Could not load wallet: {e}")

    def save_wallet(self):
        if self.wallet:
            wf = self.data_dir / "wallet.json"
            wf.write_text(json.dumps({
                "address":  self.wallet.first_address,
                "mnemonic": self.wallet.mnemonic,
            }, indent=2))

    def start_p2p(self):
        self.p2p.start()
        ok(f"P2P listening on port {self.port}")

    def start_mining(self, address: str = None, threads: int = None):
        addr = address or (self.wallet.first_address if self.wallet else None)
        if not addr:
            err("No miner address. Create wallet first.")
            return
        self.miner = NEBULAMiner(self.bc, addr, threads=threads)
        self.miner.start()
        ok(f"Mining started → {addr[:20]}...")

    def stop(self):
        self._running = False
        if self.miner:  self.miner.stop()
        if self.p2p:    self.p2p.stop()
        self.save_wallet()
        self.bc.export(str(self.data_dir / "chain.json"))

    def run_forever(self):
        self._running = True
        try:
            while self._running:
                time.sleep(30)
                self._print_status()
        except KeyboardInterrupt:
            pass
        finally:
            self.stop()

    def _print_status(self):
        info_d = self.bc.chain_info()
        print(f"\r{C.CYAN}Height:{C.RESET} {info_d['height']} | "
              f"{C.CYAN}Peers:{C.RESET} {self.p2p.peer_count()} | "
              f"{C.CYAN}Mempool:{C.RESET} {info_d['mempool_txs']} | "
              f"{C.CYAN}Supply:{C.RESET} {info_d['issued_supply']}",
              end='', flush=True)


# ================================================================
#  CLI COMMANDS
# ================================================================

def cmd_version(args, node: NodeRunner):
    print(BANNER)
    print(f"  Chain:    {CHAIN_NAME} ({CHAIN_SYMBOL})")
    print(f"  Chain ID: {CHAIN_ID}")
    print(f"  Version:  1.0.0")
    print(f"  Protocol: 70015")
    print(f"  Python:   {sys.version.split()[0]}")

def cmd_node(args, node: NodeRunner):
    print(BANNER)
    node.init()
    node.start_p2p()
    if args.mine:
        node.start_mining(args.address, args.threads)
    ok("Node started. Press Ctrl+C to stop.")
    node.run_forever()

def cmd_mine(args, node: NodeRunner):
    node.init()
    node.start_p2p()
    node.start_mining(args.address, args.threads)
    ok(f"Mining with {args.threads or 'auto'} threads")
    node.run_forever()

def cmd_wallet_new(args, node: NodeRunner):
    print(BANNER)
    node.init()
    node.wallet = NEBULAWallet.create_new(node.bc.utxo)
    node.save_wallet()
    print()
    bold("  ╔══════════════════════════════════════════╗")
    bold("  ║   NEW WALLET CREATED — SAVE THIS INFO   ║")
    bold("  ╚══════════════════════════════════════════╝")
    print()
    print(f"  {C.GOLD}Address :{C.RESET} {node.wallet.first_address}")
    print()
    print(f"  {C.RED}⚠️  12-WORD MNEMONIC (NEVER SHARE!):{C.RESET}")
    print(f"  {C.YELLOW}{node.wallet.mnemonic}{C.RESET}")
    print()
    warn("  Write these 12 words on paper. Keep offline. Never share!")
    warn(f"  Saved to {node.data_dir}/wallet.json")

def cmd_wallet_restore(args, node: NodeRunner):
    node.init()
    if args.mnemonic:
        mnemonic = args.mnemonic
    else:
        print("Enter your 12-word mnemonic phrase:")
        mnemonic = input("> ").strip()
    node.wallet = NEBULAWallet.from_mnemonic(mnemonic, utxo_set=node.bc.utxo)
    node.save_wallet()
    ok(f"Wallet restored: {node.wallet.first_address}")

def cmd_balance(args, node: NodeRunner):
    node.init()
    address = args.address
    if not address and node.wallet:
        address = node.wallet.first_address
    if not address:
        err("No address. Use --address or create wallet first.")
        return
    bal_neb = node.bc.utxo.balance(address)
    bal_nbl = bal_neb / 10**DECIMALS
    utxos   = node.bc.utxo.get_by_address(address)
    print()
    print(f"  {C.GOLD}Address:{C.RESET}     {address}")
    print(f"  {C.GREEN}Balance:{C.RESET}     {bal_nbl:.{DECIMALS}f} {CHAIN_SYMBOL}")
    print(f"  {C.CYAN}In Neb  :{C.RESET}    {bal_neb:,} Neb")
    print(f"  {C.CYAN}UTXOs   :{C.RESET}    {len(utxos)}")
    if utxos:
        print(f"\n  Unspent outputs:")
        for u in utxos[:10]:
            print(f"    {u.txid[:16]}... [{u.index}] = {u.value/10**DECIMALS:.9f} NBL (height {u.height})")

def cmd_send(args, node: NodeRunner):
    node.init()
    if not node.wallet:
        err("No wallet loaded. Use 'wallet new' or 'wallet restore'.")
        return
    to_addr = args.to
    amount  = float(args.amount)
    fee     = float(getattr(args, 'fee', 0.0001))
    print(f"\n  Sending {amount} NBL → {to_addr[:20]}...")
    print(f"  Fee: {fee} NBL")
    tx = node.wallet.build_transaction(to_addr, amount, fee)
    if tx:
        ok_r, msg = node.bc.mempool.submit(tx)
        if ok_r:
            ok(f"Transaction submitted: {tx.txid}")
            if node.p2p:
                node.p2p.broadcast_tx(tx)
        else:
            err(f"Mempool rejected: {msg}")
    else:
        err("Could not build transaction")

def cmd_block(args, node: NodeRunner):
    node.init()
    h_or_hash = args.id
    try:
        blk = node.bc.get_block(int(h_or_hash))
    except ValueError:
        blk = node.bc.get_block_by_hash(h_or_hash)
    if not blk:
        err(f"Block not found: {h_or_hash}")
        return
    d = blk.to_dict()
    print()
    print(f"  {C.GOLD}Block #{d['height']}{C.RESET}")
    print(f"  Hash        : {d['hash']}")
    print(f"  Prev        : {d['header']['prev_hash']}")
    print(f"  Merkle root : {d['header']['merkle_root']}")
    print(f"  Time        : {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(d['header']['timestamp']))}")
    print(f"  Difficulty  : {d['header']['bits']}")
    print(f"  Nonce       : {d['header']['nonce']:,}")
    print(f"  Txs         : {d['tx_count']}")
    print(f"  Size        : {d['size']:,} bytes")
    if args.json:
        print(json.dumps(d, indent=2))

def cmd_tx(args, node: NodeRunner):
    node.init()
    txid = args.txid
    for blk in reversed(node.bc._chain):
        for tx in blk.transactions:
            if tx.txid == txid or tx.txid.startswith(txid):
                d = tx.to_dict()
                print()
                print(f"  {C.GOLD}Transaction{C.RESET}")
                print(f"  TXID        : {d['txid']}")
                print(f"  Block       : #{blk.height}")
                print(f"  Confirmations: {node.bc.height - blk.height + 1}")
                print(f"  Size        : {d['size']} bytes")
                print(f"  Coinbase    : {d['coinbase']}")
                print(f"  Outputs     :")
                for o in d['vout']:
                    print(f"    [{o['n']}] {o['value_nbl']} NBL → {o.get('address','?')}")
                if args.json:
                    print(json.dumps(d, indent=2))
                return
    # Check mempool
    if txid in node.bc.mempool._txs:
        tx = node.bc.mempool._txs[txid]
        ok(f"TX in mempool (unconfirmed): {txid}")
        return
    err(f"Transaction not found: {txid}")

def cmd_addr(args, node: NodeRunner):
    cmd_balance(args, node)

def cmd_peers(args, node: NodeRunner):
    node.init()
    node.start_p2p()
    time.sleep(2)
    peers = node.p2p.all_peers()
    if not peers:
        info("No peers connected yet")
        info(f"Connecting to seed nodes...")
        return
    print(f"\n  {C.CYAN}Connected Peers ({len(peers)}){C.RESET}")
    for p in peers:
        print(f"  {p['addr']:25} | height: {p['height']:>6} | "
              f"latency: {p['latency_ms']}ms | {'inbound' if p['inbound'] else 'outbound'}")

def cmd_mempool(args, node: NodeRunner):
    node.init()
    mp = node.bc.mempool
    fees = mp.total_fees()
    print()
    print(f"  {C.CYAN}Mempool Status{C.RESET}")
    print(f"  Transactions : {mp.size()}")
    print(f"  Total fees   : {fees/10**DECIMALS:.9f} NBL")
    if args.verbose:
        txs = mp.get_for_block()
        for tx in txs[:20]:
            fee = tx.fee(node.bc.utxo)
            print(f"  {tx.txid[:16]}... | {tx.byte_size()}B | fee: {fee/10**DECIMALS:.9f}")

def cmd_supply(args, node: NodeRunner):
    node.init()
    issued   = node.bc.utxo.total_supply()
    pct      = issued / MAX_SUPPLY * 100
    era_info = halving_era(node.bc.height)
    remaining = MAX_SUPPLY - issued
    print()
    print(f"  {C.GOLD}NEBULA Supply Info{C.RESET}")
    print(f"  Max supply     : {MAX_SUPPLY/10**DECIMALS:>20,.{DECIMALS}f} NBL")
    print(f"  Issued so far  : {issued/10**DECIMALS:>20,.{DECIMALS}f} NBL")
    print(f"  Remaining      : {remaining/10**DECIMALS:>20,.{DECIMALS}f} NBL")
    print(f"  % issued       : {pct:>20.6f}%")
    print()
    print(f"  {C.CYAN}Halving Schedule{C.RESET}")
    print(f"  Current era    : {era_info['era_name']}")
    print(f"  Block reward   : {era_info['reward_nbl']} NBL")
    print(f"  Next halving   : block #{era_info['next_halving_at']:,}")
    print(f"  Blocks left    : {era_info['blocks_remaining']:,}")
    print(f"  Era progress   : {era_info['pct_complete']}")
    print()
    print(f"  {C.CYAN}Future Halvings{C.RESET}")
    print(f"  {'Era':<5} {'Block':<12} {'Reward':<20} {'Approx Year'}")
    print(f"  {'─'*55}")
    for era_n in range(8):
        blk    = era_n * HALVING_INTERVAL
        rew    = mining_reward(blk)
        year   = 2025 + era_n * 4
        arrow  = " ◄ NOW" if era_n == era_info['era'] else ""
        print(f"  {era_n:<5} {blk:<12,} {rew/10**DECIMALS:<20.9f} {year}{arrow}")

def cmd_halving(args, node: NodeRunner):
    node.init()
    cmd_supply(args, node)

def cmd_info(args, node: NodeRunner):
    node.init()
    d = node.bc.chain_info()
    print(BANNER)
    print(f"  {C.CYAN}Chain Info{C.RESET}")
    for k, v in d.items():
        print(f"  {k:20}: {v}")

def cmd_test(args, node: NodeRunner):
    from nebula_tests import run_all_tests
    result = run_all_tests()
    if result.failed == 0:
        ok(f"All {result.passed} tests passed!")
    else:
        err(f"{result.failed} tests failed")

def cmd_security(args, node: NodeRunner):
    node.init()
    node.security = SecurityManager(CHAIN_ID)
    status = node.security.status()
    print(f"\n  {C.CYAN}Security Status{C.RESET}")
    for k, v in status.items():
        print(f"  {k:25}: {v}")

def cmd_demo(args, node: NodeRunner):
    """Quick demo — mines blocks and shows everything"""
    print(BANNER)
    node.init()
    ok("Blockchain initialized")
    info(f"Genesis: {node.bc.tip.hash}")

    # Create wallet
    node.wallet = NEBULAWallet.create_new(node.bc.utxo)
    ok(f"Wallet: {node.wallet.first_address}")

    # Mine 5 blocks
    miner = NEBULAMiner(node.bc, node.wallet.first_address, threads=1)
    print(f"\n⛏️  Mining 5 demo blocks...")
    for i in range(5):
        blk = miner.mine_demo_block(0x1f0fffff)
        if blk:
            r, msg = node.bc.add_block(blk)
            print(f"  Block #{blk.height}: {blk.hash[:20]}... [{msg}]")

    # Show info
    print()
    cmd_info(args, node)
    cmd_supply(args, node)
    bal = node.bc.utxo.balance(node.wallet.first_address)
    ok(f"Miner balance: {bal/10**DECIMALS:.9f} NBL")

    # Save
    node.bc.export(str(node.data_dir / "demo_chain.json"))
    ok(f"Chain saved to {node.data_dir}/demo_chain.json")


# ================================================================
#  INTERACTIVE REPL
# ================================================================

def run_repl(node: NodeRunner):
    """Interactive REPL for advanced users"""
    node.init()
    node.start_p2p()
    print(BANNER)
    ok("Interactive mode. Type 'help' for commands.")

    COMMANDS = {
        "help":    "Show this help",
        "info":    "Chain info",
        "balance [address]": "Check balance",
        "block <height|hash>": "Block details",
        "tx <txid>":    "Transaction details",
        "peers":        "Connected peers",
        "mempool":      "Mempool status",
        "supply":       "Supply + halving info",
        "wallet new":   "Create new wallet",
        "wallet show":  "Show wallet info",
        "mine start":   "Start mining",
        "mine stop":    "Stop mining",
        "mine status":  "Mining stats",
        "test":         "Run tests",
        "security":     "Security status",
        "save":         "Save chain to disk",
        "exit":         "Exit",
    }

    while True:
        try:
            raw = input(f"\n{C.GOLD}NBL>{C.RESET} ").strip()
            if not raw:
                continue
            parts = raw.split()
            cmd   = parts[0].lower()
            rest  = parts[1:]

            if cmd in ("exit", "quit", "q"):
                break

            elif cmd == "help":
                print(f"\n  {C.CYAN}Available commands:{C.RESET}")
                for c_name, c_desc in COMMANDS.items():
                    print(f"  {c_name:<35} {c_desc}")

            elif cmd == "info":
                d = node.bc.chain_info()
                for k, v in d.items():
                    print(f"  {k:20}: {v}")

            elif cmd == "balance":
                addr = rest[0] if rest else (node.wallet.first_address if node.wallet else None)
                if not addr:
                    err("No address")
                else:
                    bal = node.bc.utxo.balance(addr)
                    print(f"  {addr}")
                    print(f"  Balance: {C.GREEN}{bal/10**DECIMALS:.{DECIMALS}f} NBL{C.RESET}")

            elif cmd == "block":
                if not rest:
                    err("Usage: block <height|hash>")
                else:
                    try:
                        blk = node.bc.get_block(int(rest[0]))
                    except ValueError:
                        blk = node.bc.get_block_by_hash(rest[0])
                    if blk:
                        d = blk.to_dict()
                        print(f"  #{d['height']} | {d['hash'][:32]}... | {d['tx_count']} txs | {d['size']} bytes")
                    else:
                        err("Block not found")

            elif cmd == "tx":
                if not rest:
                    err("Usage: tx <txid>")
                else:
                    txid = rest[0]
                    found = False
                    for blk in reversed(node.bc._chain):
                        for tx in blk.transactions:
                            if tx.txid.startswith(txid):
                                d = tx.to_dict()
                                print(f"  {d['txid']}")
                                print(f"  Block #{blk.height} | {d['size']} bytes | coinbase={d['coinbase']}")
                                for o in d['vout']:
                                    print(f"    [{o['n']}] {o['value_nbl']} → {o.get('address','?')}")
                                found = True
                                break
                        if found: break
                    if not found:
                        err("TX not found")

            elif cmd == "peers":
                peers = node.p2p.all_peers()
                if peers:
                    for p in peers:
                        print(f"  {p['addr']} | {p['state']} | height {p['height']}")
                else:
                    info("No peers connected")

            elif cmd == "mempool":
                mp = node.bc.mempool
                print(f"  {mp.size()} txs | {mp.total_fees()/10**DECIMALS:.9f} NBL fees")

            elif cmd == "supply":
                era = halving_era(node.bc.height)
                issued = node.bc.utxo.total_supply()
                print(f"  Issued : {issued/10**DECIMALS:.9f} NBL")
                print(f"  Era    : {era['era_name']}")
                print(f"  Reward : {era['reward_nbl']} NBL")
                print(f"  Halving in {era['blocks_remaining']:,} blocks")

            elif cmd == "wallet":
                sub = rest[0] if rest else ""
                if sub == "new":
                    node.wallet = NEBULAWallet.create_new(node.bc.utxo)
                    node.save_wallet()
                    print(f"  {C.GOLD}Address:{C.RESET} {node.wallet.first_address}")
                    print(f"  {C.RED}Mnemonic: {node.wallet.mnemonic}{C.RESET}")
                elif sub == "show" and node.wallet:
                    d = node.wallet.info()
                    for k, v in d.items():
                        print(f"  {k:20}: {v}")
                else:
                    err("Usage: wallet new | wallet show")

            elif cmd == "mine":
                sub = rest[0] if rest else ""
                if sub == "start":
                    if not node.wallet:
                        err("Create wallet first")
                    elif node.miner and node.miner._running:
                        warn("Already mining")
                    else:
                        node.start_mining()
                elif sub == "stop":
                    if node.miner:
                        node.miner.stop()
                        node.miner = None
                        ok("Mining stopped")
                elif sub == "status":
                    if node.miner:
                        s = node.miner.get_stats()
                        for k, v in s.items():
                            print(f"  {k:20}: {v}")
                    else:
                        info("Not mining")

            elif cmd == "test":
                from nebula_tests import run_all_tests
                run_all_tests()

            elif cmd == "security":
                if node.security:
                    for k, v in node.security.status().items():
                        print(f"  {k:25}: {v}")

            elif cmd == "save":
                node.bc.export(str(node.data_dir / "chain.json"))
                ok("Chain saved")

            else:
                err(f"Unknown command: {cmd}. Type 'help'")

        except KeyboardInterrupt:
            print()
            break
        except EOFError:
            break
        except Exception as e:
            err(f"Error: {e}")

    node.stop()
    ok("Goodbye!")


# ================================================================
#  ARGUMENT PARSER
# ================================================================

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog        = "nebula",
        description = "NEBULA (NBL) Blockchain Node",
        formatter_class = argparse.RawDescriptionHelpFormatter,
        epilog = """
Examples:
  python3 nebula_cli.py demo                    Run quick demo
  python3 nebula_cli.py node                    Start full node
  python3 nebula_cli.py node --mine             Start node + mining
  python3 nebula_cli.py mine --threads 4        Mine with 4 cores
  python3 nebula_cli.py wallet new              Create new wallet
  python3 nebula_cli.py balance                 Check balance
  python3 nebula_cli.py send --to ADDR --amount 1.5
  python3 nebula_cli.py block 0                 Show genesis block
  python3 nebula_cli.py supply                  Supply + halving info
  python3 nebula_cli.py test                    Run all tests
  python3 nebula_cli.py repl                    Interactive mode
"""
    )
    p.add_argument("--datadir",  default="./nebula_data", help="Data directory")
    p.add_argument("--port",     type=int, default=DEFAULT_PORT)
    p.add_argument("--testnet",  action="store_true")

    sub = p.add_subparsers(dest="command")

    # node
    n = sub.add_parser("node", help="Start full node")
    n.add_argument("--mine",    action="store_true")
    n.add_argument("--address", help="Miner address")
    n.add_argument("--threads", type=int)

    # mine
    m = sub.add_parser("mine", help="Start miner")
    m.add_argument("--address", help="Miner address")
    m.add_argument("--threads", type=int)

    # wallet
    w = sub.add_parser("wallet", help="Wallet commands")
    ws = w.add_subparsers(dest="wallet_cmd")
    ws.add_parser("new",     help="Create new wallet")
    wr = ws.add_parser("restore", help="Restore from mnemonic")
    wr.add_argument("--mnemonic", help="12-word mnemonic phrase")

    # balance
    b = sub.add_parser("balance", help="Check balance")
    b.add_argument("--address", help="NBL address")

    # send
    s = sub.add_parser("send", help="Send NBL")
    s.add_argument("--to",     required=True, help="Recipient address")
    s.add_argument("--amount", required=True, help="Amount in NBL")
    s.add_argument("--fee",    default="0.0001", help="Fee in NBL")

    # block
    bl = sub.add_parser("block", help="Block info")
    bl.add_argument("id", help="Block height or hash")
    bl.add_argument("--json", action="store_true")

    # tx
    tx = sub.add_parser("tx", help="Transaction info")
    tx.add_argument("txid", help="Transaction ID (can be prefix)")
    tx.add_argument("--json", action="store_true")

    # addr
    ad = sub.add_parser("addr", help="Address info")
    ad.add_argument("--address", required=True)

    # peers
    sub.add_parser("peers", help="List peers")

    # mempool
    mp = sub.add_parser("mempool", help="Mempool info")
    mp.add_argument("--verbose", "-v", action="store_true")

    # supply
    sub.add_parser("supply",  help="Supply + halving info")
    sub.add_parser("halving", help="Halving schedule")
    sub.add_parser("info",    help="Chain info")
    sub.add_parser("version", help="Version info")
    sub.add_parser("test",    help="Run test suite")
    sub.add_parser("security",help="Security status")
    sub.add_parser("demo",    help="Quick demo")

    # repl
    sub.add_parser("repl", help="Interactive REPL")

    return p


# ================================================================
#  MAIN
# ================================================================

COMMAND_MAP = {
    "node":     cmd_node,
    "mine":     cmd_mine,
    "balance":  cmd_balance,
    "send":     cmd_send,
    "block":    cmd_block,
    "tx":       cmd_tx,
    "addr":     cmd_addr,
    "peers":    cmd_peers,
    "mempool":  cmd_mempool,
    "supply":   cmd_supply,
    "halving":  cmd_halving,
    "info":     cmd_info,
    "version":  cmd_version,
    "test":     cmd_test,
    "security": cmd_security,
    "demo":     cmd_demo,
}

if __name__ == "__main__":
    parser = build_parser()
    args   = parser.parse_args()

    node = NodeRunner(
        data_dir = args.datadir,
        port     = args.port,
    )

    if args.command == "wallet":
        if args.wallet_cmd == "new":
            node.init()
            cmd_wallet_new(args, node)
        elif args.wallet_cmd == "restore":
            node.init()
            cmd_wallet_restore(args, node)
        else:
            parser.print_help()

    elif args.command == "repl":
        run_repl(node)

    elif args.command in COMMAND_MAP:
        COMMAND_MAP[args.command](args, node)

    else:
        print(BANNER)
        parser.print_help()
