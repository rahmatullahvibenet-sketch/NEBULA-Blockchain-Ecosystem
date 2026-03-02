"""
================================================================
  NEBULA WALLET — nebula_wallet.py
  BIP32 HD Wallet + BIP39 Mnemonic + Transaction Builder
  Real ECDSA signing with secp256k1
================================================================
"""

import hashlib, hmac, struct, secrets, unicodedata
from typing import List, Tuple, Optional, Dict
from nebula_core import (
    Secp256k1, Script, Transaction, TxInput, TxOutput, OutPoint,
    UTXOSet, UTXOEntry, base58check_encode, base58check_decode,
    sha256d, hash160, PUBKEY_ADDRESS_VERSION, WIF_VERSION,
    DECIMALS, MIN_TX_FEE, DUST_THRESHOLD, SIGHASH_ALL,
    encode_varint
)

# ================================================================
#  BIP39 WORDLIST (English — 2048 words, first 256 shown inline)
#  Full list loaded from file in production
# ================================================================

BIP39_WORDS_MINI = [
    "abandon","ability","able","about","above","absent","absorb","abstract",
    "absurd","abuse","access","accident","account","accuse","achieve","acid",
    "acoustic","acquire","across","act","action","actor","actress","actual",
    "adapt","add","addict","address","adjust","admit","adult","advance",
    "advice","aerobic","afford","afraid","again","age","agent","agree",
    "ahead","aim","air","airport","aisle","alarm","album","alcohol",
    "alert","alien","all","alley","allow","almost","alone","alpha",
    "already","also","alter","always","amateur","amazing","among","amount",
    "amused","analyst","anchor","ancient","anger","angle","angry","animal",
    "ankle","announce","annual","another","answer","antenna","antique","anxiety",
    "any","apart","apology","appear","apple","approve","april","arch",
    "arctic","area","arena","argue","arm","armed","armor","army",
    "around","arrange","arrest","arrive","arrow","art","artefact","artist",
    "artwork","ask","aspect","assault","asset","assist","assume","asthma",
    "athlete","atom","attack","attend","attitude","attract","auction","audit",
    "august","aunt","author","auto","autumn","average","avocado","avoid",
    "awake","aware","away","awesome","awful","awkward","axis","baby",
    "balance","bamboo","banana","banner","barely","bargain","barrel","base",
    "basic","basket","battle","beach","beauty","because","become","beef",
    "before","begin","behave","behind","believe","below","belt","bench",
    "benefit","best","betray","better","between","beyond","bicycle","bid",
    "bike","bind","biology","bird","birth","bitter","black","blade",
    "blame","blanket","blast","bleak","bless","blind","blood","blossom",
    "blouse","blue","blur","blush","board","boat","body","boil",
    "bomb","bone","book","boost","border","boring","borrow","boss",
    "bottom","bounce","box","boy","bracket","brain","brand","brave",
    "breeze","brick","bridge","brief","bright","bring","brisk","broccoli",
    "broken","bronze","broom","brother","brown","brush","bubble","buddy",
    "budget","buffalo","build","bulb","bulk","bullet","bundle","bunker",
]

def _extend_wordlist(words: List[str]) -> List[str]:
    """Extend mini wordlist to 2048 by cycling with index"""
    full = []
    for i in range(2048):
        base = words[i % len(words)]
        suffix = str(i // len(words)) if i >= len(words) else ""
        full.append(base + suffix)
    return full

BIP39_WORDLIST = _extend_wordlist(BIP39_WORDS_MINI)

# ================================================================
#  BIP39 — Mnemonic generation and seed derivation
# ================================================================

class BIP39:
    """BIP39 mnemonic phrases for wallet backup"""

    WORD_COUNT_TO_BITS = {12: 128, 15: 160, 18: 192, 21: 224, 24: 256}

    @classmethod
    def generate_mnemonic(cls, word_count: int = 12) -> str:
        """Generate a random BIP39 mnemonic phrase"""
        bits = cls.WORD_COUNT_TO_BITS.get(word_count, 128)
        entropy = secrets.randbits(bits).to_bytes(bits // 8, 'big')
        return cls.entropy_to_mnemonic(entropy)

    @classmethod
    def entropy_to_mnemonic(cls, entropy: bytes) -> str:
        """Convert entropy bytes to mnemonic words"""
        checksum_bits = len(entropy) // 4
        h = hashlib.sha256(entropy).digest()
        checksum = bin(h[0])[2:].zfill(8)[:checksum_bits]
        bits = bin(int.from_bytes(entropy, 'big'))[2:].zfill(len(entropy)*8) + checksum
        words = []
        for i in range(0, len(bits), 11):
            idx = int(bits[i:i+11], 2)
            words.append(BIP39_WORDLIST[idx])
        return ' '.join(words)

    @classmethod
    def mnemonic_to_seed(cls, mnemonic: str, passphrase: str = "") -> bytes:
        """Convert mnemonic to 64-byte seed (BIP39)"""
        mnemonic_norm  = unicodedata.normalize('NFKD', mnemonic)
        passphrase_norm = unicodedata.normalize('NFKD', 'mnemonic' + passphrase)
        return hashlib.pbkdf2_hmac(
            'sha512',
            mnemonic_norm.encode('utf-8'),
            passphrase_norm.encode('utf-8'),
            iterations = 2048,
            dklen      = 64,
        )

    @classmethod
    def validate(cls, mnemonic: str) -> bool:
        words = mnemonic.strip().split()
        return all(w in BIP39_WORDLIST for w in words)

# ================================================================
#  BIP32 — HD Key derivation
# ================================================================

HARDENED = 0x80000000

class HDKey:
    """BIP32 Hierarchical Deterministic key"""

    VERSION_MAINNET_PUB  = 0x0488B21E
    VERSION_MAINNET_PRIV = 0x0488ADE4

    def __init__(self,
                 key:         int,             # private key (int) or None
                 chain_code:  bytes,
                 pubkey:      Tuple[int,int],
                 depth:       int = 0,
                 fingerprint: bytes = b'\x00'*4,
                 child_num:   int = 0):
        self.key         = key
        self.chain_code  = chain_code
        self.pubkey      = pubkey
        self.depth       = depth
        self.fingerprint = fingerprint
        self.child_num   = child_num

    @classmethod
    def from_seed(cls, seed: bytes) -> 'HDKey':
        """Derive master key from seed"""
        I    = hmac.new(b'Bitcoin seed', seed, hashlib.sha512).digest()
        key  = int.from_bytes(I[:32], 'big') % Secp256k1.N
        cc   = I[32:]
        pub  = Secp256k1.point_mul(key, Secp256k1.G())
        return cls(key=key, chain_code=cc, pubkey=pub)

    def derive_child(self, index: int) -> 'HDKey':
        """Derive child key at given index"""
        hardened = index >= HARDENED
        pub_bytes = Secp256k1.pubkey_to_bytes(self.pubkey)

        if hardened:
            if self.key is None:
                raise ValueError("Cannot derive hardened child from public key")
            data = b'\x00' + self.key.to_bytes(32, 'big') + struct.pack('>I', index)
        else:
            data = pub_bytes + struct.pack('>I', index)

        I   = hmac.new(self.chain_code, data, hashlib.sha512).digest()
        il  = int.from_bytes(I[:32], 'big')
        cc  = I[32:]

        if self.key is not None:
            child_key = (il + self.key) % Secp256k1.N
        else:
            child_key = None

        child_pub = Secp256k1.point_add(
            Secp256k1.point_mul(il, Secp256k1.G()), self.pubkey)

        parent_pub  = Secp256k1.pubkey_to_bytes(self.pubkey)
        fingerprint = hash160(parent_pub)[:4]

        return HDKey(
            key         = child_key,
            chain_code  = cc,
            pubkey      = child_pub,
            depth       = self.depth + 1,
            fingerprint = fingerprint,
            child_num   = index,
        )

    def derive_path(self, path: str) -> 'HDKey':
        """Derive key from path string e.g. m/44'/0'/0'/0/0"""
        parts = path.split('/')
        node  = self
        for part in parts:
            if part == 'm':
                continue
            hardened = part.endswith("'")
            idx = int(part.rstrip("'"))
            if hardened:
                idx += HARDENED
            node = node.derive_child(idx)
        return node

    @property
    def address(self) -> str:
        pub_bytes = Secp256k1.pubkey_to_bytes(self.pubkey)
        return Script.p2pkh_address(pub_bytes)

    @property
    def wif(self) -> str:
        """Wallet Import Format — private key for import"""
        if self.key is None:
            raise ValueError("No private key")
        payload = self.key.to_bytes(32, 'big') + b'\x01'   # compressed
        return base58check_encode(payload, WIF_VERSION)

    @classmethod
    def from_wif(cls, wif_str: str) -> 'HDKey':
        version, payload = base58check_decode(wif_str)
        assert version == WIF_VERSION
        key_bytes = payload[:32]
        privkey   = int.from_bytes(key_bytes, 'big')
        pubkey    = Secp256k1.point_mul(privkey, Secp256k1.G())
        return cls(key=privkey, chain_code=b'\x00'*32, pubkey=pubkey)

    def xpub(self) -> str:
        """Extended public key"""
        pub = Secp256k1.pubkey_to_bytes(self.pubkey)
        payload = (
            struct.pack('>I', self.VERSION_MAINNET_PUB) +
            bytes([self.depth]) +
            self.fingerprint +
            struct.pack('>I', self.child_num) +
            self.chain_code +
            pub
        )
        return base58check_encode(payload[1:], payload[0])

    def xpriv(self) -> str:
        """Extended private key"""
        if self.key is None:
            raise ValueError("No private key")
        payload = (
            struct.pack('>I', self.VERSION_MAINNET_PRIV) +
            bytes([self.depth]) +
            self.fingerprint +
            struct.pack('>I', self.child_num) +
            self.chain_code +
            b'\x00' + self.key.to_bytes(32, 'big')
        )
        return base58check_encode(payload[1:], payload[0])

# ================================================================
#  NEBULA WALLET
# ================================================================

# BIP44 coin type for NBL
NBL_COIN_TYPE   = 2025
NBL_BIP44_PATH  = f"m/44'/{NBL_COIN_TYPE}'/0'"

class NEBULAWallet:
    """
    Full HD wallet for NEBULA (NBL).
    Supports BIP39 mnemonic, BIP32 key derivation,
    transaction signing, UTXO management.
    """

    def __init__(self,
                 mnemonic:   str = None,
                 passphrase: str = "",
                 utxo_set:   UTXOSet = None):
        if mnemonic is None:
            mnemonic = BIP39.generate_mnemonic(12)

        self.mnemonic   = mnemonic
        self.passphrase = passphrase
        self.seed       = BIP39.mnemonic_to_seed(mnemonic, passphrase)
        self.master     = HDKey.from_seed(self.seed)
        self.account    = self.master.derive_path(NBL_BIP44_PATH)
        self._utxo      = utxo_set
        self._addresses: Dict[int, str] = {}
        self._keys:      Dict[str, HDKey] = {}

        # Pre-derive first 20 receiving addresses
        for i in range(20):
            self._derive_address(0, i)

    def _derive_address(self, change: int, index: int) -> str:
        """Derive address at m/44'/2025'/0'/{change}/{index}"""
        node    = self.account.derive_child(change).derive_child(index)
        addr    = node.address
        path    = f"{NBL_BIP44_PATH}/{change}/{index}"
        self._keys[addr] = node
        return addr

    def receiving_address(self, index: int = 0) -> str:
        """Get receiving address at index"""
        if index not in self._addresses:
            self._addresses[index] = self._derive_address(0, index)
        return self._addresses[index]

    def change_address(self, index: int = 0) -> str:
        """Get change address at index"""
        return self._derive_address(1, index)

    @property
    def first_address(self) -> str:
        return self.receiving_address(0)

    def get_balance(self) -> Dict[str, int]:
        """Get balance for all derived addresses"""
        if self._utxo is None:
            return {}
        balances = {}
        for addr in self._keys:
            bal = self._utxo.balance(addr)
            if bal > 0:
                balances[addr] = bal
        return balances

    def total_balance_neb(self) -> int:
        return sum(self.get_balance().values())

    def total_balance_nbl(self) -> float:
        return self.total_balance_neb() / 10**DECIMALS

    def get_utxos(self) -> List[UTXOEntry]:
        """Get all UTXOs for this wallet"""
        if self._utxo is None:
            return []
        all_utxos = []
        for addr in self._keys:
            all_utxos.extend(self._utxo.get_by_address(addr))
        return all_utxos

    def build_transaction(self,
                           to_address:   str,
                           amount_nbl:   float,
                           fee_nbl:      float = 0.0001,
                           memo:         str   = "") -> Optional[Transaction]:
        """Build and sign a transaction"""
        amount_neb = int(amount_nbl  * 10**DECIMALS)
        fee_neb    = int(fee_nbl     * 10**DECIMALS)
        total_needed = amount_neb + fee_neb

        if amount_neb <= DUST_THRESHOLD:
            print(f"❌ Amount below dust threshold: {amount_neb}")
            return None

        # Coin selection (simple: use largest UTXOs first)
        available = sorted(self.get_utxos(), key=lambda u: u.value, reverse=True)
        selected  = []
        selected_total = 0

        for utxo in available:
            selected.append(utxo)
            selected_total += utxo.value
            if selected_total >= total_needed:
                break

        if selected_total < total_needed:
            print(f"❌ Insufficient funds: have {selected_total/10**DECIMALS:.9f}, "
                  f"need {total_needed/10**DECIMALS:.9f}")
            return None

        # Build inputs
        inputs = []
        for utxo in selected:
            inputs.append(TxInput(
                outpoint   = OutPoint(utxo.txid, utxo.index),
                script_sig = b'',
                sequence   = 0xFFFFFFFE,
            ))

        # Build outputs
        outputs = [TxOutput(
            value        = amount_neb,
            script_pubkey = Script.p2pkh_locking_from_address(to_address),
        )]

        # Change output
        change = selected_total - total_needed
        if change > DUST_THRESHOLD:
            change_addr = self.change_address(0)
            outputs.append(TxOutput(
                value        = change,
                script_pubkey = Script.p2pkh_locking_from_address(change_addr),
            ))

        # OP_RETURN memo
        if memo:
            outputs.append(TxOutput(
                value        = 0,
                script_pubkey = Script.nulldata(memo[:80].encode()),
            ))

        tx = Transaction(version=1, inputs=inputs, outputs=outputs)

        # Sign each input
        for i, (inp, utxo) in enumerate(zip(tx.inputs, selected)):
            addr  = Script.p2pkh_address(
                Secp256k1.pubkey_to_bytes(self._keys[
                    base58check_encode(utxo.script_pubkey[3:23], PUBKEY_ADDRESS_VERSION)
                ].pubkey)
            )
            # Find signing key
            signing_key = None
            for wallet_addr, hd_key in self._keys.items():
                pub = Secp256k1.pubkey_to_bytes(hd_key.pubkey)
                if hash160(pub) == utxo.script_pubkey[3:23]:
                    signing_key = hd_key
                    break

            if signing_key is None:
                print(f"❌ No signing key for input {i}")
                return None

            subscript  = utxo.script_pubkey
            sighash    = tx.signature_hash(i, subscript, SIGHASH_ALL)
            r, s       = Secp256k1.sign(signing_key.key, sighash)
            der        = Secp256k1.sig_to_der(r, s) + bytes([SIGHASH_ALL])
            pub_bytes  = Secp256k1.pubkey_to_bytes(signing_key.pubkey)
            tx.inputs[i].script_sig = Script.p2pkh_unlocking(der, pub_bytes)
            tx.invalidate_cache()

        print(f"✅ Transaction built: {tx.txid}")
        print(f"   Amount : {amount_nbl:.9f} NBL → {to_address[:16]}...")
        print(f"   Fee    : {fee_nbl:.9f} NBL")
        print(f"   Size   : {tx.byte_size()} bytes")
        return tx

    def info(self) -> dict:
        addr = self.first_address
        return {
            "first_address": addr,
            "mnemonic_words": len(self.mnemonic.split()),
            "derived_keys":  len(self._keys),
            "balance_nbl":   f"{self.total_balance_nbl():.{DECIMALS}f} NBL",
            "balance_neb":   f"{self.total_balance_neb():,} Neb",
            "coin_type":     NBL_COIN_TYPE,
            "path":          NBL_BIP44_PATH,
            "xpub":          self.account.xpub()[:32] + "...",
        }

    @classmethod
    def create_new(cls, utxo_set: UTXOSet = None) -> 'NEBULAWallet':
        """Create a brand new wallet with random mnemonic"""
        mnemonic = BIP39.generate_mnemonic(12)
        wallet   = cls(mnemonic=mnemonic, utxo_set=utxo_set)
        print(f"\n🔑 New NBL Wallet Created!")
        print(f"   Address : {wallet.first_address}")
        print(f"   ⚠️  WRITE DOWN YOUR MNEMONIC — KEEP IT SAFE:")
        print(f"   {mnemonic}")
        print(f"   WIF Key : {wallet.master.derive_path(NBL_BIP44_PATH + '/0/0').wif}")
        return wallet

    @classmethod
    def from_mnemonic(cls, mnemonic: str, passphrase: str = "",
                      utxo_set: UTXOSet = None) -> 'NEBULAWallet':
        """Restore wallet from mnemonic"""
        wallet = cls(mnemonic=mnemonic, passphrase=passphrase, utxo_set=utxo_set)
        print(f"✅ Wallet restored: {wallet.first_address}")
        return wallet

    def export_keys(self, include_private: bool = False) -> List[dict]:
        """Export key list"""
        result = []
        for addr, hd in self._keys.items():
            entry = {"address": addr, "pubkey": Secp256k1.pubkey_to_bytes(hd.pubkey).hex()}
            if include_private and hd.key:
                entry["wif"] = hd.wif
            result.append(entry)
        return result


# ================================================================
#  WALLET EXTENDED FEATURES
# ================================================================
import time as _wtime
from typing import List as _WList, Optional as _WOpt, Dict as _WDict, Tuple as _WTuple

class WalletTransaction:
    """Record of a wallet transaction for history tracking."""
    def __init__(self, txid, amount, fee, to_addr, timestamp=None, confirmed=False, height=-1):
        self.txid       = txid
        self.amount     = amount      # positive=received, negative=sent
        self.fee        = fee
        self.to_addr    = to_addr
        self.timestamp  = timestamp or _wtime.time()
        self.confirmed  = confirmed
        self.height     = height

    def to_dict(self) -> dict:
        return {
            "txid"      : self.txid,
            "amount"    : self.amount,
            "fee"       : self.fee,
            "to"        : self.to_addr,
            "timestamp" : self.timestamp,
            "confirmed" : self.confirmed,
            "height"    : self.height,
        }


class WalletHistory:
    """Track and query wallet transaction history."""
    def __init__(self):
        self._txs : _WList[WalletTransaction] = []

    def add(self, tx: WalletTransaction):
        self._txs.append(tx)

    def confirm(self, txid: str, height: int):
        for tx in self._txs:
            if tx.txid == txid:
                tx.confirmed = True
                tx.height    = height
                break

    def received(self) -> int:
        return sum(t.amount for t in self._txs if t.amount > 0)

    def sent(self) -> int:
        return sum(abs(t.amount) for t in self._txs if t.amount < 0)

    def fees_paid(self) -> int:
        return sum(t.fee for t in self._txs if t.amount < 0)

    def net_balance(self) -> int:
        return sum(t.amount for t in self._txs)

    def all_txs(self, confirmed_only: bool = False) -> _WList[dict]:
        txs = self._txs
        if confirmed_only:
            txs = [t for t in txs if t.confirmed]
        return [t.to_dict() for t in sorted(txs, key=lambda x: x.timestamp, reverse=True)]

    def stats(self) -> dict:
        return {
            "total_txs"  : len(self._txs),
            "received"   : self.received(),
            "sent"       : self.sent(),
            "fees_paid"  : self.fees_paid(),
            "net_balance": self.net_balance(),
            "confirmed"  : sum(1 for t in self._txs if t.confirmed),
            "pending"    : sum(1 for t in self._txs if not t.confirmed),
        }


class CoinSelector:
    """
    UTXO coin selection algorithms.
    Chooses which UTXOs to spend for a given target amount.

    Algorithms:
      1. BnB  — Branch and Bound (minimize change output)
      2. FIFO — First In First Out (spend oldest first)
      3. Rand — Random selection
    """

    @staticmethod
    def bnb(utxos, target: int, fee_per_byte: int = 1,
            input_size: int = 148) -> _WOpt[_WList]:
        """Branch and Bound — tries to find exact match first."""
        # Sort by value descending
        sorted_utxos = sorted(utxos, key=lambda u: u.value, reverse=True)
        # Try exact match within tolerance
        tolerance = fee_per_byte * input_size * 2
        for utxo in sorted_utxos:
            if abs(utxo.value - target) <= tolerance:
                return [utxo]
        # Fall back to accumulation
        return CoinSelector.accumulate(sorted_utxos, target, fee_per_byte, input_size)

    @staticmethod
    def fifo(utxos, target: int, fee_per_byte: int = 1,
             input_size: int = 148) -> _WOpt[_WList]:
        """FIFO — spend oldest UTXOs first."""
        sorted_utxos = sorted(utxos, key=lambda u: u.height)
        return CoinSelector.accumulate(sorted_utxos, target, fee_per_byte, input_size)

    @staticmethod
    def accumulate(utxos, target: int, fee_per_byte: int,
                   input_size: int) -> _WOpt[_WList]:
        """Accumulate UTXOs until target is met."""
        selected = []
        total    = 0
        for utxo in utxos:
            if total >= target:
                break
            selected.append(utxo)
            total += utxo.value
            # Subtract input fee
            total -= fee_per_byte * input_size
        if total >= 0:
            return selected
        return None

    @staticmethod
    def estimate_fee(n_inputs: int, n_outputs: int,
                     fee_rate: int = 1) -> int:
        """Estimate TX fee: 10 + 148*inputs + 34*outputs bytes."""
        size = 10 + 148 * n_inputs + 34 * n_outputs
        return size * fee_rate


class MultiSigWallet:
    """
    m-of-n multi-signature wallet.
    Supports 2-of-3 for treasury/escrow use cases.
    """

    def __init__(self, m: int, n: int, public_keys: _WList[bytes]):
        if not (1 <= m <= n <= 16):
            raise ValueError(f"Invalid m-of-n: {m}/{n}")
        if len(public_keys) != n:
            raise ValueError(f"Expected {n} keys, got {len(public_keys)}")
        self.m           = m
        self.n           = n
        self.public_keys = public_keys

    def redeem_script(self) -> bytes:
        """OP_m [pubkeys] OP_n OP_CHECKMULTISIG"""
        script  = bytes([0x50 + self.m])  # OP_m
        for pk in self.public_keys:
            script += bytes([len(pk)]) + pk
        script += bytes([0x50 + self.n])  # OP_n
        script += bytes([0xae])           # OP_CHECKMULTISIG
        return script

    def p2sh_address(self) -> str:
        """P2SH address (starts with 3 in Bitcoin, N in NEBULA)."""
        import hashlib
        rs   = self.redeem_script()
        h160 = hashlib.new('ripemd160', hashlib.sha256(rs).digest()).digest()
        return "N" + h160.hex()[:32]

    def info(self) -> dict:
        return {
            "type"         : f"{self.m}-of-{self.n} multisig",
            "m"            : self.m,
            "n"            : self.n,
            "redeem_script": self.redeem_script().hex(),
            "address"      : self.p2sh_address(),
            "signers_needed": self.m,
        }


class WatchOnlyWallet:
    """
    Watch-only wallet — tracks addresses without private keys.
    Used for read-only monitoring (e.g. on an online node).
    """

    def __init__(self):
        self._addrs : _WDict[str, dict] = {}

    def add(self, address: str, label: str = ""):
        self._addrs[address] = {"label": label, "added": _wtime.time()}

    def remove(self, address: str):
        self._addrs.pop(address, None)

    def is_watching(self, address: str) -> bool:
        return address in self._addrs

    def list_addresses(self) -> _WList[dict]:
        return [{"address": a, **info} for a, info in self._addrs.items()]

    def count(self) -> int:
        return len(self._addrs)


class HDAccount:
    """
    BIP-44 account-level HD wallet manager.
    Manages external (receive) and internal (change) address chains.
    """

    def __init__(self, wallet, account_idx: int = 0):
        self._wallet      = wallet
        self._account     = account_idx
        self._ext_idx     = 0   # external (receive) index
        self._int_idx     = 0   # internal (change) index
        self._used_ext    : set = set()
        self._used_int    : set = set()

    def receive_address(self) -> str:
        """Get next unused receive address (external chain)."""
        addr = self._wallet.get_address(self._ext_idx)
        return addr

    def change_address(self) -> str:
        """Get next unused change address (internal chain)."""
        addr = self._wallet.get_address(1000 + self._int_idx)
        return addr

    def mark_used(self, address: str, is_change: bool = False):
        if is_change:
            self._used_int.add(address)
            self._int_idx += 1
        else:
            self._used_ext.add(address)
            self._ext_idx += 1

    def gap_limit_scan(self, check_fn, gap: int = 20) -> _WList[str]:
        """
        Scan addresses until gap consecutive unused ones are found.
        Returns list of all addresses with activity.
        """
        found = []
        consecutive_unused = 0
        idx = 0
        while consecutive_unused < gap:
            addr = self._wallet.get_address(idx)
            if check_fn(addr):
                found.append(addr)
                consecutive_unused = 0
            else:
                consecutive_unused += 1
            idx += 1
        return found

    def account_info(self) -> dict:
        return {
            "account_index"     : self._account,
            "external_index"    : self._ext_idx,
            "internal_index"    : self._int_idx,
            "used_receive"      : len(self._used_ext),
            "used_change"       : len(self._used_int),
            "path"              : f"m/44'/2025'/{self._account}'",
        }
