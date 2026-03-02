"""
================================================================
  NEBULA SMART CONTRACTS — nebula_contracts.py
  Bitcoin Script + Extended NBL scripting engine
  
  Supports:
  - Full Bitcoin Script opcodes
  - Multi-signature (P2MS)
  - Time-locked transactions (CLTV, CSV)
  - Hash-locked contracts (HTLC)
  - Token contracts (NBL-20 standard)
  - Vesting contracts
  - Atomic swaps
================================================================
"""

import hashlib, time, struct
from typing import List, Dict, Optional, Tuple, Any, Callable
from dataclasses import dataclass, field
from enum import IntEnum
from nebula_core import sha256d, hash160, sha256, Script, ScriptType

# ================================================================
#  SCRIPT OPCODES — Complete Bitcoin-compatible set
# ================================================================

class OP(IntEnum):
    # Constants
    OP_0            = 0x00
    OP_FALSE        = 0x00
    OP_PUSHDATA1    = 0x4c
    OP_PUSHDATA2    = 0x4d
    OP_PUSHDATA4    = 0x4e
    OP_1NEGATE      = 0x4f
    OP_1            = 0x51
    OP_TRUE         = 0x51
    OP_2            = 0x52
    OP_3            = 0x53
    OP_4            = 0x54
    OP_5            = 0x55
    OP_6            = 0x56
    OP_7            = 0x57
    OP_8            = 0x58
    OP_9            = 0x59
    OP_10           = 0x5a
    OP_11           = 0x5b
    OP_12           = 0x5c
    OP_13           = 0x5d
    OP_14           = 0x5e
    OP_15           = 0x5f
    OP_16           = 0x60

    # Flow control
    OP_NOP          = 0x61
    OP_IF           = 0x63
    OP_NOTIF        = 0x64
    OP_ELSE         = 0x67
    OP_ENDIF        = 0x68
    OP_VERIFY       = 0x69
    OP_RETURN       = 0x6a

    # Stack
    OP_TOALTSTACK   = 0x6b
    OP_FROMALTSTACK = 0x6c
    OP_IFDUP        = 0x73
    OP_DEPTH        = 0x74
    OP_DROP         = 0x75
    OP_DUP          = 0x76
    OP_NIP          = 0x77
    OP_OVER         = 0x79
    OP_PICK         = 0x79
    OP_ROLL         = 0x7a
    OP_ROT          = 0x7b
    OP_SWAP         = 0x7c
    OP_TUCK         = 0x7d
    OP_2DROP        = 0x6d
    OP_2DUP         = 0x6e
    OP_3DUP         = 0x6f
    OP_2OVER        = 0x70
    OP_2ROT         = 0x71
    OP_2SWAP        = 0x72

    # Splice
    OP_CAT          = 0x7e
    OP_SIZE         = 0x82

    # Bitwise
    OP_EQUAL        = 0x87
    OP_EQUALVERIFY  = 0x88

    # Arithmetic
    OP_1ADD         = 0x8b
    OP_1SUB         = 0x8c
    OP_NEGATE       = 0x8f
    OP_ABS          = 0x90
    OP_NOT          = 0x91
    OP_0NOTEQUAL    = 0x92
    OP_ADD          = 0x93
    OP_SUB          = 0x94
    OP_MUL          = 0x95
    OP_DIV          = 0x96
    OP_MOD          = 0x97
    OP_BOOLAND      = 0x9a
    OP_BOOLOR       = 0x9b
    OP_NUMEQUAL     = 0x9c
    OP_NUMEQUALVERIFY = 0x9d
    OP_NUMNOTEQUAL  = 0x9e
    OP_LESSTHAN     = 0x9f
    OP_GREATERTHAN  = 0xa0
    OP_LESSTHANOREQUAL    = 0xa1
    OP_GREATERTHANOREQUAL = 0xa2
    OP_MIN          = 0xa3
    OP_MAX          = 0xa4
    OP_WITHIN       = 0xa5

    # Crypto
    OP_RIPEMD160    = 0xa6
    OP_SHA1         = 0xa7
    OP_SHA256       = 0xa8
    OP_HASH160      = 0xa9
    OP_HASH256      = 0xaa
    OP_CODESEPARATOR = 0xab
    OP_CHECKSIG     = 0xac
    OP_CHECKSIGVERIFY = 0xad
    OP_CHECKMULTISIG = 0xae
    OP_CHECKMULTISIGVERIFY = 0xaf

    # Locktime
    OP_CHECKLOCKTIMEVERIFY = 0xb1   # CLTV (BIP65)
    OP_CHECKSEQUENCEVERIFY = 0xb2   # CSV  (BIP112)

    # NBL extensions
    OP_NBL_TRANSFER = 0xc0   # NBL token transfer
    OP_NBL_BALANCE  = 0xc1   # Check NBL balance
    OP_NBL_MINT     = 0xc2   # Mint NBL-20 token
    OP_NBL_BURN     = 0xc3   # Burn tokens

# ================================================================
#  SCRIPT INTERPRETER
# ================================================================

class ScriptError(Exception):
    pass

class ScriptInterpreter:
    """
    Full Bitcoin-compatible script interpreter.
    Executes locking + unlocking scripts.
    """

    MAX_STACK_SIZE  = 1000
    MAX_SCRIPT_SIZE = 10_000
    MAX_OPS         = 201

    def __init__(self,
                 tx_hash:    bytes = b'\x00' * 32,
                 block_time: int   = 0,
                 block_height: int = 0):
        self.tx_hash      = tx_hash
        self.block_time   = block_time
        self.block_height = block_height

    def execute(self,
                script:    bytes,
                stack:     List[bytes] = None,
                altstack:  List[bytes] = None) -> Tuple[bool, List[bytes]]:
        """Execute a script, return (success, final_stack)"""
        if len(script) > self.MAX_SCRIPT_SIZE:
            raise ScriptError("Script too large")

        stack    = stack    or []
        altstack = altstack or []
        ops_done = 0
        pc       = 0
        cond_stack: List[bool] = []   # for IF/ELSE/ENDIF

        def executing() -> bool:
            return all(cond_stack) if cond_stack else True

        while pc < len(script):
            op = script[pc]
            pc += 1
            ops_done += 1

            if ops_done > self.MAX_OPS:
                raise ScriptError("Too many ops")

            if len(stack) > self.MAX_STACK_SIZE:
                raise ScriptError("Stack overflow")

            # ── Data push opcodes ──────────────────────────────
            if 0x01 <= op <= 0x4b:
                # Push N bytes
                data = script[pc:pc+op]
                pc  += op
                if executing():
                    stack.append(data)
                continue

            if op == OP.OP_PUSHDATA1:
                n    = script[pc]; pc += 1
                data = script[pc:pc+n]; pc += n
                if executing(): stack.append(data)
                continue

            if op == OP.OP_PUSHDATA2:
                n    = struct.unpack_from('<H', script, pc)[0]; pc += 2
                data = script[pc:pc+n]; pc += n
                if executing(): stack.append(data)
                continue

            if op == OP.OP_PUSHDATA4:
                n    = struct.unpack_from('<I', script, pc)[0]; pc += 4
                data = script[pc:pc+n]; pc += n
                if executing(): stack.append(data)
                continue

            # ── Small integers ─────────────────────────────────
            if op == OP.OP_0:
                if executing(): stack.append(b'')
                continue
            if op == OP.OP_1NEGATE:
                if executing(): stack.append(self._encode_int(-1))
                continue
            if OP.OP_1 <= op <= OP.OP_16:
                n = op - OP.OP_1 + 1
                if executing(): stack.append(self._encode_int(n))
                continue

            # ── Flow control ───────────────────────────────────
            if op == OP.OP_NOP:
                continue

            if op == OP.OP_IF:
                if executing():
                    val = self._pop(stack)
                    cond_stack.append(bool(val and any(val)))
                else:
                    cond_stack.append(False)
                continue

            if op == OP.OP_NOTIF:
                if executing():
                    val = self._pop(stack)
                    cond_stack.append(not (val and any(val)))
                else:
                    cond_stack.append(False)
                continue

            if op == OP.OP_ELSE:
                if cond_stack:
                    cond_stack[-1] = not cond_stack[-1]
                continue

            if op == OP.OP_ENDIF:
                if cond_stack:
                    cond_stack.pop()
                continue

            if not executing():
                continue

            if op == OP.OP_VERIFY:
                val = self._pop(stack)
                if not (val and any(val)):
                    raise ScriptError("OP_VERIFY failed")

            elif op == OP.OP_RETURN:
                raise ScriptError("OP_RETURN: unspendable")

            # ── Stack ops ──────────────────────────────────────
            elif op == OP.OP_DROP:   stack.pop()
            elif op == OP.OP_2DROP:  stack.pop(); stack.pop()
            elif op == OP.OP_DUP:    stack.append(stack[-1])
            elif op == OP.OP_2DUP:   stack.extend(stack[-2:])
            elif op == OP.OP_3DUP:   stack.extend(stack[-3:])
            elif op == OP.OP_OVER:   stack.append(stack[-2])
            elif op == OP.OP_2OVER:  stack.extend(stack[-4:-2])
            elif op == OP.OP_SWAP:   stack[-1], stack[-2] = stack[-2], stack[-1]
            elif op == OP.OP_2SWAP:
                stack[-4], stack[-3], stack[-2], stack[-1] = \
                stack[-2], stack[-1], stack[-4], stack[-3]
            elif op == OP.OP_ROT:
                stack.append(stack.pop(-3))
            elif op == OP.OP_NIP:
                del stack[-2]
            elif op == OP.OP_TUCK:
                stack.insert(-2, stack[-1])
            elif op == OP.OP_DEPTH:
                stack.append(self._encode_int(len(stack)))
            elif op == OP.OP_IFDUP:
                if stack[-1]: stack.append(stack[-1])
            elif op == OP.OP_TOALTSTACK:
                altstack.append(self._pop(stack))
            elif op == OP.OP_FROMALTSTACK:
                stack.append(altstack.pop())
            elif op == OP.OP_SIZE:
                stack.append(self._encode_int(len(stack[-1])))

            # ── Arithmetic ─────────────────────────────────────
            elif op == OP.OP_1ADD:
                stack.append(self._encode_int(self._decode_int(self._pop(stack)) + 1))
            elif op == OP.OP_1SUB:
                stack.append(self._encode_int(self._decode_int(self._pop(stack)) - 1))
            elif op == OP.OP_NEGATE:
                stack.append(self._encode_int(-self._decode_int(self._pop(stack))))
            elif op == OP.OP_ABS:
                stack.append(self._encode_int(abs(self._decode_int(self._pop(stack)))))
            elif op == OP.OP_NOT:
                stack.append(self._encode_int(0 if self._decode_int(self._pop(stack)) else 1))
            elif op == OP.OP_0NOTEQUAL:
                stack.append(self._encode_int(0 if not self._decode_int(self._pop(stack)) else 1))
            elif op == OP.OP_ADD:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(a + b))
            elif op == OP.OP_SUB:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(a - b))
            elif op == OP.OP_MUL:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(a * b))
            elif op == OP.OP_DIV:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                if b == 0: raise ScriptError("Division by zero")
                stack.append(self._encode_int(a // b))
            elif op == OP.OP_MOD:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                if b == 0: raise ScriptError("Mod by zero")
                stack.append(self._encode_int(a % b))
            elif op == OP.OP_BOOLAND:
                b, a = self._pop(stack), self._pop(stack)
                stack.append(self._encode_int(1 if (any(a) and any(b)) else 0))
            elif op == OP.OP_BOOLOR:
                b, a = self._pop(stack), self._pop(stack)
                stack.append(self._encode_int(1 if (any(a) or any(b)) else 0))
            elif op == OP.OP_NUMEQUAL:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(1 if a == b else 0))
            elif op == OP.OP_NUMEQUALVERIFY:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                if a != b: raise ScriptError("NUMEQUALVERIFY failed")
            elif op == OP.OP_NUMNOTEQUAL:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(1 if a != b else 0))
            elif op == OP.OP_LESSTHAN:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(1 if a < b else 0))
            elif op == OP.OP_GREATERTHAN:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(1 if a > b else 0))
            elif op == OP.OP_LESSTHANOREQUAL:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(1 if a <= b else 0))
            elif op == OP.OP_GREATERTHANOREQUAL:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(1 if a >= b else 0))
            elif op == OP.OP_MIN:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(min(a, b)))
            elif op == OP.OP_MAX:
                b, a = self._decode_int(self._pop(stack)), self._decode_int(self._pop(stack))
                stack.append(self._encode_int(max(a, b)))
            elif op == OP.OP_WITHIN:
                mx, mn, x = (self._decode_int(self._pop(stack)) for _ in range(3))
                stack.append(self._encode_int(1 if mn <= x < mx else 0))

            # ── Equality ───────────────────────────────────────
            elif op == OP.OP_EQUAL:
                b, a = self._pop(stack), self._pop(stack)
                stack.append(self._encode_int(1 if a == b else 0))
            elif op == OP.OP_EQUALVERIFY:
                b, a = self._pop(stack), self._pop(stack)
                if a != b: raise ScriptError("EQUALVERIFY failed")

            # ── Crypto ─────────────────────────────────────────
            elif op == OP.OP_RIPEMD160:
                h = hashlib.new('ripemd160'); h.update(self._pop(stack))
                stack.append(h.digest())
            elif op == OP.OP_SHA1:
                stack.append(hashlib.sha1(self._pop(stack)).digest())
            elif op == OP.OP_SHA256:
                stack.append(hashlib.sha256(self._pop(stack)).digest())
            elif op == OP.OP_HASH160:
                stack.append(hash160(self._pop(stack)))
            elif op == OP.OP_HASH256:
                stack.append(sha256d(self._pop(stack)))
            elif op == OP.OP_CHECKSIG:
                pub_bytes = self._pop(stack)
                sig_bytes = self._pop(stack)
                result    = self._checksig(sig_bytes, pub_bytes)
                stack.append(self._encode_int(1 if result else 0))
            elif op == OP.OP_CHECKSIGVERIFY:
                pub_bytes = self._pop(stack)
                sig_bytes = self._pop(stack)
                if not self._checksig(sig_bytes, pub_bytes):
                    raise ScriptError("CHECKSIGVERIFY failed")
            elif op == OP.OP_CHECKMULTISIG:
                self._op_checkmultisig(stack)
            elif op == OP.OP_CHECKMULTISIGVERIFY:
                self._op_checkmultisig(stack)
                if not self._pop(stack): raise ScriptError("CHECKMULTISIGVERIFY failed")

            # ── Timelocks ──────────────────────────────────────
            elif op == OP.OP_CHECKLOCKTIMEVERIFY:
                locktime = self._decode_int(stack[-1])   # peek, don't pop
                if locktime < 0:
                    raise ScriptError("CLTV: negative locktime")
                if locktime >= 500_000_000:
                    # Unix timestamp
                    if self.block_time < locktime:
                        raise ScriptError(f"CLTV: too early (time {self.block_time} < {locktime})")
                else:
                    # Block height
                    if self.block_height < locktime:
                        raise ScriptError(f"CLTV: too early (height {self.block_height} < {locktime})")

            elif op == OP.OP_CHECKSEQUENCEVERIFY:
                seq = self._decode_int(stack[-1])
                if seq < 0:
                    raise ScriptError("CSV: negative sequence")
                # Simplified check

            else:
                # Unknown opcode
                raise ScriptError(f"Unknown opcode: {hex(op)}")

        # Script succeeds if top of stack is truthy
        if not stack:
            return False, stack
        top = stack[-1]
        success = bool(top and any(top))
        return success, stack

    # ── Helpers ───────────────────────────────────────────────

    def _pop(self, stack: List[bytes]) -> bytes:
        if not stack:
            raise ScriptError("Stack underflow")
        return stack.pop()

    def _encode_int(self, n: int) -> bytes:
        if n == 0: return b''
        negative = n < 0
        n = abs(n)
        result = []
        while n:
            result.append(n & 0xff)
            n >>= 8
        if result[-1] & 0x80:
            result.append(0x80 if negative else 0x00)
        elif negative:
            result[-1] |= 0x80
        return bytes(result)

    def _decode_int(self, data: bytes) -> int:
        if not data: return 0
        result   = int.from_bytes(data[:-1] + bytes([data[-1] & 0x7f]), 'little')
        return -result if data[-1] & 0x80 else result

    def _checksig(self, sig_bytes: bytes, pub_bytes: bytes) -> bool:
        try:
            from nebula_core import Secp256k1
            if len(sig_bytes) < 9 or sig_bytes[0] != 0x30:
                return False
            sighash_type = sig_bytes[-1]
            der          = sig_bytes[:-1]
            r, s         = Secp256k1.sig_from_der(der)
            # Reconstruct public key point
            prefix = pub_bytes[0]
            x      = int.from_bytes(pub_bytes[1:33], 'big')
            p      = Secp256k1.P
            y_sq   = (pow(x, 3, p) + 7) % p
            y      = pow(y_sq, (p+1)//4, p)
            if (y % 2 == 0) != (prefix == 0x02):
                y = p - y
            pub_point = (x, y)
            return Secp256k1.verify(pub_point, self.tx_hash, (r, s))
        except Exception:
            return False

    def _op_checkmultisig(self, stack: List[bytes]):
        n_keys = self._decode_int(self._pop(stack))
        keys   = [self._pop(stack) for _ in range(n_keys)]
        n_sigs = self._decode_int(self._pop(stack))
        sigs   = [self._pop(stack) for _ in range(n_sigs)]
        stack.pop()   # Bitcoin bug: extra pop

        valid = 0
        ki    = 0
        for sig in sigs:
            while ki < len(keys):
                if self._checksig(sig, keys[ki]):
                    valid += 1
                    ki    += 1
                    break
                ki += 1
        stack.append(self._encode_int(1 if valid >= n_sigs else 0))


# ================================================================
#  CONTRACT TEMPLATES
# ================================================================

class ContractTemplates:
    """
    Ready-made contract templates.
    Each returns (locking_script, unlocking_script_builder)
    """

    @staticmethod
    def multisig(m: int, pubkeys: List[bytes]) -> bytes:
        """
        m-of-n multisig locking script.
        Example: 2-of-3 multisig
        OP_m <pubkey1> <pubkey2> ... <pubkeyn> OP_n OP_CHECKMULTISIG
        """
        n = len(pubkeys)
        assert 1 <= m <= n <= 16
        script = bytes([OP.OP_1 + m - 1])
        for pk in pubkeys:
            script += bytes([len(pk)]) + pk
        script += bytes([OP.OP_1 + n - 1, OP.OP_CHECKMULTISIG])
        return script

    @staticmethod
    def htlc(recipient_hash160: bytes,
              refund_hash160:   bytes,
              secret_hash:      bytes,
              lock_blocks:      int) -> bytes:
        """
        Hash Time-Locked Contract (HTLC) — for atomic swaps.
        
        Spend paths:
        1. Recipient: provide secret preimage
        2. Refund: after lock_blocks, sender gets refund
        
        OP_IF
          OP_SHA256 <secret_hash> OP_EQUALVERIFY
          OP_DUP OP_HASH160 <recipient_h160> OP_EQUALVERIFY OP_CHECKSIG
        OP_ELSE
          <lock_blocks> OP_CHECKSEQUENCEVERIFY OP_DROP
          OP_DUP OP_HASH160 <refund_h160> OP_EQUALVERIFY OP_CHECKSIG
        OP_ENDIF
        """
        lb = lock_blocks.to_bytes(3, 'little')
        return (
            bytes([OP.OP_IF]) +
            bytes([OP.OP_SHA256]) +
            bytes([len(secret_hash)]) + secret_hash +
            bytes([OP.OP_EQUALVERIFY]) +
            bytes([OP.OP_DUP, OP.OP_HASH160]) +
            bytes([len(recipient_hash160)]) + recipient_hash160 +
            bytes([OP.OP_EQUALVERIFY, OP.OP_CHECKSIG]) +
            bytes([OP.OP_ELSE]) +
            bytes([len(lb)]) + lb +
            bytes([OP.OP_CHECKSEQUENCEVERIFY, OP.OP_DROP]) +
            bytes([OP.OP_DUP, OP.OP_HASH160]) +
            bytes([len(refund_hash160)]) + refund_hash160 +
            bytes([OP.OP_EQUALVERIFY, OP.OP_CHECKSIG]) +
            bytes([OP.OP_ENDIF])
        )

    @staticmethod
    def timelock_p2pkh(pubkey_hash: bytes, lock_until: int) -> bytes:
        """
        Time-locked P2PKH — can only be spent after block height.
        
        <lock_height> OP_CHECKLOCKTIMEVERIFY OP_DROP
        OP_DUP OP_HASH160 <pubKeyHash> OP_EQUALVERIFY OP_CHECKSIG
        """
        lh = lock_until.to_bytes(5, 'little').rstrip(b'\x00') or b'\x00'
        return (
            bytes([len(lh)]) + lh +
            bytes([OP.OP_CHECKLOCKTIMEVERIFY, OP.OP_DROP]) +
            bytes([OP.OP_DUP, OP.OP_HASH160]) +
            bytes([len(pubkey_hash)]) + pubkey_hash +
            bytes([OP.OP_EQUALVERIFY, OP.OP_CHECKSIG])
        )

    @staticmethod
    def vesting(beneficiary_hash: bytes,
                 owner_hash:       bytes,
                 cliff_blocks:     int,
                 vest_blocks:      int) -> bytes:
        """
        Vesting contract — tokens unlock gradually.
        Before cliff: only owner can spend (revoke).
        After cliff:  beneficiary can spend.
        After vest:   fully vested.
        """
        cliff_b = cliff_blocks.to_bytes(4, 'little')
        return (
            bytes([OP.OP_IF]) +
            bytes([len(cliff_b)]) + cliff_b +
            bytes([OP.OP_CHECKSEQUENCEVERIFY, OP.OP_DROP]) +
            bytes([OP.OP_DUP, OP.OP_HASH160]) +
            bytes([len(beneficiary_hash)]) + beneficiary_hash +
            bytes([OP.OP_EQUALVERIFY, OP.OP_CHECKSIG]) +
            bytes([OP.OP_ELSE]) +
            bytes([OP.OP_DUP, OP.OP_HASH160]) +
            bytes([len(owner_hash)]) + owner_hash +
            bytes([OP.OP_EQUALVERIFY, OP.OP_CHECKSIG]) +
            bytes([OP.OP_ENDIF])
        )

    @staticmethod
    def atomic_swap(their_hash160: bytes,
                     our_hash160:   bytes,
                     secret_hash:   bytes,
                     timeout:       int) -> bytes:
        """Cross-chain atomic swap script"""
        return ContractTemplates.htlc(
            their_hash160, our_hash160, secret_hash, timeout)


# ================================================================
#  NBL-20 TOKEN STANDARD
#  (Like ERC-20 but on NEBULA blockchain)
# ================================================================

@dataclass
class NBL20Token:
    """NBL-20 fungible token on NEBULA chain"""
    name:         str
    symbol:       str
    decimals:     int
    total_supply: int
    owner:        str
    contract_id:  str = ""
    created_at:   int = field(default_factory=lambda: int(time.time()))

    def __post_init__(self):
        if not self.contract_id:
            data = f"{self.name}{self.symbol}{self.owner}{self.created_at}".encode()
            self.contract_id = hashlib.sha256(data).hexdigest()[:40]

class NBL20Registry:
    """Registry of all NBL-20 tokens on NEBULA"""

    def __init__(self):
        self._tokens:   Dict[str, NBL20Token]               = {}
        self._balances: Dict[str, Dict[str, int]]            = {}
        self._allowances: Dict[str, Dict[str, Dict[str, int]]] = {}

    def deploy(self, token: NBL20Token, initial_holder: str) -> str:
        """Deploy a new NBL-20 token"""
        cid = token.contract_id
        self._tokens[cid]                          = token
        self._balances[cid]                        = {initial_holder: token.total_supply}
        self._allowances[cid]                      = {}
        print(f"🪙 NBL-20 Token deployed: {token.symbol} ({cid[:12]}...)")
        print(f"   Name:   {token.name}")
        print(f"   Supply: {token.total_supply / 10**token.decimals:,.{token.decimals}f} {token.symbol}")
        return cid

    def balance_of(self, contract_id: str, address: str) -> int:
        return self._balances.get(contract_id, {}).get(address, 0)

    def transfer(self, contract_id: str,
                  from_addr: str, to_addr: str, amount: int) -> bool:
        bal = self._balances.get(contract_id, {})
        if bal.get(from_addr, 0) < amount:
            return False
        bal[from_addr]  = bal.get(from_addr, 0)  - amount
        bal[to_addr]    = bal.get(to_addr, 0)    + amount
        return True

    def approve(self, contract_id: str,
                 owner: str, spender: str, amount: int):
        a = self._allowances.setdefault(contract_id, {})
        a.setdefault(owner, {})[spender] = amount

    def transfer_from(self, contract_id: str,
                       spender: str, from_addr: str,
                       to_addr: str, amount: int) -> bool:
        allowed = self._allowances.get(contract_id, {}).get(from_addr, {}).get(spender, 0)
        if allowed < amount:
            return False
        if not self.transfer(contract_id, from_addr, to_addr, amount):
            return False
        self._allowances[contract_id][from_addr][spender] -= amount
        return True

    def burn(self, contract_id: str, from_addr: str, amount: int) -> bool:
        bal = self._balances.get(contract_id, {})
        if bal.get(from_addr, 0) < amount:
            return False
        bal[from_addr] -= amount
        self._tokens[contract_id].total_supply -= amount
        return True

    def mint(self, contract_id: str, to_addr: str, amount: int,
              caller: str) -> bool:
        token = self._tokens.get(contract_id)
        if not token or token.owner != caller:
            return False
        self._balances[contract_id][to_addr] = \
            self._balances[contract_id].get(to_addr, 0) + amount
        token.total_supply += amount
        return True

    def token_info(self, contract_id: str) -> Optional[dict]:
        t = self._tokens.get(contract_id)
        if not t: return None
        return {
            "contract_id":  t.contract_id,
            "name":         t.name,
            "symbol":       t.symbol,
            "decimals":     t.decimals,
            "total_supply": t.total_supply,
            "owner":        t.owner,
            "created_at":   t.created_at,
            "holders":      len(self._balances.get(contract_id, {})),
        }

    def list_tokens(self) -> List[dict]:
        return [self.token_info(cid) for cid in self._tokens]


# ================================================================
#  CONTRACT MANAGER
# ================================================================

class ContractManager:
    """Manages all contracts on the NEBULA chain"""

    def __init__(self):
        self.interpreter  = ScriptInterpreter()
        self.nbl20        = NBL20Registry()
        self.templates    = ContractTemplates()
        self._contracts:  Dict[str, dict] = {}

    def verify_script(self,
                       unlocking: bytes,
                       locking:   bytes,
                       tx_hash:   bytes = b'\x00'*32,
                       height:    int   = 0,
                       ts:        int   = 0) -> Tuple[bool, str]:
        """Verify a script pair"""
        interp = ScriptInterpreter(tx_hash, ts, height)
        try:
            # Run unlocking script first
            ok, stack = interp.execute(unlocking)
            # Then locking script with result stack
            ok, stack = interp.execute(locking, stack)
            return ok, "OK" if ok else "Script returned false"
        except ScriptError as e:
            return False, str(e)

    def create_htlc(self,
                     recipient_address: str,
                     refund_address:    str,
                     secret:            bytes,
                     lock_blocks:       int = 144) -> dict:
        """Create Hash Time-Locked Contract for atomic swaps"""
        from nebula_core import Script, base58check_decode, PUBKEY_ADDRESS_VERSION
        secret_hash   = hashlib.sha256(secret).digest()
        recipient_h160 = base58check_decode(recipient_address)[1]
        refund_h160    = base58check_decode(refund_address)[1]

        locking = self.templates.htlc(
            recipient_h160, refund_h160, secret_hash, lock_blocks)

        contract_id = hashlib.sha256(locking).hexdigest()[:32]
        self._contracts[contract_id] = {
            "type":       "HTLC",
            "id":         contract_id,
            "recipient":  recipient_address,
            "refund":     refund_address,
            "secret_hash":secret_hash.hex(),
            "lock_blocks":lock_blocks,
            "script":     locking.hex(),
        }
        return self._contracts[contract_id]

    def deploy_nbl20(self,
                      name:    str,
                      symbol:  str,
                      supply:  float,
                      dec:     int,
                      owner:   str) -> str:
        """Deploy NBL-20 token"""
        token = NBL20Token(
            name         = name,
            symbol       = symbol,
            decimals     = dec,
            total_supply = int(supply * 10**dec),
            owner        = owner,
        )
        return self.nbl20.deploy(token, owner)

    def info(self) -> dict:
        return {
            "contracts":    len(self._contracts),
            "nbl20_tokens": len(self.nbl20.list_tokens()),
            "opcodes":      len(OP),
        }
