#!/usr/bin/env python3

import re
import hashlib
import verystable.core.key
import verystable.core.messages
import verystable.core.script

class Allocator:
    """simple object to monitor how much space is used up by
       currently allocated objects"""
    def __init__(self):
        self.x = 0
        self.max = 0
        #self.alloced = set()
        self.limit = 500000

    def over_limit(self):
        return self.max > self.limit

    def alloc(self, n, w):
        assert n >= 0
        self.x += n
        if self.x > self.max:
            self.max = self.x
        #self.alloced.add(w)

    def realloc(self, old, new, w):
        #assert w in self.alloced
        self.x += (new - old)
        if self.x > self.max:
            self.max = self.x

    def free(self, n, w):
        assert n >= 0
        self.x -= n
        #self.alloced.remove(w)

ALLOCATOR = Allocator()

# kinds
ATOM=255
CONS=254
REF=253
ERROR=252

class Element:
    re_printable = re.compile(b"^[a-z]+$")
    _nil = None
    _one = None

    def __init__(self, kind, val1, val2=None):
        ALLOCATOR.alloc(24, self)
        assert 0 <= kind and kind < 256
        self.kind = kind
        self._refs = 1
        self.val1 = val1
        self.val2 = val2
        if kind == ATOM:
            assert (isinstance(val1, int) and 0 <= val2 <= 8) or (isinstance(val1, bytes) and val2 > 8)

    def bumpref(self):
        self._refs += 1
        return self

    @classmethod
    def Nil(cls):
        if cls._nil is None:
            cls._nil = cls(ATOM, 0, 0)
            cls._nil.bumpref()
        return cls._nil.bumpref()

    @classmethod
    def One(cls):
        if cls._one is None:
            cls._one = cls(ATOM, 1, 1)
            cls._one.bumpref()
        return cls._one.bumpref()

    @classmethod
    def Atom(cls, data, length=None):
        if length is not None:
            assert isinstance(data, int) and data > 0 and data <= 0xFFFF_FFFF_FFFF_FFFF
            assert length >= (data.bit_length() + 7) // 8
            assert length <= 8
            if length == 0: return cls.Nil()
            if length == 1 and data == 1: return cls.One()
            return cls(ATOM, data, length)
        if data == False or data == 0 or data is None or data == '' or data == b'':
            return cls.Nil()
        if data == True or data == 1 or data == '\x01' or data == b'\x01':
            return cls.One()

        if isinstance(data, str):
            data = data.encode('utf8')
        elif isinstance(data, int):
            assert data > 0 and data <= 0xFFFF_FFFF_FFFF_FFFF
            bl = (data.bit_length() + 7)//8
            return cls(ATOM, data, bl)
        assert isinstance(data, bytes)
        if len(data) <= 8:
            i = int.from_bytes(data, byteorder='little', signed=False)
            return cls(ATOM, i, len(data)) # in place
        else:
            ALLOCATOR.alloc(len(data), data) # pointer
            return cls(ATOM, data, len(data))

    @classmethod
    def Cons(cls, left, right):
        return cls(CONS, left, right)

    @classmethod
    def Ref(cls, ref):
        return cls(REF, ref)

    @classmethod
    def Error(cls, msg):
        return cls(ERROR, msg)

    def dupe_atom(self):
        assert self.kind == ATOM
        v = self.val1
        if isinstance(v, bytes):
            v = v[:] # copy
        else:
            assert isinstance(v, int) # don't need to copy
        replace = Element(ATOM, v, self.val2)
        self.deref()
        return replace

    @classmethod
    def toderef(cls, stk, *els):
        for el in els:
            if el._refs > 1:
                el._refs -= 1
            else:
                stk.append(el)

    def deref(self):
        s = [self]
        # XXX should consider having this be a cons to keep
        # constant memory usage?
        while s:
            f = s.pop()
            assert f._refs >= 1, f"double-free of {f}"
            f._refs -= 1
            if f._refs == 0:
                if f.kind == ATOM:
                    if f.val2 > 8: ALLOCATOR.free(f.val2, f.val1)
                elif f.kind == CONS:
                    if f.val2.kind == ATOM:
                        self.toderef(s, f.val1, f.val2)
                    else:
                        self.toderef(s, f.val2, f.val1)
                else: # REF, ERROR, FN
                     self.toderef(s, f.val1)
                     assert not isinstance(f.val2, Element)
                ALLOCATOR.free(24, f)

    def is_nil(self):
        return self.kind == ATOM and self.val1 == 0 and self.val2 == 0

    def is_atom(self):
        return self.kind == ATOM

    def is_cons(self):
        return self.kind == CONS

    def atom_as_bytes(self):
        assert self.kind == ATOM
        if self.val2 <= 8:
            return self.val1.to_bytes(self.val2, byteorder='little', signed=False)
        else:
            return self.val1

    def atom_as_u64(self):
        assert self.kind == ATOM
        if self.val2 <= 8:
            assert isinstance(self.val1, int) and 0 <= self.val1 <= 0xFFFF_FFFF_FFFF_FFFF
            return self.val1
        else:
            return int.from_bytes(self.val1[:8], byteorder='little', signed=False)

    def __str__(self):
        if self.is_nil():
            return "nil"
        elif self.is_atom():
            if self.val2 == 0 or (self.val1 != 0 and self.val2 == 1):
                return str(self.val1)
            else:
                v = self.atom_as_bytes()
                if self.re_printable.match(v):
                    return '"%s"' % (v.decode('utf8'),)
                else:
                    return "0x%s" % (v.hex(),)
        elif self.is_cons():
            x = []
            while self.val2.is_cons():
                x.append(self.val1)
                self = self.val2
            x.append(self.val1)
            if not self.val2.is_nil():
                x.append(".")
                x.append(self.val2)
            return "(%s)" % " ".join(map(str, x))
        elif self.is_ref():
            return "REF(%s)" % (str(self.val1))
        elif self.is_error():
            return "ERR(%s)" % (str(self.val1))
        else:
            return "FN(%d,%s)" % (str(self.val1))

class Tree:
    def __init__(self):
        self.tree = []

    def add(self, element):
        i = 0
        while i < len(self.tree):
            if self.tree[i] is None:
                self.tree[i] = element
                return
            element = Element.Cons(self.tree[i], element)
            self.tree[i] = None
            i += 1
        self.tree.append(element)

    def resolve(self):
        x = None
        for el in self.tree:
            if el is None: continue
            if x is None:
                x = el
            else:
                x = Element.Cons(el, x)
        return x

class Operator:
    state = 0
    def __init__(self):
        # do any special setup
        pass

    def argument(self, el):
        # handle an argument
        raise Exception("BUG: argument handling unimplemented")

    def finish(self):
        # return the result
        raise Exception("BUG: finish unimplemented")

class op_a(Operator):
    # if given multiple arguments, builds them up into a tree,
    # biased to the left
    def __init__(self):
        self.tree = Tree()
    def argument(self, el):
        if self.state == 0:
            self.i = el
            self.env = None
            self.state = 1
        else:
            self.tree.add(el)
    def finish(self):
        if self.state == 0:
            raise Exception("a: requires at least one argument")
        env = self.tree.resolve()
        return [env, self.i]

class op_x(Operator):
    def __init__(self):
        self.x = []
    def argument(self, el):
        self.x.append(repr(i))
        el.deref()
    def finish(self):
        raise Exception(" ".join(self.x))

class op_i(Operator):
    def argument(self, el):
        if self.state == 0:
            self.then = not el.is_nil()
            el.deref()
        elif self.state == 1:
            if self.then:
                self.result = el
            else:
                self.result = Element.Atom(0)
                el.deref()
        elif self.state == 2:
            if not self.then:
                self.result.deref()
                self.result = el
            else:
                el.deref()
        else:
            raise Exception("i: too many arguments")
        self.state += 1
    def finish(self):
        if self.state == 0:
            raise Exception("i: must provide condition argument")
        if self.state == 1:
            raise Exception("i: must provide then argument")
        return self.result

class op_softfork(Operator):
    def argument(self, el):
        el.deref()
    def finish(self):
        return Element.Atom(True)

class op_h(Operator):
    def argument(self, el):
        if self.state > 0:
            raise Exception("h: too many arguments")
        if el.is_atom():
            raise Exception("h: received non-list argument %s" % (el,))
        self.r = el.val1.bumpref()
        el.deref()
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("h: must provide list argument")
        return self.r

class op_t(Operator):
    def argument(self, el):
        if self.state > 0:
            raise Exception("t: too many arguments")
        if el.is_atom():
            raise Exception("t: received non-list argument %s" % (el,))
        self.r = el.val2.bumpref()
        el.deref()
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("t: must provide list argument")
        return self.r

class op_l(Operator):
    def argument(self, el):
        if self.state > 0:
            raise Exception("l: too many arguments")
        self.r = el.is_cons()
        el.deref()
        self.state += 1

    def finish(self):
        if self.state == 0:
            raise Exception("l: must provide list argument")
        return Element.Atom(self.r)

class op_c(Operator):
    # (c head tail), (c h1 h2 h3 tail)
    # this may mean you often want to have "nil" as the last arg,
    # if you're constructing a list from scratch

    res = None
    last_cons = None

    def argument(self, el):
        if self.res is None:
            self.res = el
        elif self.last_cons is None:
            self.res = self.last_cons = Element.Cons(self.res, el)
        else:
            self.last_cons.val2 = Element.Cons(self.last_cons.val2, el)
            self.last_cons = self.last_cons.val2

    def finish(self):
        if self.res is None:
            return Element.Atom(0)
        return self.res

class op_nand(Operator):
    # aka are any false?
    def __init__(self):
        self.b = False
    def argument(self, el):
        if el.is_nil():
            self.b = True
        el.deref()
    def finish(self):
        return Element.Atom(self.b)

class op_and(Operator):
    # aka are all true?
    def __init__(self):
        self.b = True
    def argument(self, el):
        if el.is_nil():
            self.b = False
        el.deref()
    def finish(self):
        return Element.Atom(self.b)

class op_or(Operator):
    # aka are any true?
    def __init__(self):
        self.b = False
    def argument(self, el):
        if not el.is_nil():
            self.b = True
        el.deref()
    def finish(self):
        return Element.Atom(self.b)

class op_eq(Operator):
    def __init__(self):
        self.h = None
        self.ok = True
    def argument(self, el):
        if not self.ok:
            el.deref()
        else:
            if self.h is None:
                self.h = el
                return
            else:
                if not Element.check_equal([(self.h, el)]):
                    self.h.deref()
                    self.h, self.ok = None, False
                el.deref()
    def finish(self):
        if self.h is not None:
            self.h.deref()
        return Element.Atom(self.ok)

class op_strlen(Operator):
   def __init__(self):
       self.v = 0
   def argument(self, el):
        if not el.is_atom():
            raise Exception(f"len: not an atom: {el}")
        self.v += el.val2
        el.deref()
   def finish(self):
        return Element.Atom(self.v)

class op_cat(Operator):
    def __init__(self):
        self.build = None
    def argument(self, el):
        if not el.is_atom():
            raise Exception(f"cat: argument not an atom: {el}")
        if self.build is None:
            self.build = el
        else:
            if self.build._refs > 1:
                self.build = self.build.dupe_atom()

            new_size = self.build.val2 + el.val2
            if new_size <= 8:
                self.build.val1 += (el.val1 << (8*self.build.val2))
            else:
                if self.build.val2 <= 8:
                    self.build.val1 = self.build.atom_as_bytes()
                    ALLOCATOR.alloc(new_size, self.build.val1)
                else:
                    ALLOCATOR.realloc(self.build.val2, new_size, self.build.val1)
                self.build.val1 += el.atom_as_bytes()
            self.build.val2 = new_size
            el.deref()

    def finish(self):
        if self.build is None: return Element.Atom(0)
        return self.build

class op_substr(Operator):
    def __init__(self):
        self.el = None
        self.start = None
        self.end = None
    def argument(self, el):
        if self.el is None:
            if not el.is_atom():
                raise Exception("substr: must be atom")
            self.el = el
        elif self.start is None:
            self.start = el.atom_as_u64()
            el.deref()
        elif self.end is None:
            self.end = el.atom_as_u64()
            el.deref()
        else:
            raise Exception("substr: too many arguments")
    def finish(self):
        if self.el is None: return Element.Atom(0)
        if self.start is None: return self.el
        if self.start == 0:
            if self.end is None: return self.el
            if self.end >= self.el.val2: return self.el
        if self.end is None:
            self.end = self.el.val2
        if self.el.val2 <= 8:
            m = 0xFFFF_FFFF_FFFF_FFFF
            n = self.el.val1
            s = Element.Atom(((m^(m<<(self.end*8))) & n) >> (self.start*8), self.end-self.start)
        else:
            s = Element.Atom(self.el.val1[self.start:self.end])
        self.el.deref()
        return s

class op_add_u64(Operator):
    def __init__(self):
        self.i = 0

    def argument(self, el):
        self.i += el.atom_as_u64()
        self.i %= 0x1_0000_0000_0000_0000
        el.deref()

    def finish(self):
        return Element.Atom(self.i)

class op_mul_u64(Operator):
    def __init__(self):
        self.i = 1

    def argument(self, el):
        self.i *= el.atom_as_u64()
        self.i %= 0x1_0000_0000_0000_0000
        el.deref()

    def finish(self):
        return Element.Atom(self.i)

class op_sub_u64(Operator):
    def __init__(self):
        self.i = None

    def argument(self, el):
        n = el.atom_as_u64()
        el.deref()
        if self.i is None:
            self.i = n
        else:
            self.i -= n
            self.i %= 0x1_0000_0000_0000_0000

    def finish(self):
        if self.i is None:
            raise Exception("sub: missing arguments")
        return Element.Atom(self.i)

# op_mod / op_divmod
class op_div_u64(Operator):
    def __init__(self):
        self.i = None

    def argument(self, el):
        n = el.atom_as_u64()
        el.deref()
        if self.i is None:
            self.i = n
        else:
            ## if el >= 2**64 should we just set i to 0?
            if n == 0:
                raise Exception("div: attempted div by 0")
            self.i //= n

    def finish(self):
        if self.i is None:
            raise Exception("div: missing arguments")
        return Element.Atom(self.i)

class op_lt_u64(Operator):
    def __init__(self):
        self.i = -1

    def argument(self, el):
        k = el.atom_as_u64()
        if self.i is not None and self.i < k:
            self.i = k
        else:
            self.i = None
        el.deref()

    def finish(self):
        return Element.Atom(self.i is not None)

class op_sha256(Operator):
    def __init__(self):
        self.st = hashlib.sha256()

    def argument(self, el):
        if not el.is_atom():
            raise Exception("sha256: cannot hash list")
        self.st.update(el.atom_as_bytes())
        el.deref()

    def finish(self):
        return Element.Atom(self.st.digest())

class op_hash160(op_sha256):
    def finish(self):
        x = hashlib.new("ripemd160")
        x.update(self.st.digest())
        return Element.Atom(x.digest())

class op_hash256(op_sha256):
    def finish(self):
        x = hashlib.sha256()
        x.update(self.st.digest())
        return Element.Atom(x.digest())

class op_bip340_verify(Operator):
    def __init__(self):
        self.args = []

    def argument(self, el):
        if not el.is_atom():
            raise Exception("bip340_verify: argument must be atom")
        if len(self.args) < 3:
            self.args.append(el)
        else:
            raise Exception("bip340_verify: too many arguments")

    def finish(self):
        if len(self.args) != 3:
            raise Exception("bip340_verify: too few arguments")
        pk, m, sig = self.args
        if pk.val2 != 32 or m.val2 != 32 or sig.val2 != 64:
            r = False
        else:
            r = verystable.core.key.verify_schnorr(key=pk.val1, sig=sig.val1, msg=m.val1)
        pk.deref()
        m.deref()
        sig.deref()
        return Element.Atom(r)

class op_bip342_txmsg:
    def __init__(self):
        self.sighash = None

    def argument(self, el):
        if self.sighash is not None:
            raise Exception("bip342_txmsg: too many arguments")
        if not el.is_atom() or el.val2 > 1:
            raise Exception("bip342_txmsg: expects a single sighash byte")
        if el.val2 == 1 and el.val1 not in [0x01, 0x02, 0x03, 0x81, 0x82, 0x83]:
            raise Exception("bip342_txmsg: unknown sighash byte")
        self.sighash = el.atom_as_u64()
        el.deref()

    def finish(self):
        if self.sighash is None: self.sighash = 0
        annex = None
        if len(GLOBAL_TX.wit.vtxinwit) > 0:
            w = GLOBAL_TX.wit.vtxinwit[GLOBAL_TX_INPUT_IDX].scriptWitness.stack
            if len(w) > 0 and w[-1][0] == 0x50:
                annex = w[-1]
        r = verystable.core.script.TaprootSignatureHash(txTo=GLOBAL_TX, spent_utxos=GLOBAL_UTXOS, hash_type=self.sighash, input_index=GLOBAL_TX_INPUT_IDX, scriptpath=True, annex=annex, script=GLOBAL_TX_SCRIPT)
        return Element.Atom(r)

class op_tx:
    def __init__(self):
        # build up r as we go, by updating last_cons
        self.r = None
        self.last_cons = None

    def argument(self, el):
        # el is either an atom giving info about the tx as a whole
        # or a pair of what info is requested, plus what input/output idx
        #  we want info about
        if el.is_atom():
            code = el.atom_as_u64()
            which = None
        elif el.is_cons():
            if not el.val1.is_atom() or not el.val2.is_atom():
                raise Exception("tx: expects atoms or pairs of atoms")
            code = el.val1.atom_as_u64()
            which = el.val2.atom_as_u64()
        el.deref()
        result = self.get_tx_info(code, which)
        if self.r is None:
            self.r = result
        elif self.last_cons is None:
            self.last_cons = Element.Cons(result, Element.Atom(0))
            self.r = Element.Cons(self.r, self.last_cons)
        else:
            assert self.last_cons.is_cons()
            assert self.last_cons.val2.is_atom()
            assert self.last_cons.val2.val2 == 0
            self.last_cons.val2 = Element.Cons(result, self.last_cons.val2)
            self.last_cons = self.last_cons.val2

    def get_tx_info(self, code, which):
        if 0 <= code <= 9:
            if which is not None: raise Exception(f"tx: {code} should be an atom not a pair")
            return self.get_tx_global_info(code)
        elif 10 <= code <= 19:
            if which is None: which = GLOBAL_TX_INPUT_IDX
            if which < 0 or which >= len(GLOBAL_TX.vin):
                raise Exception(f"tx: {code} invalid input index")
            return self.get_tx_input_info(code, which)
        elif 20 <= code <= 29:
            if which is None: which = GLOBAL_TX_INPUT_IDX
            if which < 0 or which >= len(GLOBAL_TX.vout):
                raise Exception(f"tx: {code} requires valid output index")
            return self.get_tx_output_info(code, which)
        else:
            raise Exception(f"tx: {code} out of range")

    def get_tx_global_info(self, code):
        if code == 0:
            return Element.Atom(GLOBAL_TX.nVersion, 4)
        elif code == 1:
            return Element.Atom(GLOBAL_TX.nLockTime, 4)
        elif code == 2:
            return Element.Atom(len(GLOBAL_TX.vin))
        elif code == 3:
            return Element.Atom(len(GLOBAL_TX.vout))
        elif code == 4:
            return Element.Atom(GLOBAL_TX_INPUT_IDX)
        elif code == 5:
            return Element.Atom(GLOBAL_TX.serialize_without_witness())
        elif code == 6:
            wit = GLOBAL_TX.wit.vtxinwit[GLOBAL_TX_INPUT_IDX].scriptWitness.stack
            n = len(wit) - 1
            if n >= 0 and wit[n][0] == 0x50: n -= 1 # skip annex
            if n >= 1 and len(wit[n]) > 0:
                v = (wit[n][0] & 0xFE)
                s = wit[n-1]
                h = verystable.core.key.TaggedHash("TapLeaf", bytes([v]) + verystable.core.messages.ser_string(s))
                return Element.Atom(h)
            else:
                return Element.Atom(0)

        elif code == 7:
            wit = GLOBAL_TX.wit.vtxinwit[GLOBAL_TX_INPUT_IDX].scriptWitness.stack
            if len(wit) > 0 and len(wit[-1]) > 0 and wit[-1][0] == 0x50:
                return Element.Atom(wit[-1])
            else:
                return Element.Atom(0)
        else:
            return Element.Atom(0)

    def get_tx_input_info(self, code, which):
        txin = GLOBAL_TX.vin[which]
        wit = GLOBAL_TX.wit.vtxinwit[which].scriptWitness.stack
        coin = GLOBAL_UTXOS[which]
        if code == 10:
             return Element.Atom(txin.nSequence, 4)
        elif code == 11:
             return Element.Atom(verystable.core.messages.ser_uint256(txin.prevout.hash))
        elif code == 12:
             return Element.Atom(txin.prevout.n, 4)
        elif code == 13:
             return Element.Atom(txin.scriptSig)
        elif code == 14:
             if len(wit) > 0 and len(wit[-1]) > 0 and wit[-1][0] == 0x50:
                 return Element.Atom(wit[-1])
             else:
                 return Element.Atom(0)
        elif code == 15:
             return Element.Atom(coin.nValue, 8)
        elif code == 16:
             return Element.Atom(coin.scriptPubKey)
        else:
             return Element.Atom(0)

    def get_tx_output_info(self, code, which):
        out = GLOBAL_TX.vout[which]
        if code == 20:
             return Element.Atom(out.nValue, 8)
        elif code == 21:
             return Element.Atom(out.scriptPubKey)
        else:
             return Element.Atom(0)

    def finish(self):
        if self.r is None: return Element.Atom(0)
        return self.r

FUNCS = [
  (b'', "q", None), # quoting indicator, special

  (0x01, "a", op_a),  # apply
  (0x02, "x", op_x),  # exception
  (0x03, "i", op_i),  # eager-evaluated if
  (0x04, "sf", op_softfork),

  (0x05, "c", op_c), # construct a list, last element is a list
  (0x06, "h", op_h), # head / car
  (0x07, "t", op_t), # tail / cdr
  (0x08, "l", op_l), # is cons?

  (0x09, "not", op_nand),
  (0x0a, "all", op_and),
  (0x0b, "any", op_or),

  (0x0c, "=", op_eq),
#  (0x0d, "<s", op_str_lt),
  (0x0e, "strlen", op_strlen),
  (0x0f, "substr", op_substr),
  (0x10, "cat", op_cat),

#  (0x11, "~",op_bit_not),
#  (0x12, "&", op_bit_and),
#  (0x13, "|", op_bit_or),
#  (0x14, "^", op_bit_xor),
#  (0x15, "b<<", op_bit_lshift),
#  (0x16, "b>>", op_bit_rshift),

  (0x17, "+", op_add_u64),
  (0x18, "-", op_sub_u64),
  (0x19, "*", op_mul_u64),
#  (0x1a, "%", op_mod_u64),
#  (0x1b, "/%", op_divmod_u64), # (/ a b) => (h (/% a b))
  (0x1c, "<", op_lt_u64),
#  (0x1d, "<<", op_lshift_u64),
#  (0x1e, ">>", op_rshift_u64),

#  (0x1f, "log2e42", op_log2e42_u64),
      ## allow both of these to apply to arbitrary atoms?
      ## (500kB atoms are in range for log, < is just little
      ##  endian with special handling for 0?)

#  (0x20, "rd_csn", op_csn_read),  # convert CScriptNum to atom
#  (0x21, "wr_csn", op_csn_write), # convert atom to CScriptNum
#  (0x22, "rd_list", op_list_read), # read bytes to Element
#  (0x23, "wr_list", op_list_write), # write Element as bytes

  (0x24, "sha256", op_sha256),
 # (0x25, "ripemd160", op_ripemd160),
  (0x26, "hash160", op_hash160),
  (0x27, "hash256", op_hash256),
  (0x28, "bip340_verify", op_bip340_verify),
#  (0x29, "ecdsa_verify", op_ecdsa_verify),
#  (0x2a, "secp256k1_muladd", op_secp256k1_muladd),

  (0x2b, "tx", op_tx),
  (0x2c, "bip342_txmsg", op_bip342_txmsg),
]

def _Do_FUNCS():
    se = {}
    op = {}
    for (val, name, fn) in FUNCS:
        assert name not in se
        assert val not in op
        se[name] = val
        op[val] = fn
    return se, op
SExpr_FUNCS, Op_FUNCS = _Do_FUNCS()

class SExpr:
    re_parse = re.compile("(?P<ws>\s+)|(?P<open>[(])|(?P<close>[)])|(?P<dot>[.])|(?P<tick>['])|(?P<atom>[^'()\s.]+)")
    re_int = re.compile("^-?\d+$")
    re_hex = re.compile("^0x[0-9a-fA-F]+$")
    re_quote = re.compile('^"[^"]*"$')

    @staticmethod
    def list_to_element(l):
        if len(l) >= 3 and l[-2] is None:
            t = l[-1]
            l = l[:-2]
        else:
            t = Element.Atom(0)
        assert None not in l
        for h in reversed(l):
            t = Element.Cons(h, t)
        return t

    @classmethod
    def get_token(cls, s):
        m = cls.re_parse.match(s)
        if m is None:
            raise Exception("failed to parse at \"%s\"" % (s,))
        return s[m.end():], m

    @classmethod
    def parse(cls, s, many=False):
        where = 0
        end = len(s)
        parstack = [[]]

        while s != "":
            s, m = cls.get_token(s)

            g = m.groupdict()
            if g["ws"]:
                pass
            elif g["open"]:
                parstack.append([])
            elif g["close"]:
                if len(parstack) <= 1 or (parstack[-1] and parstack[-1][-1] is None) or (parstack[-1] and parstack[-1][0] == "tick"):
                    raise Exception("unexpected )")
                q = parstack.pop()
                parstack[-1].append(cls.list_to_element(q))
            elif g["dot"]:
                if len(parstack[-1]) == 0:
                    raise Exception("must have one or more elements before . in list")
                parstack[-1].append(None)
            elif g["tick"]:
                parstack.append(["tick"])
            elif g["atom"]:
                a = g["atom"]
                if a in SExpr_FUNCS:
                    a = SExpr_FUNCS[a]
                elif a == "nil":
                    a = 0
                elif cls.re_hex.match(a):
                    a = bytes.fromhex(a[2:])
                elif cls.re_int.match(a):
                    a = int(a, 10)
                elif cls.re_quote.match(a):
                    a = a[1:-1]
                else:
                    raise Exception("unparsable/unknown atom %r" % (a,))
                if a == b'' or a == 0:
                    parstack[-1].append(Element.Atom(0))
                else:
                    parstack[-1].append(Element.Atom(a))
            else:
                raise Exception("BUG: unhandled match")

            while len(parstack[-1]) > 1 and parstack[-1][0] == "tick":
                assert len(parstack[-1]) == 2
                q = parstack.pop()
                parstack[-1].append(Element.Cons(Element.Atom(0), q[1]))

            if len(parstack[-1]) > 3 and parstack[-1][-3] is None:
                raise Exception("cannot have multiple elements after . in list")

        if parstack and parstack[-1] and parstack[-1][0] == "tick":
            raise Exception("tick without following element")

        if len(parstack) > 1:
            raise Exception("missing )")

        if not many:
            if len(parstack[0]) > 1:
                raise Exception("multiple unbracketed entries")
            return parstack[0][0]

        else:
            return cls.list_to_element(parstack[0])

def steal_list(l):
    assert isinstance(l, Element) and l.is_cons()
    h, t = l.val1.bumpref(), l.val2.bumpref()
    l.deref()
    return h, t

def get_env(n, env):
    if n < 0:
        raise Exception("env argument out of range: %s" % (n,))
    while n > 1:
        if not env.is_cons():
            raise Exception("invalid env path %d" % (n,))
        n, x = divmod(n, 2)
        env = env.val2 if x else env.val1
    return env

def eval(baseenv, inst, debug):
   assert isinstance(baseenv, Element)
   assert isinstance(inst, Element)

   work = [(0, baseenv.bumpref(), None, inst.bumpref())] # stage, env, generator, remaining args to evaluate

   if debug:
       print(f'ENV={baseenv}')
       print(f'GOAL={inst}')

   while work:
       if ALLOCATOR.over_limit():
           raise Exception("used too much memory")

       (what, env, gen, args) = work.pop()

       if debug:
           if env is baseenv:
               print(f'  depth={len(work)} ENV {gen} {args}')
           else:
               print(f'  depth={len(work)} <{env}> {gen} {args}')
           for xd, (xw, xe, xg, xa) in enumerate(work):
               if xe is baseenv: xe = "ENV"
               print(f' &depth={xd} <{xe}> {xg} {xa}')

       assert isinstance(args, Element)
       result = None

       if args.is_nil():
           if gen is None:
               result = args.bumpref()
           else:
               result = gen.finish()
               assert result is not None
       elif args.is_atom():
           if gen is None:
               n = args.atom_as_u64()
               result = get_env(n, env).bumpref()
           else:
               raise Exception("args terminated with non-nil atom")
       else:
           arg, args = steal_list(args)

           if gen is None:
               if arg.is_cons():
                   work.append( (what, env, gen, args) )
                   work.append( (1, env.bumpref(), None, arg) )
               else:
                   opcode = arg.atom_as_u64()
                   huh = arg.val1,arg.val2
                   arg.deref()
                   if opcode == 0:
                       # nil / q
                       result = args.bumpref()
                       assert result is not None
                   else:
                       o = Op_FUNCS.get(opcode, None)
                       if o is None:
                           raise Exception("unknown operator: %x %s" % (opcode,huh))
                       if debug: print("DOING OP %s" % (o.__name__))
                       gen = o()
                       work.append( (what, env, gen, args) )
           else:
               if arg.is_atom():
                   if arg.is_nil():
                       gen.argument(arg)
                   else:
                       n = arg.atom_as_u64()
                       arg.deref()
                       gen.argument(get_env(n, env).bumpref())
                   work.append( (what, env, gen, args) )
               else:
                   work.append( (what, env, gen, args) )
                   work.append( (2, env.bumpref(), None, arg) )

       if result is None: continue

       # tail call (a)
       if not isinstance(result, list):
           if debug: print(f'  fin --> {result}')
       else:
           if debug: print(f'  fin --> {" // ".join(map(str,result))}')
           if result[0] is not None:
               env.deref()
               env, args = result
           else:
               args = result[1]
           work.append( (what, env, None, args) )
           continue

       assert isinstance(result, Element)
       env.deref()
       args.deref()

       if what == 0:
           # finish!
           assert len(work) == 0
           return result

       assert len(work) > 0
       if debug: print(f"RES {what} {result} {gen}")
       if what == 1:
           # recursion to decide instruction
           if result.is_cons():
               raise Exception("non-atomic instruction after evaluation: %s" % (result,))
           (_w, _e, _g, _a) = work.pop()
           assert _g is None
           work.append( (_w, _e, _g, Element.Cons(result, _a)) )
           continue
       elif what == 2:
           # recursion to resolve argument
           assert work[-1][2] is not None
           work[-1][2].argument(result)
           continue

       assert False, "BUG: unreachable"
   assert False, "BUG: unreachable"

class Rep:
    def __init__(self, env, debug=False):
        self.env = env
        self.debug = debug

    def __call__(self, program, debug=None):
        if debug is None: debug = self.debug
        if debug: print("PROGRAM: %s" % (program,))
        ALLOCATOR.max = 0
        init_x = ALLOCATOR.x
        #before_x = set(ALLOCATOR.alloced)
        p = SExpr.parse(program, many=False)
        try:
            r = eval(self.env, p, debug=debug)
            print("MAX=%s ; %s -> %s" % (ALLOCATOR.max, program, r))
            r.deref()
        except:
            print("%s -> FAILED" % (program,))
            raise
            ## need some proper way of freeing memory so that REPL can
            ## continue after a failure. difficult because we don't want
            ## to free the original environment, but do want to free
            ## everything else
            ##
            ## perhaps should restructure to set a flag in ALLOCATOR
            ## or similar for normal execution failures, and only raise
            ## for BUG scenarios? need to count "execution load" somewhere
            ## as well
        p.deref()
        #if ALLOCATOR.x != init_x:
        #    print("=======================")
        #    for el in ALLOCATOR.alloced:
        #        if el not in before_x:
        #            print(el._refs, el)
        #    print("=======================")
        assert ALLOCATOR.x == init_x, "memory leak: %d -> %d (%d)" % (init_x, ALLOCATOR.x, ALLOCATOR.x - init_x)

nil = Element.Atom(0)
one = Element.Atom(1)

rep = Rep(SExpr.parse("((55 . 33) . (22 . 8))"))
print("Env: %s" % (rep.env))

rep("1")
rep("(q . 1)")
rep("(q . q)")
rep("'1")
rep("'(1)")
rep("'\"q\"")
rep("(+ '2 '2 . 0)")
rep("(+ (q . 2) '2)")
rep("(a '(+ '2 '2))")
rep("(h '(4 5 6))")
rep("(t '(4 5 6))")
rep("(+ 7 '3)")
rep("(a '(+ 7 '3))")
rep("(a '(+ 7 '3) 1)")
rep("(a '(+ 7 '3) '((1 . 2) . (3 . 4)))")
rep("(c 1 ())")
rep("(c 4 ())")
rep("(c 4 6 5 7 nil)")
#rep("(- '77 (* '3 (/ '77 '3)))")
rep("(c '1 '2 '3 '4 (c '5 '(6 7)))")
rep("(a '(+ 7 '3) (c '(1 . 2) 3))")
rep("(c '2 '2)")
rep("(c '2 (sf . '(1 2 3 4 5)))")
rep("(c (l ()) (l '1) (l '(1 2 3)) ())")
rep("(all '1 '2 '3 '4)")
rep("(not '1 '2 '3 '4)")
rep("(all '1 '2 '0 '4)")
rep("(not '1 '2 '0 '4)")
rep("(any '0 '0 '5 '0)")
rep("(< '1 '2 '3 '4 '5)")
rep("(< '1 '2 '4 '4 '5)")
rep("(<)")
rep("(< '1)")
rep("(< '1 '2)")
rep("(< '2 '1)")

# factorial
# n=2, fn=3
# `if 2 (a 3 (- 2 '1) 3)
rep = Rep(SExpr.parse("(a (i 2 '(* 2 (a 3 (- 2 '1) 3)) ''1))"))
rep("(a 1 '150 1)")
#rep("(a 1 (c '15000 1))")

# factorial but efficient
rep = Rep(SExpr.parse("(a (i 2 '(a 7 (c (- 2 '1) (* 5 2) 7)) '(c 5)))"))
rep("(a 1 (c '150 '1 1))")
#rep("(a 1 (c '15000 '1 1))")

# sum factorial (+ 1! 2! 3! 4! ... n!)
# (proxy for (sha256 1! 2! .. n!)
# f 1 1 n
# f a! a b = 
# 4=fn 6=(a-1)! 5=a 7=left!

rep = Rep(SExpr.parse("(a (i 7 '(c (c nil 6) (a 4 4 (* 6 5) (+ 5 '1) (- 7 '1))) '(c nil)))"))
#rep("(a 1 1 '1 '1 '10)")
rep("(c '+ (a 1 1 '1 '1 '10))")
rep("(a (c '+ (a 1 1 '1 '1 '10)))")

# fibonacci


# 0 1 1 2 3 5 ...
# 0 1 2 3 4 5

# fib n = fib n 0 1
# fib 0 a b = a; fib n a b = fib (n-1) b (a+b)
# env = (n a b FIB) ; n=2, a=5, b=11, FIB=15

rep = Rep(SExpr.parse("(a (i 2 '(a 15 (c (- 2 '1) 11 (+ 5 11) 15)) '(c 5)))"))
rep("(a 1 (c '300 '0 '1 1))")

rep = Rep(SExpr.parse("(a (i 4 '(a 7 (- 4 '1) 5 (+ 6 5) 7) '(c 6)))"))
rep("(a 1 '300 '0 '1 1)")

rep = Rep(SExpr.parse("0x0200000015a20d97f5a65e130e08f2b254f97f65b96173a7057aef0da203000000000000887e309c02ebdddbd0f3faff78f868d61b1c4cff2a25e5b3c9d90ff501818fa0e7965d508bdb051a40d8d8f7"))
rep("(sha256 (sha256 1))")
rep("(hash256 1)")


bip340_tests = [
"F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9,0000000000000000000000000000000000000000000000000000000000000000,E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0,TRUE",
"DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659,243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89,6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE33418906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A,TRUE",
"DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8,7E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C,5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1BAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7,TRUE",
"25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517,FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3,TRUE",
"D69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9,4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703,00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C6376AFB1548AF603B3EB45C9F8207DEE1060CB71C04E80F593060B07D28308D7F4,TRUE",
"EEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34,243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89,6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B,FALSE",
"DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659,243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89,FFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A14602975563CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2,FALSE",
]
for x in bip340_tests:
    key, msg, sig, result = x.split(",")
    result = 1 if result == "TRUE" else 0
    rep(f"(c (bip340_verify '0x{key} '0x{msg} '0x{sig}) '{result} nil)")

GLOBAL_TX = verystable.core.messages.tx_from_hex("f0ccee2a000101ebf2f9fc896e70145c84116fae33d0242f8c146e1a07deecd9a98d9cc03f4fb70d000000002badf3fb01126b8c01000000001976a914551b850385def11149727e72c4470ffaeae5cdf288ac04402c797661dfac511e35f42601edd355e9cffb6ce47beddd9a9bf0914992c002af34c67933f89da981149f6044448f14ec7931f3641da82fac3aa9512d052e3b712220256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963fac21c0cdb18e708d5164ecbd681797623cb8f9be34dd1765ef0b63788d18ca4db18478025073ee1a6e46")
GLOBAL_TX_INPUT_IDX = 0
GLOBAL_TX_SCRIPT = bytes.fromhex("20256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963fac")
GLOBAL_UTXOS = [
    verystable.core.messages.from_hex(verystable.core.messages.CTxOut(), "1fc6d101000000002251203240405372856fe921522eca27514e2669f0aa4c46d52c78cfe608174828f937")
]

rep("(bip342_txmsg)")
rep("(bip340_verify '0x256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963f (bip342_txmsg) '0x2c797661dfac511e35f42601edd355e9cffb6ce47beddd9a9bf0914992c002af34c67933f89da981149f6044448f14ec7931f3641da82fac3aa9512d052e3b71)")

rep("(tx '0 '1 '2 '3 '4)")
rep("(tx '10 '11 '12 '13 '14 '15 '16)")
rep("(tx '(10 . 0) '(11 . 0) '(12 . 0) '(13 . 0) '(14 . 0) '(15 . 0) '(16 . 0))")
rep("(tx '(20 . 0) '(21 . 0))")
rep("(- (tx '15) (tx '(20 . 0)))")

rep("(hash256 (tx '5))")

rep("(a '1 '1 '2 '3 '4 '5)")
rep("(a '1 '1 '2 '3 '4 '5 '6 '7 '8 '9 '10)")

# acc fn 0 n nil -> acc fn 1 (- n 1) (cat nil (fn 0))
#  8  12 10 14 3
rep = Rep(SExpr.parse("(a (i 14 '(a 8 8 12 (+ 10 '1) (- 14 '1) (cat 3 (a 12 10))) '3))"))
rep("(bip342_txmsg)")

# implement sighash_all, codesep_pos=-1, len(scriptPubKey) < 253
rep("(a '(sha256 4 4 '0x00 6 3) (sha256 '\"TapSighash\") (cat '0x00 (tx '0) (tx '1) (sha256 (a 1 1 '(cat (tx (c '11 1)) (tx (c '12 1))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '15 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(a '(cat (strlen 1) 1) (tx (c '16 '0))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '10 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(cat (tx (c '20 1)) (a '(cat (strlen 1) 1) (tx (c '21 1)))) '0 (tx '3) 'nil)) (i (tx '7) '0x03 '0x01) (substr (cat (tx '4) '0x00000000) 'nil '4) (i (tx '7) (sha256 (a '(cat (strlen 1) 1) (tx '7))) 'nil)) (cat (tx '6) '0x00 '0xffffffff))")

print("----")
for a in [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,20,21]:
    rep("(tx '%d)" % (a,))

rep("(cat '0x1122 '0x3344)")


# levels:
#   bytes/hex
#   (c (q . 1) (q . 0xCAFEBABE) (q . "hello, world") (q . nil))
#   \' and aliases? (car,head = h, etc)
#   symbols; let/defun (compile to env access)
#   \` and \,  (quote and unquote / macros)

# notation?
#   'foo  = (q . foo)
#   '(a b c) = (q a b c)
#   `(a ,b c) = (c (q . a) b (q . c) nil)
#
# would be nice to have a "compiler" that can deal with a symbol table
# (for named ops).
