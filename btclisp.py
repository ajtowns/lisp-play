#!/usr/bin/env python3

import time

import verystable.core.messages

from element import Element, SExpr, ALLOCATOR, ATOM, CONS, ERROR, FUNC, REF, SYMBOL, SerDeser, nil, one
from funcs import  Op_FUNCS, SExpr_FUNCS, Set_GLOBAL_TX, Set_GLOBAL_TX_INPUT_IDX, Set_GLOBAL_TX_SCRIPT, Set_GLOBAL_UTXOS, Tree, fn_eval, get_env

class Compiler:
    @classmethod
    def demacro_module(cls, e):
        symtable = {}
        l = e.cons_to_pylist()
        if l is None:
            return Element.Error(f"argument to module not a list")
        for e in l:
            dfn = e.cons_to_pylist()
            if not dfn or dfn[0].kind != SYMBOL or dfn[0].val1 != "define" or len(dfn) != 3:
                return Element.Error(f"invalid module entry {e}")
            name = dfn[1].cons_to_pylist()
            if not name or name[0].kind != SYMBOL:
                return Element.Error(f"invalid module entry {e}")
            if name[0].val1 in symtable:
                return Element.Error(f"duplicate symbol {name[0]}")
            if name[0].val1 in SExpr_FUNCS:
                return Element.Error(f"define {name[0]} duplicates opcode")
            args = []
            for a in name[1:]:
                if a.kind != SYMBOL:
                    return Element.Error(f"define arg name must be symbol, not {a}")
                if a.val1 in SExpr_FUNCS:
                    return Element.Error(f"argument {a} duplicates opcode")
                args.append(a.val1)
            symtable[name[0].val1] = (args, dfn[2])
        names = symtable.keys()
        if "main" not in names:
            return Element.Error("no main function in module")
        defs = list(symtable.keys())
        envpos = {a: b for a,b in zip(defs, Tree.get_values_pair(len(symtable), 1)[0])}
        defcons = Element.Atom(0)
        for d in reversed(defs):
            argpos = {a: b for a,b in zip(symtable[d][0], Tree.get_values_pair(1, len(symtable[d][0]))[1])}
            argpos.update(envpos)
            defcons = Element.Cons(
                cls.demacro(symtable[d][1], argpos),
                defcons)

        # (a (a <main>) (b ...) 1)
        return Element.Cons(Element.Atom(SExpr_FUNCS['a']),
               Element.Cons(
                   Element.Cons(Element.Atom(SExpr_FUNCS['q']),
                   Element.Cons(Element.Atom(SExpr_FUNCS['a']),
                   Element.Cons(Element.Atom(envpos["main"]),
                   Element.Atom(0)))),
               Element.Cons(
                   Element.Cons(Element.Atom(SExpr_FUNCS['b']),
                   Element.Cons(
                      Element.Cons(Element.Atom(SExpr_FUNCS['q']), defcons),
                   Element.Atom(0))),
               Element.Cons(Element.Atom(1),
               Element.Atom(0)))))

    @classmethod
    def demacro_c_list(cls, e, extrasyms=None):
        orig = e
        if e.kind == ATOM: return e
        # (x y z) -> (c x y z nil)
        els = []
        while e.kind == CONS:
            els.append( cls.demacro(e.val1, extrasyms, midlist=True) )
            e = e.val2
        if not e.is_nil():
            return Element.Error("arg list {orig} not nil terminated")
        cons = Element.Cons(e, Element.Atom(0))
        for e in reversed(els):
            cons = Element.Cons(e, cons)
        cons = Element.Cons(Element.Atom(SExpr_FUNCS['c']), cons)
        return cons

    @classmethod
    def demacro(cls, e, extrasyms=None, midlist=False):
        if e.kind == ATOM: return e
        if e.kind == CONS:
            if e.val1.kind == SYMBOL and not midlist:
                if e.val1.val1 == "module":
                    return cls.demacro_module(e.val2)
                if extrasyms and e.val1.val1 in extrasyms:
                    # (foo bar baz) -> (a ENV 2 (b bar baz))
                    return Element.Cons(Element.Atom(SExpr_FUNCS['a']),
                           Element.Cons(Element.Atom(extrasyms[e.val1.val1]),
                           Element.Cons(Element.Atom(2),
                           Element.Cons(
                               Element.Cons(Element.Atom(SExpr_FUNCS['b']),
                               Element.Cons(
                                 cls.demacro_c_list(e.val2, extrasyms),
                               Element.Atom(0))),
                           Element.Atom(0)))))
            l = cls.demacro(e.val1, extrasyms, midlist=False)
            r = cls.demacro(e.val2, extrasyms, midlist=True)
            return Element.Cons(l, r)
        if e.kind == SYMBOL:
            if e.val1 in SExpr_FUNCS:
                return Element.Atom(SExpr_FUNCS[e.val1])
            if extrasyms and e.val1 in extrasyms:
                return Element.Atom(extrasyms[e.val1])
            return Element.Error(f"undefined symbol {e.val1} {extrasyms}")
        return Element.error(f"unexpected element {e}")

    @classmethod
    def compile(cls, sexpr):
        e = SExpr.parse(sexpr, many=False)
        return cls.demacro(e)

def steal_list(l):
    assert isinstance(l, Element) and l.is_cons()
    h, t = l.val1.bumpref(), l.val2.bumpref()
    l.deref()
    return h, t

def eager_eval(baseenv, inst, debug):
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


def lazy_eval(env, sexpr, debug):
    result = Element.Func(Element.Cons(sexpr.bumpref(), env.bumpref()), fn_eval())
    stack = [(True, result)]
    error = None
    while stack:
        assert error is None
        ALLOCATOR.record_work(1)
        if ALLOCATOR.over_limit(): break
        dfs, work = stack.pop()
        if debug: print(f"{len(stack)}/{0+dfs}:{ALLOCATOR.effort}: {work}")
        if debug: print(f"r: {result}")
        if work.kind == REF:
            if work.val1.kind == REF:
                work.replace(REF, work.val1.val1.bumpref())
                stack.append((dfs, work))
                continue
            else:
                work = work.val1
                # pass through
        if work.kind == ERROR:
            # early exit
            error = work.bumpref()
            break
        if work.kind == SYMBOL:
            error = Element.Error(f"unresolved symbol {work}")
            break
        if work.kind == ATOM: continue
        if work.kind == CONS:
            if work.val1.kind == ERROR:
                stack.append((dfs, work.val1))
            elif work.val2.kind == ERROR:
                stack.append((dfs, work.val2))
            elif dfs:
                if work.val2.kind != ATOM: stack.append((dfs, work.val2))
                if work.val1.kind != ATOM: stack.append((dfs, work.val1))
            continue
        assert work.kind == FUNC
        stack.append((dfs, work))
        x = work.val2.resolve(work)
        if ALLOCATOR.over_limit(): break
        if x is not None:
            assert isinstance(x, Element), f"non-none,non-element {x} {work.val2}"
            stack.append((False, x))

    if ALLOCATOR.over_limit():
        assert error is None
        #result.bumpref()
        error = Element.Error("exceeded execution limits")
    if error is not None:
        result.deref()
        result = error
    return result

class Rep:
    def __init__(self, env, debug=False, lazy=True):
        self.env = env
        self.debug = debug
        self.lazy = lazy
        eser = SerDeser().Serialize(self.env)
        edeser = SerDeser().Deserialize(eser)
        print(f"ENVSER: {eser.hex()}")
        assert str(edeser) == str(self.env)

    def __call__(self, program, debug=None):
        if debug is None: debug = self.debug
        if debug: print("PROGRAM: %s" % (program,))
        p = Compiler.compile(program)
        pser = SerDeser().Serialize(p)
        pdeser = SerDeser().Deserialize(pser)
        print("PROGHEX: %s" % (pser.hex()))
        print("DESER: %s" % (pdeser))
        assert str(pdeser) == str(p)
        ALLOCATOR.max = 0
        ALLOCATOR.reset_work()
        init_x = ALLOCATOR.x
        before_x = set(ALLOCATOR.allocated)
        try:
            t = time.time()
            if self.lazy:
                r = lazy_eval(self.env, p, debug=debug)
            else:
                r = eager_eval(self.env, p, debug=debug)
            elapsed = time.time() - t
            print("MAX=%s WORK=%s ELAPSED=%.1f ; %s -> %s" % (ALLOCATOR.max, ALLOCATOR.effort, elapsed, program, r))
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
        if ALLOCATOR.x != init_x:
            print("=======================")
            print("leaked:")
            for el,ln in ALLOCATOR.allocated.items():
                if el not in before_x:
                    print(el._refs, ln, el)
            print("=======================")
            print("pre-existing:")
            for el,ln in ALLOCATOR.allocated.items():
                if el in before_x:
                    print(el._refs, ln, el)
            print("=======================")
            print("missing:")
            for el in before_x:
                if el not in ALLOCATOR.allocated:
                    print("...", el)
            print("=======================")
        assert ALLOCATOR.x == init_x, "memory leak: %d -> %d (%d)" % (init_x, ALLOCATOR.x, ALLOCATOR.x - init_x)
        p.deref()

rep = Rep(Compiler.compile("((55 . 33) . (22 . 8))"))
print("\nBasic syntax -- Env: %s" % (rep.env))


rep("1")
rep("(q . 1)")
rep("(q . q)")
rep("'1")
rep("'(1)")
rep("'\"q\"")
rep("(+ '2 '2 . 0)")
rep("(+ (q . 2) '2)")
rep("(a '1 '1 '2 '3 '4)")
rep("(a '1 '1 '2 '3 '4 '5)")
rep("(a '1 '1 '2 '3 '4 '5 '6)")
rep("(a '1 '1 '2 '3 '4 '5 '6 '7)")
rep("(a '1 '1 '2 '3 '4 '5 '6 '7 '8)")
rep("(a '(+ '2 '2))")
rep("(h '(4 5 6))")
rep("(t '(4 5 6))")
rep("(+ 7 '3)")
rep("(a '(+ 7 '3))")
rep("(a '(+ 7 '3) 1)")
rep("(a '(+ 7 '3) '((1 . 2) . (3 . 4)))")
rep("(c)")
rep("(c . 1)")
rep("(c nil)")
rep("(c 1)")
rep("(c 1 nil)")
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
rep("(+ '1 '2 . '3)")
rep("(<s)")
rep("(<s '1)")
rep("(<s '99 '66 '88)")
rep("(<s '1 '2 '3)")
rep("(<s nil '0x00 '0x0001 '0x01 '0x02)")
rep("(<s '0x00 '0x0001 '0x01 '0x0002)")
rep("(c (<s '254 '255) (< '254 '255) nil)")
rep("(c (<s '255 '256) (< '255 '256) nil)")
rep("(%)")
rep("(% '100 '3)")
rep("(% '100 '3 '2)")
rep("(~ '7)")
rep("(~)")
rep("(~ 0)")
rep("(~ '1 '3 '5)")

# factorial
# n=2, fn=3
# `if 2 (a 3 (- 2 '1) 3)
rep = Rep(Compiler.compile("(a (i 2 '(* 2 (a 3 (- 2 '1) 3)) ''1))"))
print("\nInefficient factorial -- Env: %s" % (rep.env))
rep("(a 1 '3 1)")
rep("(a 1 '10 1)")
rep("(a 1 '40 1)")
#rep("(a 1 '150 1)")
#rep("(a 1 (c '15000 1))")

# factorial but efficient
rep = Rep(Compiler.compile("(a (i 2 '(a 7 (c (- 2 '1) (* 5 2) 7)) '(c 5)))"))
print("\nEfficient (?) factorial -- Env: %s" % (rep.env))
rep("(a 1 (c '3 '1 1))")
rep("(a 1 (c '10 '1 1))")
rep("(a 1 (c '40 '1 1))")
rep("(a 1 (c '150 '1 1))")  # nil since 66! == 0 (mod 2**64)
rep("(a 1 (c '15000 '1 1))")

# sum factorial (+ 1! 2! 3! 4! ... n!)
# (proxy for (sha256 1! 2! .. n!)
# f 1 1 n
# f a! a b =
# 4=fn 6=(a-1)! 5=a 7=left!

rep = Rep(Compiler.compile("(a (i 7 '(c (c nil 6) (a 4 4 (* 6 5) (+ 5 '1) (- 7 '1))) '(c nil)))"))
print("\nSum factorial (1! + 2! + .. + n!) -- Env: %s" % (rep.env))
#rep("(a 1 1 '1 '1 '10)")
rep("(c '+ (a 1 1 '1 '1 '10))")
rep("(a (c '+ (a 1 1 '1 '1 '10)))")

# fibonacci


# 0 1 1 2 3 5 ...
# 0 1 2 3 4 5

# fib n = fib n 0 1
# fib 0 a b = a; fib n a b = fib (n-1) b (a+b)
# env = (n a b FIB) ; n=2, a=5, b=11, FIB=15

rep = Rep(Compiler.compile("(a (i 2 '(a 15 (c (- 2 '1) 11 (+ 5 11) 15)) '(c 5)))"))
print("\nFibonacci 1 -- Env: %s" % (rep.env))
rep("(a 1 (c '300 '0 '1 1))")
rep("(a 1 (c '500 '0 '1 1))")

rep = Rep(Compiler.compile("(a (i 4 '(a 7 (- 4 '1) 5 (+ 6 5) 7) '(c 6)))"))
print("\nFibonacci 2 -- Env: %s" % (rep.env))
rep("(a 1 '300 '0 '1 1)")
rep("(a 1 '500 '0 '1 1)")

rep = Rep(Compiler.compile("0x0200000015a20d97f5a65e130e08f2b254f97f65b96173a7057aef0da203000000000000887e309c02ebdddbd0f3faff78f868d61b1c4cff2a25e5b3c9d90ff501818fa0e7965d508bdb051a40d8d8f7"))
print("\nHash a transaction -- Env: %s" % (rep.env))
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

Set_GLOBAL_TX(verystable.core.messages.tx_from_hex("f0ccee2a000101ebf2f9fc896e70145c84116fae33d0242f8c146e1a07deecd9a98d9cc03f4fb70d000000002badf3fb01126b8c01000000001976a914551b850385def11149727e72c4470ffaeae5cdf288ac04402c797661dfac511e35f42601edd355e9cffb6ce47beddd9a9bf0914992c002af34c67933f89da981149f6044448f14ec7931f3641da82fac3aa9512d052e3b712220256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963fac21c0cdb18e708d5164ecbd681797623cb8f9be34dd1765ef0b63788d18ca4db18478025073ee1a6e46"))
Set_GLOBAL_TX_INPUT_IDX(0)
Set_GLOBAL_TX_SCRIPT(bytes.fromhex("20256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963fac"))
Set_GLOBAL_UTXOS([
    verystable.core.messages.from_hex(verystable.core.messages.CTxOut(), "1fc6d101000000002251203240405372856fe921522eca27514e2669f0aa4c46d52c78cfe608174828f937")
])

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

for a in [0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,20,21]:
    rep("(tx '%d)" % (a,))

# acc fn 0 n nil -> acc fn 1 (- n 1) (cat nil (fn 0))
#  8  12 10 14 3
rep = Rep(Compiler.compile("nil"))
print("\nBIP342 calculated manually -- Env: %s" % (rep.env))
rep("(bip342_txmsg)")

# implement sighash_all, codesep_pos=-1, len(scriptPubKey) < 253
rep("(a '(a '(sha256 4 4 '0x00 6 3) (sha256 '\"TapSighash\") (cat '0x00 (tx '0) (tx '1) (sha256 (a 1 1 '(cat (tx (c '11 1)) (tx (c '12 1))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '15 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(a '(cat (strlen 1) 1) (tx '(16 . 0))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '10 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(cat (tx (c '20 1)) (a '(cat (strlen 1) 1) (tx (c '21 1)))) '0 (tx '3) 'nil)) (i (tx '14) '0x03 '0x01) (substr (cat (tx '4) '0x00000000) 'nil '4) (i (tx '14) (sha256 (a '(cat (strlen 1) 1) (tx '14))) 'nil)) (cat (tx '6) '0x00 '0xffffffff)) '(a (i 14 '(a 8 8 12 (+ 10 '1) (- 14 '1) (cat 3 (a 12 10))) '3)))")

rep("(cat '0x1122 '0x3344)")

rep("(secp256k1_muladd)")
rep("(secp256k1_muladd '1)")
rep("(secp256k1_muladd '(1))")
rep("(secp256k1_muladd '1 '(1))")


# (defun bip340check (R s e P) `(secp256k1_muladd ('1 . ,R) (,e . ,P) (,s)))
# (defun mkR (sig) `(substr ,sig 0 '32))
# (defun mkS (sig) `(substr ,sig '32 '64))
# (defun taghash (tag) `(a '(cat 1 1) (sha256 ,tag))
# (defun mkE (R P m) `(sha256 (taghash "BIP0340/challenge") ,R ,P ,m)
# (defun mybip340x (R s P m)
#        `(bip340check ,R ,s (mkE ,R ,P ,m) ,P))
# (defun mybip340 (sig P m) `(mybip340x (mkR ,sig) (mkS ,sig) ,P ,m)

bip340check = "(secp256k1_muladd (c '1 4) (c 5 7) (c 6 nil))"
  # expects R s e P
mkE = "(sha256 (a '(cat 1 1) (sha256 '\"BIP0340/challenge\")) 4 6 3)"
  # expects R p m
mybip340x = "(a 5 8 12 (a 7 8 10 14) 10)"
  # expects R s P m bip340check mkE
mybip340 = "(a 7 (substr 8 0 '32) (substr 8 '32 '64) 12 10 14 5)"
  # expects sig P m bip340check mkE mybip340x
sexpr = "((%s . %s) . (%s . %s))" % (bip340check, mkE, mybip340x, mybip340)
print(f"env={sexpr}")
rep = Rep(Compiler.compile(sexpr))
  # usage: (a 7 SIG P M 4 6 5)

# P = F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9
# m = 0000000000000000000000000000000000000000000000000000000000000000
# sig = E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0

rep("1")
rep("(a 7 '0xE907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0 '0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9 '0x0000000000000000000000000000000000000000000000000000000000000000 4 6 5)")


# control block =  c1e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1
# script = 20e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1ac0063036f726401010a746578742f706c61696e00337b2270223a226272632d3230222c226f70223a226d696e74222c227469636b223a22656f7262222c22616d74223a223130227d68
# scriptPK = 5120 c142718fddee89867607e1eeb6e1aab685285e5c78c9ffd2f379c68d52bcb0b6

taghash = "(a '(sha256 2 2 3) (sha256 2) 3)"
  # expects tag contents
tapleaf = "(a 3 '\"TapLeaf\" (cat 4 (strlen 6) 6))"
  # expects v script taghash
tapbranch =  "(a 3 '\"TapBranch\" (i (<s 4 6) (cat 4 6) (cat 6 4)))"
  # expects a b taghash
tappath = "(i 12 (a 5 (a 14 8 (substr 12 '0 '32) 10) (substr 12 '32) 10 14 3) (a 10 '\"TapTweak\" (cat 7 8)))"
  # expects leaf:8 path:12 taghash:10 tapbranch:14 tappath:5 P:7
taproot = "(secp256k1_muladd (a 9 (a 11 (& 16 '0xfe) 24 15) 12 15 13 9 10) (c '1 10) (c (& 16 '1) 14))"
  # expects v:16 script:24 path:12 ipk:10 spk:14 tappath:9 tapbranch:13 tapleaf:11 taghash:15

sexpr = "(((%s . %s) . %s) . (%s . %s))" % (taproot, taghash, tapleaf, tapbranch, tappath)
print(f"env={sexpr}")
rep = Rep(Compiler.compile(sexpr))
  # usage: (a 8 '(V . SCRIPT) PATH IPK SPK 7 5 6 12)

rep("(a 8 '(0xc1 . 0x20e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1ac0063036f726401010a746578742f706c61696e00337b2270223a226272632d3230222c226f70223a226d696e74222c227469636b223a22656f7262222c22616d74223a223130227d68) nil '0xe9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1 '0xc142718fddee89867607e1eeb6e1aab685285e5c78c9ffd2f379c68d52bcb0b6 7 5 6 12)")

rep("(a 8 '(0xc1 . 0x20e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1ac0063036f726401010a746578742f706c61696e00337b2270223a226272632d3230222c226f70223a226d696e74222c227469636b223a22656f7262222c22616d74223a223130227d68) nil '0xe9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1 '0xc142718fddee89867607e1eeb6e1aab685285e5c78c9ffd2f379c68d52bcb0b6 7 5 6 12)")

# same as above, but this time the witness data is in the environment,
# and the program is passed in

rep = Rep(SExpr.parse("0xc1 0x20e9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1ac0063036f726401010a746578742f706c61696e00337b2270223a226272632d3230222c226f70223a226d696e74222c227469636b223a22656f7262222c22616d74223a223130227d68 nil 0xe9d8184a170affaac4f7924a31899b1668a49d7d857b8cec611e79f39c5c7ba1 0xc142718fddee89867607e1eeb6e1aab685285e5c78c9ffd2f379c68d52bcb0b6", many=True))
rep("(a '(a 16 (c 17 25) 21 29 7 6 28 20 24) (b '(%s %s %s %s %s)) (b 1))" % (taproot, taghash, tapleaf, tapbranch, tappath))

rep = Rep(SExpr.parse("12"))
rep("(module (define (_x _a _b) (* _a _b)) (define (main _a) (+ (_x _a _a) '1)))")
#print(exp)

rep = Rep(SExpr.parse("19"))
rep("(module (define (factorial _n accum) (i _n (factorial (- _n '1) (* _n accum)) accum)) (define (main _x) (factorial _x '1)))")


rep = Rep(SExpr.parse("(0x256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963f . 0x2c797661dfac511e35f42601edd355e9cffb6ce47beddd9a9bf0914992c002af34c67933f89da981149f6044448f14ec7931f3641da82fac3aa9512d052e3b71)"))

rep("(a '(secp256k1_muladd (c '1 4) (c (sha256 5 4 7 (bip342_txmsg)) 7) (c 6 nil)) (substr 3 0 '32) (substr 3 '32 '64) (a '(cat 1 1) (sha256 '\"BIP0340/challenge\")) 2)")

rep("(bip340_verify '0x256c556c3663e1cfe2412e879bc1ace16785aa79c0ae1840e831e837ab9d963f (bip342_txmsg) '0x2c797661dfac511e35f42601edd355e9cffb6ce47beddd9a9bf0914992c002af34c67933f89da981149f6044448f14ec7931f3641da82fac3aa9512d052e3b71)")

rep("(rd '0xa0)")
rep("(wr '(1 2 3 (4 5 6 (7 8 9))))")
rep("(rd '0x780102037804050677070809)")
rep("(rd (wr '(1 2 3 (4 5 6 (7 8 9)))))")

print("first: bip340")
rep("(wr '(a '(secp256k1_muladd (c '1 4) (c (sha256 5 4 7 (bip342_txmsg)) 7) (c 6 nil)) (substr 3 0 '32) (substr 3 '32 '64) (a '(cat 1 1) (sha256 '\"BIP0340/challenge\")) 2))")
print("second: sighash_all")
rep("(wr '(a '(a '(sha256 4 4 '0x00 6 3) (sha256 '\"TapSighash\") (cat '0x00 (tx '0) (tx '1) (sha256 (a 1 1 '(cat (tx (c '11 1)) (tx (c '12 1))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '15 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(a '(cat (strlen 1) 1) (tx '(16 . 0))) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(tx (c '10 1)) '0 (tx '2) 'nil)) (sha256 (a 1 1 '(cat (tx (c '20 1)) (a '(cat (strlen 1) 1) (tx (c '21 1)))) '0 (tx '3) 'nil)) (i (tx '14) '0x03 '0x01) (substr (cat (tx '4) '0x00000000) 'nil '4) (i (tx '14) (sha256 (a '(cat (strlen 1) 1) (tx '14))) 'nil)) (cat (tx '6) '0x00 '0xffffffff)) '(a (i 14 '(a 8 8 12 (+ 10 '1) (- 14 '1) (cat 3 (a 12 10))) '3))))")

# test: (secp_muladd ,tt (1 ,p) (,x ,spk))
# tt: (a '(sha256 1 1 ,p ,root) (sha256 '"TapTweak"))
# tl: (a '(sha256 1 1 ,v (strlen ,scr) ,scr) (sha256 '"TapLeaf"))



# levels:
#   bytes/hex
#   (c (q . 1) (q . 0xCAFEBABE) (q . "hello, world") (q . nil))
#   \' and aliases? (car,head = h, etc)
#   symbols; let/defun (compile to env access)
#   \` and \,  (qq and unquote in chialisp / macros)

# notation?
#   'foo  = (q . foo)
#   '(a b c) = (q a b c)
#   `(a ,b c) = (c (q . a) b (q . c) nil)
#
# would be nice to have a "compiler" that can deal with a symbol table
# (for named ops).
