#!/usr/bin/env python3

import time

from element import Element, SExpr, ALLOCATOR, ATOM, CONS, ERROR, FUNC, REF, SYMBOL, SerDeser, nil, one
from funcs import  Op_FUNCS, SExpr_FUNCS, Tree, fn_eval, get_env

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

