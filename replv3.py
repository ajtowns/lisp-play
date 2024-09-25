#!/usr/bin/env python3

import cmd
import functools
import os
import sys
import traceback

from dataclasses import dataclass, field
from typing import Optional, Tuple, List, Any, Self

from element2 import Element, SExpr, Atom, Cons, Error, Symbol, Func, ALLOCATOR
from opcodes import SExpr_FUNCS, Op_FUNCS, Opcode

##########

# To do:
#
#  * make bll evaluation work
#  * make compilation work
#
#  * all the opcodes
#  * implement op_partial
#
#  * add tx/utxo commands
#
#  * do stuff about costs?
#  * do stuff about ensuring refcounting is correct?
#
#  * add tui debugger (via "textual" module?)
#
# possibly:
#    def (factorial x (= acc 1))  (a (i x '(factorial (- x 1) (* acc x)) 'acc))
#    eval (factorial 7)

##########

# how does compilation work?
# i guess i want something that will interpret from just numbers?

#    def (foo a b c) (* (+ a b) (+ a c) 3)
#    ; (foo 1 2 3)

#    def (foo (a.3) (b.4) (c.5)) (* (+ a b) (+ a c) 3)
#    ; (foo) = (foo 3 4 5)

#    $foo = (* (+ 9 13) (+ 9 7) (nil . 3))    ## whatever values * and + are

#    def (bar a) (foo a (+ a 1) (+ a 2))
#    def (qux a) (+ a 2)

#    $bar = (a 8 2 (b 3 (+ 3 (q . 1)) (+ 3 (q . 2))))

#    (a (i X bar qux) 9)
#    (a (i X 12 6) (q . 9))

#    that's basically the "if" construction anyway? except with arguments

# if we did elements2.py, perhaps we could tag elements as to whether they
# reference a symbol/function/etc?, or are bll-compatible?
# if we did that, should continuations become elements? with a special type, or
# just semi-structured?

##########

####

def handle_exc(func):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        try:
            return func(*args, **kwargs)
        except Exception:
            traceback.print_exc()
    return wrapper

####

class SymbolTable:
    def __init__(self):
        self.refcnt = 1
        self.syms = {}

    def set(self, symname, value):
        # XXX: cope with parameters (and default values for parameters)
        assert isinstance(symname, str)
        if not isinstance(value, Element):
            assert isinstance(value, tuple) and len(value) == 2
            assert all(isinstance(v, Element) for v in value)

        if symname in self.syms:
            self.syms[symname].deref()
        self.syms[symname] = value

    def unset(self, symname):
        assert isinstance(symname, str), f"{repr(symname)} not a str?"
        if symname in self.syms:
            self.syms[symname].deref()
            del self.syms[symname]

    def bumpref(self):
        self.refcnt += 1
        return self

    def deref(self):
        self.refcnt -= 1
        if self.refcnt == 0:
            for _, v in self.syms.items():
                v.deref()
            self.syms = None

def ResolveSymbol(localsyms, globalsyms, symname):
    assert isinstance(symname, str)

    if symname == "if":
        return fn_if()

    if symname in SExpr_FUNCS:
        op = Op_FUNCS[SExpr_FUNCS[symname]]
        return fn_op(Func(op.initial_state(), op()))

    # locals override globals, but do not override builtins
    r = localsyms.syms.get(symname, None)
    if r is None:
        r = globalsyms.syms.get(symname, None)
    if r is None:
        return None

    if isinstance(r, Element):
        return r.bumpref()
    else:
        return fn_userfunc(r[0].bumpref(), r[1].bumpref())

    return None

#### evaluation model = workitem with continuations

class Functor:
    def step(self, workitem): raise NotImplementedError
    def feedback(self, workitem, value):
        # defaults to a no-op, discarding the passed in value
        value.deref()

    def deref(self):
        pass # deref any internal state

    def __repr__(self):
        return self.__class__.__name__

class fn_fin(Functor):
    def step(self, workitem):
        assert workitem.continuations
        assert workitem.continuations[-1].fn is self
        if len(workitem.continuations) == 1:
            return
        cont = workitem.continuations[-1]
        if cont.args.is_error():
            workitem.continuations.pop()
            while workitem.continuations:
                workitem.popcont()
            workitem.continuations.append(cont)
            return
        v = cont.args.bumpref()
        workitem.popcont()
        pcont = workitem.continuations[-1]
        pcont.fn.feedback(workitem, v)

class fn_eval(Functor):
    def step(self, workitem):
        assert workitem.continuations
        cont = workitem.continuations[-1]
        assert cont.fn is self
        assert isinstance(cont.args, Element)
        if cont.args.is_atom() or cont.args.is_error():
            cont.fn = fn_fin()
            return cont.fn.step(workitem)
        elif cont.args.is_cons():
            op, cont.args = cont.args.steal_children()
            if op.is_symbol():
                r = ResolveSymbol(cont.localsyms, workitem.globalsyms, op.val2)
                op.deref()
                if r is None:
                    workitem.error("undefined symbol")
                    return
                if isinstance(r, Functor):
                     cont.fn = r
                     return
                else:
                     r.deref()
                     return
            op.deref()
            workitem.error("expression does not have a function/operator")
        elif cont.args.is_func():
            # not sure?
            workitem.error("BUG? expression with raw function??")
        elif cont.args.is_symbol():
            r = ResolveSymbol(cont.localsyms, workitem.globalsyms, cont.args.val2)
            if r is None:
                workitem.error("undefined symbol")
                return
            elif isinstance(r, Element):
                cont.args.deref()
                cont.args = r
            elif isinstance(r, Functor):
                workitem.error("opcode must be called")
                r.deref()
            else:
                workitem.error(f"BUG? symbol {cont.args}={r} isn't a functor or element")
        else:
            # internal error
            workitem.error("BUG? not sure what to eval")

class fn_op(Functor):
    @staticmethod
    def _get_type(obj):
        return obj if isinstance(obj, type) else type(obj)

    def __init__(self, opcode):
        assert isinstance(opcode, Element) and opcode.is_func()
        self.op_func = opcode

    def __repr__(self):
        return f"{self.op_func}"

    def deref(self):
        self.op_func.deref()

    def step(self, workitem):
        assert workitem.continuations
        assert workitem.continuations[-1].fn is self
        cont = workitem.continuations[-1]
        if cont.args.is_nil():
            f = self.op_func.val2.finish(self.op_func.val1)
            c = Continuation(fn=fn_fin(), args=f, localsyms=cont.localsyms.bumpref())
            workitem.popcont()
            workitem.continuations.append(c)
        elif cont.args.is_cons():
            w, cont.args = cont.args.steal_children()
            c = Continuation(fn=fn_eval(), args=w, localsyms=cont.localsyms.bumpref())
            workitem.continuations.append(c)
        else:
            workitem.error("argument to opcode is improper list")

    def feedback(self, workitem, value):
        assert workitem.continuations
        assert workitem.continuations[-1].fn is self
        assert isinstance(value, Element)
        if value.is_error():
            workitem.error("argument to opcode is improper list")
            return

        nof = self.op_func.val2.argument(self.op_func.val1, value)
        value.deref()
        assert isinstance(nof, Element) and nof.is_func()
        assert issubclass(self._get_type(nof.val2), Opcode)
        self.op_func.deref()
        self.op_func = nof

class fn_if(Functor):
    def step(self, workitem):
        assert workitem.continuations
        cont = workitem.continuations[-1]
        assert cont.fn is self

        if not cont.args.is_cons():
            workitem.error("if requires at least one argument")
            return

        cond, cont.args = cont.args.steal_children()
        c = Continuation(fn=fn_eval(), args=cond, localsyms=cont.localsyms.bumpref())
        workitem.continuations.append(c)

    def feedback(self, workitem, value):
        assert workitem.continuations
        cont = workitem.continuations[-1]
        assert cont.fn is self

        if cont.args.is_cons():
            iftrue, cont.args = cont.args.steal_children()
        elif cont.args.is_nil():
            iftrue = Atom(1)

        if cont.args.is_cons():
            iffalse, cont.args = cont.args.steal_children()
        elif cont.args.is_nil():
            iffalse = Atom(0)

        if not cont.args.is_nil():
            iftrue.deref()
            iffalse.deref()
            value.deref()
            if cont.args.is_cons():
                worktree.error("if must have at most three arguments")
            else:
                worktree.error("argument to if are improper list")
            return

        if value.is_nil():
            iftrue.deref()
            c = Continuation(fn=fn_eval(), args=iffalse, localsyms=cont.localsyms.bumpref())
        else:
            iffalse.deref()
            c = Continuation(fn=fn_eval(), args=iftrue, localsyms=cont.localsyms.bumpref())
        workitem.popcont()
        workitem.continuations.append(c)
        value.deref()

class fn_userfunc(Functor):
    def __init__(self, params, expr):
        self.params = params
        self.expr = expr
        self.syms = SymbolTable()

    def __repr__(self):
        return f"{self.params}->{self.expr}"

    def deref(self):
        self.params.deref()
        self.expr.deref()
        self.syms.deref()

    def step(self, workitem):
        assert workitem.continuations[-1].fn is self
        cont = workitem.continuations[-1]
        if cont.args.is_nil():
            if self.params.is_nil():
                # done!
                c = Continuation(fn=fn_eval(), args=self.expr.bumpref(), localsyms=self.syms.bumpref())
                workitem.popcont()
                workitem.continuations.append(c)
                return
            #elif self.params.is_cons() and self.params.val1.is_cons():
            #   XXX fill in default arguments
            else:
                workitem.error("insufficient arguments for user defined function")
                return
        elif cont.args.is_cons():
            if self.params.is_nil():
                workitem.error("too many arguments for user defined functions")
                return
            elif self.params.is_cons() and self.params.val1.is_symbol():
                param, cont.args = cont.args.steal_children()
                c = Continuation(fn=fn_eval(), args=param, localsyms=cont.localsyms.bumpref())
                workitem.continuations.append(c)
                return
            else:
                workitem.error("user defined function has non-symbol as param name?")
                return
        else:
            workitem.error("call to user defined function is not proper list")
            return

    def feedback(self, workitem, value):
        cont = workitem.continuations[-1]
        assert cont.fn is self
        assert self.params.is_cons() and self.params.val1.is_symbol()
        param, self.params = self.params.steal_children()
        self.syms.set(param.val2, value)
        param.deref()

@dataclass
class Continuation:
    fn: Functor
    args: Element           # (remaining) arguments to fn
    localsyms: SymbolTable

    def __repr__(self):
        return f"Continuation({self.fn}, {self.args})"

    def deref(self):
        self.fn.deref()
        self.args.deref()
        self.localsyms.deref()

@dataclass
class WorkItem:
    globalsyms: SymbolTable
    continuations: List[Continuation]
    dummylocalsyms: SymbolTable = field(default_factory=SymbolTable)

    @classmethod
    def begin(cls, sexpr, syms):
        wi = WorkItem(globalsyms=syms, continuations=[])
        c = Continuation(fn=fn_eval(), args=sexpr, localsyms=wi.dummylocalsyms.bumpref())
        wi.continuations.append(c)
        return wi

    def error(self, msg):
        c = Continuation(fn=fn_fin(), args=Error(msg), localsyms=self.dummylocalsyms.bumpref())
        self.popcont()
        self.continuations.append(c)

    def popcont(self):
        last = self.continuations.pop()
        last.deref()

    def finished(self):
        return isinstance(self.continuations[0].fn, fn_fin)

    def get_result(self):
        assert self.finished()
        r = self.continuations[0].args.bumpref()
        self.popcont()
        return r

    def localsyms(self):
        if self.continuations:
            return self.continuations[-1].localsyms
        else:
            return self.dummylocalsyms

    def step(self):
        cont = self.continuations[-1].fn.step(self)

def symbolic_eval(sexpr, globalsyms):
    wi = WorkItem.begin(sexpr, globalsyms)

    while not wi.finished():
        wi.step()

    return wi.get_result()

class BTCLispRepl(cmd.Cmd):
    def __init__(self, prompt=None):
        self.prompt = ">>> " if prompt is None else prompt
        self.symbols = SymbolTable()
        self.wi = None

        cmd.Cmd.__init__(self)

    def show_state(self):
        if self.wi is None: return
        for c in reversed(self.wi.continuations):
            s = " ".join(f"{k}={v}" for k,v in c.localsyms.syms.items())
            if s != "": s = f"    [{s}]"
            print(f"   -- {c.fn}    {c.args}{s}")

    def default(self, line):
        if line.strip().startswith(";"):
            # comment
            return
        return super().default(line)

    def do_exit(self, arg):
        return True

    def do_EOF(self, arg):
        if self.prompt != "": print()
        return True

    @handle_exc
    def do_eval(self, arg):
        before = ALLOCATOR.x
        s = SExpr.parse(arg)
        r = symbolic_eval(s, self.symbols)
        print(r)
        r.deref()
        print(f"allocation: {before} -> {ALLOCATOR.x}")
        if before < ALLOCATOR.x:
            print("allocated:")
            for x in ALLOCATOR.allocated:
                print(f"    {x.refcnt} {x}")

    @handle_exc
    def do_debug(self, arg):
        if self.wi is not None:
            print("Already debugging an expression")
            return
        sexpr = SExpr.parse(arg)
        self.wi = WorkItem.begin(sexpr, self.symbols)
        self.show_state()

    @handle_exc
    def do_step(self, arg):
        if self.wi is None:
            print("No expression being debugged")
        elif not self.wi.finished():
            self.wi.step()
            self.show_state()
        else:
            r = self.wi.get_result()
            print(f"Result: {r}")
            r.deref()
            self.wi = None

    @handle_exc
    def do_next(self, arg):
        if self.wi is None:
            print("No expression being debugged")

        target = len(self.wi.continuations)
        while not self.wi.finished():
            self.wi.step()
            if len(self.wi.continuations) <= target:
                break
        if not self.wi.finished():
            self.show_state()
        else:
            r = self.wi.get_result()
            print(f"Result: {r}")
            r.deref()
            self.wi = None

    @handle_exc
    def do_cont(self, arg):
        if self.wi is None:
            print("No expression being debugged")
            return

        while not self.wi.finished():
            self.wi.step()

        r = self.wi.get_result()
        print(f"Result: {r}")
        r.deref()
        self.wi = None

    @handle_exc
    def do_def(self, arg):
        s = SExpr.parse(arg, manypy=True)
        if len(s) != 2:
            print("Expected symbol name (plus parameters) and definition")
            for e in s: e.deref()
            return
        sym, val = s
        if sym.is_symbol():
            self.symbols.set(sym.val2, val.bumpref())
        elif sym.is_cons() and sym.val1.is_symbol():
            self.symbols.set(sym.val1.val2, (sym.val2.bumpref(), val.bumpref()))
        else:
            print("Expected symbol name (plus parameters) and definition")
        for e in s:
            e.deref()

    @handle_exc
    def do_undef(self, arg):
        for x in arg.split():
            x = x.strip()
            if x == "": continue
            self.symbols.unset(x)

if __name__ == "__main__":
    if os.isatty(sys.stdin.fileno()):
        repl = BTCLispRepl()
    else:
        repl = BTCLispRepl(prompt="")
    repl.cmdloop()

