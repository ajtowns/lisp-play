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
#  * implement op_partial
#  * make function calls work
#
#  * make bll evaluation work
#  * make compilation work
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
            for _, v in self.syms:
                v.deref()
            self.syms = None

def ResolveSymbol(localsyms, globalsyms, symname):
    if symname in SExpr_FUNCS:
        op = Op_FUNCS[SExpr_FUNCS[symname]]
        return fn_op(Func(op.initial_state(), op()))

    # locals override globals, but do not override builtins
    if symname in localsyms.syms: return localsyms.syms[symname].bumpref()
    if symname in globalsyms.syms: return globalsyms.syms[symname].bumpref()

    # should be creating a functor for user functions here

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
        assert len(workitem.continuations) > 1
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
                if isinstance(r, Functor):
                     cont.fn = r
                     return
                else:
                     r.deref()
            op.deref()
            workitem.error("expression does not have a function/operator")
        elif cont.args.is_func():
            # not sure?
            workitem.error("BUG? expression with raw function??")
        elif cont.args.is_symbol():
            r = ResolveSymbol(cont.localsyms, workitem.globalsyms, cont.args)
            if isinstance(r, Element):
                cont.args.deref()
                cont.args = r
            elif isinstance(r, Functor):
                workitem.error("symbol must be called")
                r.deref()
            else:
                workitem.error("BUG? symbol isn't a functor or element")
                r.deref()
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

    def deref(self):
        self.op_func.deref()

    def __repr__(self):
        return f"{self.op_func}"

    def step(self, workitem):
        assert workitem.continuations
        assert workitem.continuations[-1].fn is self
        cont = workitem.continuations[-1]
        if cont.args.is_nil():
            f = self.op_func.val2.finish(self.op_func.val1)
            c = Continuation(fn_fin(), f, cont.localsyms)
            workitem.popcont()
            workitem.continuations.append(c)
        elif cont.args.is_cons():
            w, cont.args = cont.args.steal_children()
            c = Continuation(fn_eval(), w, cont.localsyms)
            workitem.continuations.append(c)
        else:
            c = Continuation(fn_fin(), Error("argument to opcode is improper list"))
            workitem.popcont()
            workitem.continuations.append(c)

    def feedback(self, workitem, value):
        assert workitem.continuations
        assert workitem.continuations[-1].fn is self
        assert isinstance(value, Element)
        if value.is_error():
            c = Continuation(fn_fin(), Error("argument to opcode is improper list"))
            workitem.popcont()
            workitem.continuations.append(c)
            return

        nof = self.op_func.val2.argument(self.op_func.val1, value)
        assert isinstance(nof, Element) and nof.is_func()
        assert issubclass(self._get_type(nof.val2), Opcode)
        self.op_func.deref()
        self.op_func = nof

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
        c = Continuation(fn_fin(), Error(msg))
        workitem.popcont()
        workitem.continuations.append(c)

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
            print(f"   -- {c.fn}    {c.args}")

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
    def do_cont(self, arg):
        if self.wi is None:
            print("No expression being debugged")
            return

        while not self.wi.finished():
            self.wi.step()

        print(f"Result: {self.wi.value}")
        self.wi.value.deref()
        self.wi = None
        return

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
            self.symbols.set(sym.val1.val2, [sym.val2.bumpref(), val.bumpref()])
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

