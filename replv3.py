#!/usr/bin/env python3

import cmd
import functools
import os
import sys
import traceback

from dataclasses import dataclass, field
from typing import Optional, Tuple, List, Any, Self

from element2 import Element, SExpr, Atom, Cons, Error, Symbol, Func, ALLOCATOR
from opcodes import SExpr_FUNCS, Op_FUNCS

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
        return Func(op.initial_state(), op())

    # locals override globals, but do not override builtins
    if symname in localsyms.syms: return localsyms.syms[symname].bumpref()
    if symname in globalsyms.syms: return globalsyms.syms[symname].bumpref()

    return None

#### evaluation model = workitem with continuations

@dataclass
class Continuation:
    args: Element      # remaining arguments
    localsyms: SymbolTable
    fn: Optional[Element] = None

    def __repr__(self):
        return f"Continuation({self.fn}, {self.args})"

    def deref(self):
        if isinstance(self.localsyms, SymbolTable):
            self.localsyms.deref()
        if isinstance(self.args, Element):
            self.args.deref()
        if isinstance(self.fn, Element):
            self.fn.deref()

    def feedback(self, value):
        if self.fn is None:
            if value.is_func():
                self.fn = value.bumpref()
            else:
                return Error("non-function used as function")
        else:
            # Opcode application
            a = self.fn.val2.argument(self.fn.val1, value)
            self.fn.deref()
            self.fn = a

        assert self.fn is not None

        if self.fn.is_error():
            err, self.fn = self.fn, None
            return err

        if self.args.is_cons():
            res, self.args = self.args.steal_children()
            return res

        if self.args.is_nil():
            res, self.fn = self.fn, None
            return res
        else:
            return Error("improper list in functional expression")

@dataclass
class WorkItem:
    value: Element
    globalsyms: SymbolTable
    continuations: List[Continuation] = field(default_factory=list)
    is_result: bool = False
    dummylocalsyms: SymbolTable = field(default_factory=SymbolTable)

    def popcont(self):
        last = self.continuations.pop()
        last.deref()

    def finished(self):
        return (self.is_result and not self.continuations)

    def localsyms(self):
        if self.continuations:
            return self.continuations[-1].localsyms
        else:
            return self.dummylocalsyms

    def step(self):
        if isinstance(self.value, Element):
            assert self.value.refcnt > 0

        # trivial cases, handle them immediately
        if self.value.is_error():
            if self.continuations:
                self.popcont()
                return
            self.is_result = True

        elif self.value.is_atom():
            self.is_result = True

        # have a result, feed it back
        if self.is_result:
            if self.continuations:
                v = self.continuations[-1].feedback(self.value)
                self.value.deref()
                self.value = v
                self.is_result = False
                if self.continuations[-1].fn is None:
                    self.popcont()
            return

        # finish function
        if self.value.is_func():
            f = self.value.val2.finish(self.value.val1)
            self.value.deref()
            self.value = f
            self.is_result = True
            return
        elif self.value.is_cons():
            self.value, t = self.value.steal_children()
            self.continuations.append(Continuation(args=t, localsyms=self.localsyms().bumpref()))
            return
        elif self.value.is_symbol():
            v = self.value
            sym = v.val2
            if sym == 'q' and self.continuations and self.continuations[-1].fn is None:
                # rewrite (q . foo)
                cont = self.continuations[-1]
                self.value.deref()
                self.value = cont.args
                self.is_result = True
                cont.args = None
                self.popcont()
                return

            self.value = ResolveSymbol(self.localsyms(), self.globalsyms, sym)
            if self.value is None:
                self.value = Error(f"Unknown symbol {sym}")
            elif self.value.is_func():
                self.is_result = True
            v.deref()
            return
        else:
            raise Exception(f"unknown element kind {self.value.kind}")

def symbolic_eval(sexpr, globalsyms):
    wi = WorkItem(value=sexpr, globalsyms=globalsyms)

    while not wi.finished():
        wi.step()

    return wi.value

class BTCLispRepl(cmd.Cmd):
    def __init__(self, prompt=None):
        self.prompt = ">>> " if prompt is None else prompt
        self.symbols = SymbolTable()
        self.wi = None

        cmd.Cmd.__init__(self)

    def show_state(self):
        if self.wi is None: return
        print(f" --- {'*' if self.wi.is_result else ''}{self.wi.value}")
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
        self.wi = WorkItem(value=sexpr, globalsyms=self.symbols)
        self.show_state()

    @handle_exc
    def do_step(self, arg):
        if self.wi is None:
            print("No expression being debugged")
        elif not self.wi.finished():
            self.wi.step()
            self.show_state()
        else:
            print(f"Result: {self.wi.value}")
            self.wi.value.deref()
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

