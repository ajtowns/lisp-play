#!/usr/bin/env python3

import cmd
import functools
import os
import sys
import traceback

from dataclasses import dataclass, field
from typing import Optional, Tuple, List, Any, Self

from element2 import Element, SExpr, Atom, Cons, Error, Symbol, Func
from opcodes import SExpr_FUNCS, Op_FUNCS

##########

# To do:
#
#  * funcv2.py
#  * have them have a better repr()
#  * implement op_partial
#
#  * make def work at all
#  * separate symbols into  pre-defined, global, local
#  * make function calls work
#
#  * make bll evaluation work
#  * make compilation work
#  * make symbolic evaluation work when invoked with compiled code
#    (does the first argument to a contain symbols? symbolic, no env. else,
#     bll, potentially with env)
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
        return op.make_func()

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
        # XXX should deref symtable too
        if isinstance(self.fn, Element): self.fn.deref()
        if isinstance(self.args, Element): self.args.deref()

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

    def feedback(self):
        if not self.continuations:
            return

        cont = self.continuations[-1]
        if cont.fn is None:
            cont.fn = self.value
        else:
            cont.fn = cont.fn.apply_argument(self.value)
        self.value = None

        assert cont.fn is not None

        if cont.args.is_cons():
            self.value, cont.args = cont.args.steal_children()
            self.is_result = False
            return

        if not cont.args.is_nil():
            self.value = Error("improper list in functional expression")
            return

        fin = cont.fn.apply_finish()
        cont.fn = None # dereffed by apply_finish

        if isinstance(fin, Element):
            self.value = fin
            self.is_result = True
        else:
            # XXX handling of "a"; probably don't want to do it this way
            env, fin = fin
            if env is None:
                self.value = fin
                self.is_result = False
            else:
                self.value = Error("cannot specify environment with a in symbolic mode")
                fin.deref()
                self.is_result = True

        self.popcont()

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
        # rewriting
        # (eval x) -> *x
        # (q x y z) --> (x y z) done
        # (if a b c) --> (eval (i a (q . b) (q . c)))

        if self.value.is_symbol() and self.value.val1 == 'q' and self.continuations and self.continuations[-1].fn is None:
            cont = self.continuations[-1]
            self.value.deref()
            self.value = cont.args
            self.is_result = True
            cont.args = None
            cont.localsyms.deref()
            self.popcont()
            return

        if self.value.is_error():
            if self.continuations:
                self.popcont()
                return
            self.is_result = True
        elif self.value.is_atom() or self.value.is_func():
            self.is_result = True

        if self.is_result:
            self.feedback()
            return

        if self.value.is_cons():
            self.value, t = self.value.steal_children()
            self.continuations.append(Continuation(args=t, localsyms=self.localsyms().bumpref()))
        elif self.value.is_symbol():
            sym = self.value.val2
            self.value = ResolveSymbol(self.localsyms(), self.globalsyms, sym)
            if self.value is None:
                self.value = Error(f"Unknown symbol {sym}")
            return
        else:
            raise Exception(f"unknwon element kind {self.value.kind}")

def symbolic_eval(sexpr, globalsyms):
    wi = WorkItem(value=sexpr.bumpref(), globalsyms=globalsyms)

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
        print(f" --- {self.wi.value}")
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
        s = SExpr.parse(arg)
        r = symbolic_eval(s, self.symbols)
        print(r)
        r.deref()
        s.deref()

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
            return
        elif self.wi.finished():
            print(f"Result: {self.wi.value}")
            self.wi.value.deref()
            self.wi = None
            return

        self.wi.step()
        self.show_state()

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

