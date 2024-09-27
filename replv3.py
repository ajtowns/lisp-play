#!/usr/bin/env python3

import cmd
import functools
import os
import sys
import traceback

try:
    import readline
except ImportError:
    readline = None

from dataclasses import dataclass, field
from typing import Optional, Tuple, List, Any, Self

from element2 import SExpr, Atom, ALLOCATOR
import symbll

##########

# To do:
#
#  * make bll evaluation work
#  * make compilation work
#
#  * all the opcodes
#  * implement op_partial
#  * default values for fn arguments
#  * defconst for compile-time constants (with quote support)
#  * quasiquote support
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

class BTCLispRepl(cmd.Cmd):
    HISTPATH = "~/.replv3.history"
    HISTSIZE = 2000

    @classmethod
    def histpath(cls):
        return os.path.expanduser(cls.HISTPATH)

    def __init__(self, prompt=None):
        self.prompt = ">>> " if prompt is None else prompt
        self.symbols = symbll.SymbolTable()
        self.wi = None

        cmd.Cmd.__init__(self)

    def preloop(self):
        if readline and os.path.exists(self.histpath()):
            readline.read_history_file(self.histpath())

    def postloop(self):
        if readline:
            readline.set_history_length(self.HISTSIZE)
            readline.write_history_file(self.histpath())

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
        r = symbll.symbolic_eval(s, self.symbols)
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
        self.wi = symbll.WorkItem.begin(sexpr, self.symbols)
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
            self.symbols.set(sym.val2, (Atom(0), val.bumpref()))
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

