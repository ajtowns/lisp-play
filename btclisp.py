#!/usr/bin/env python3

import verystable.core.messages

from element import SExpr
from funcs import Set_GLOBAL_TX, Set_GLOBAL_TX_INPUT_IDX, Set_GLOBAL_TX_SCRIPT, Set_GLOBAL_UTXOS

from replv2 import Rep, Compiler

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
