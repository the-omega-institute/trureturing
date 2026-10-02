#!/usr/bin/env python3
"""Exact endpoint audit for a pure three-cycle CFMP (8,9) static box.

Box: low x in [73/50,2], high x in [53/40,347/200].
The six-variable cosine is the Zhao/Luo--Yang formula. For a cycle packet,
monotonicity reduces each target's lower/upper face to four displayed tuples.
This script checks all signs over Q and bounds cos(2*pi/9) by its cubic root.
"""
from fractions import Fraction as F

A = F(73,50)       # low lower
B = F(2)           # low upper
C = F(53,40)       # high lower
D = F(347,200)     # high upper


def phi_sq(x1,x2,x3,x4,x5,x6):
    AA = 2*x1*x2*x6 + x1*x1 + x2*x2 + x6*x6 - 1
    BB = 2*x1*x3*x5 + x1*x1 + x3*x3 + x5*x5 - 1
    P = x2*x3 + x5*x6 + x1*x2*x5 + x1*x3*x6 - (x1*x1 - 1)*x4
    assert P > 0 and AA > 0 and BB > 0
    return P*P/(AA*BB)

# cos(2*pi/9)=cos(40 degrees) is the unique root q in (0.7,0.8)
# of f(q)=8q^3-6q+1. On [3/4,4/5], f' = 24q^2-6 > 0.
Qlo, Qhi = F(766044,10**6), F(766045,10**6)
def f(q): return 8*q**3 - 6*q + 1
assert f(Qlo) < 0 < f(Qhi)
assert 24*F(3,4)**2 - 6 > 0

vals = {
    # low target lower/upper faces
    "L_lower": phi_sq(A,A,C,D,C,A),
    "L_upper": phi_sq(B,B,D,C,D,B),
    # high target lower/upper faces
    "H_lower": phi_sq(C,A,A,B,C,C),
    "H_upper": phi_sq(D,B,B,A,D,D),
}
assert vals["L_lower"] > F(1,2)
assert vals["L_upper"] < F(1,2)
# Positivity lets us compare phi with q by squaring.
assert vals["H_lower"] > Qhi*Qhi
assert vals["H_upper"] < Qlo*Qlo

print("PASS pure-cycle (8,9) endpoint certificate")
for k,v in vals.items(): print(k, v, float(v))
print("f(Qlo), f(Qhi)=", f(Qlo), f(Qhi))
print("Margins:")
print("L_lower - 1/2 =", vals["L_lower"]-F(1,2))
print("1/2 - L_upper =", F(1,2)-vals["L_upper"])
print("H_lower - Qhi^2 =", vals["H_lower"]-Qhi*Qhi)
print("Qlo^2 - H_upper =", Qlo*Qlo-vals["H_upper"])
