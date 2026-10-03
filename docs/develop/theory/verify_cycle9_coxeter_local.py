#!/usr/bin/env python3
"""Exact finite-local audit for the [4,9,3] six-sector CFMP (8,9) construction.

No floating point, no random search, no external packages. This checks the
Coxeter relators, faithful images of every maximal finite special subgroup,
and local block counts. It does not enumerate the full finite quotient G,
compute its order, prove Coxeter development/Selberg/Tits theorems, or verify
a listed N=24 face-pairing.
"""
from fractions import Fraction
from itertools import combinations

P = 17
DIM = 4
I = tuple(int(i == j) for i in range(DIM) for j in range(DIM))

def mul(A, B):
    return tuple(sum(A[DIM*i+k]*B[DIM*k+j] for k in range(DIM)) % P
                 for i in range(DIM) for j in range(DIM))

def power(A, n):
    R = I
    while n:
        if n & 1:
            R = mul(R, A)
        A = mul(A, A)
        n //= 2
    return R

def subgroup(gens, max_size):
    seen, todo = {I}, [I]
    while todo:
        x = todo.pop()
        for gen in gens:
            y = mul(x, gen)
            if y not in seen:
                seen.add(y)
                todo.append(y)
                assert len(seen) <= max_size, "subgroup exceeded claimed finite order"
    return seen

# Canonical reflection matrices: r_i(e_j)=e_j+q_ij e_i, r_i(e_i)=-e_i.
# q_ab=2cos(pi/4)=sqrt(2), q_bc=2cos(pi/9), q_cd=1.
# The coefficient specialization sqrt(2)->6, 2cos(pi/9)->3 is mod17:
assert (6*6 - 2) % P == 0
assert (3**3 - 3*3 - 1) % P == 0
q = [[0,6,0,0],[6,0,3,0],[0,3,0,1],[0,0,1,0]]
R = []
for i in range(DIM):
    entries = list(I)
    for j in range(DIM):
        entries[DIM*i+j] = (P-1 if i == j else q[i][j])
    R.append(tuple(entries))
a,b,c,d = R
m = {(0,1):4,(1,2):9,(2,3):3,(0,2):2,(0,3):2,(1,3):2}
for x in R:
    assert mul(x,x) == I
for pair, order in m.items():
    x = mul(R[pair[0]], R[pair[1]])
    assert power(x,order) == I
    assert all(power(x,k) != I for k in range(1,order))

# The only maximal finite special subsets of [4,9,3]:
# abd = I2(4) x A1; acd = A1 x I2(3); bc = I2(9).
H_low = subgroup([a,b,d], 16)
H_base = subgroup([a,c,d], 12)
H_high = subgroup([b,c], 18)
K = subgroup([c,d], 6)
assert len(H_low) == 16
assert len(H_base) == 12
assert len(H_high) == 18
assert len(K) == 6
assert H_low & K == {I,d}
assert H_high & K == {I,c}
assert H_base & K == K
assert len(H_low) // len(H_low & K) == 8
assert len(H_high) // len(H_high & K) == 9
assert len(H_base) // len(H_base & K) == 2

# Full-face consistency: a commutes with K, b with the side stabilizer d.
assert all(mul(a,k) == mul(k,a) for k in K)
assert mul(b,d) == mul(d,b)

# Exact angle sums, in units of pi.
alpha, beta = Fraction(1,4), Fraction(2,9)
assert 8*alpha == 2 and 9*beta == 2
assert 3*beta == Fraction(2,3) < 1
assert 2*alpha+beta == Fraction(13,18) < 1
assert Fraction(1,4)+Fraction(1,9)+Fraction(1,2) == Fraction(31,36) < 1
assert Fraction(1,9)+Fraction(1,3)+Fraction(1,2) == Fraction(17,18) < 1

print("PASS: [4,9,3] Coxeter relations and exact local images mod 17")
print("Maximal spherical special subgroup orders: abd=16, acd=12, bc=18")
print("K order=6; intersections: low=2, high=2, base=6")
print("Block incidences: low midpoint=16/2=8, high=18/2=9, base center=12/6=2")
print("Whole-face commuting relations and target/link angle sums: PASS")
print("No full finite quotient order, minimum tetrahedron count, or N=24 claim")
