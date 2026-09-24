---
bibkey: bugeaud2006lebesguenagell
authors: Yann Bugeaud, Maurice Mignotte, Samir Siksek
year: 2006
title: Classical and modular approaches to exponential Diophantine equations II. The Lebesgue-Nagell equation
doi: 10.1112/S0010437X05001739
claim: Theorem 1 and the empty D=3 row in Section 16 exclude integer solutions of x^2+3=y^e for e>=3; this supplies a common-depth obstruction on the actual fixed-golden Lucas blocks.
strata_touched: []
license: citation-only
triage: anchor
---

# Lebesgue-Nagell input for actual golden initial-depth vectors

## Verified primary locator

Y. Bugeaud, M. Mignotte and S. Siksek, *Classical and modular approaches to
exponential Diophantine equations II. The Lebesgue-Nagell equation*,
Compositio Mathematica 142 (2006), 31-62.

https://doi.org/10.1112/S0010437X05001739
https://arxiv.org/abs/math/0405220
https://arxiv.org/pdf/math/0405220

The input is Theorem 1, covering x^2+D=y^e for integers x,y and e>=3,
together with Section 16's complete tables. The D=3 row has no solution.
The table is on printed page 47 of the author preprint; that page was
inspected as an image, and the theorem and scope were read in the primary
text. The publisher record fixes the journal citation above. The classical
D=3 case is attributed to Nagell in Section 2. This note does not claim
that this classical special case originated in 2006, or reproduce the
full proof of the classification.

## Exact use in the WSS owner

`docs/develop/theory/WALL_SUN_SUN_GOLDEN_UNIT_RESEARCH.md`, DCE.1-DCE.2,
combines that
published theorem with elementary factorization at e=2. For x>=2,
x^2+3 is therefore not a perfect power. Apply it to x=L_(3^j), j>=1.
TBN.3 separately proves that every prime factor of the actual block
B_j=L_(3^j)^2+3 occurs with its ORIGINAL Fibonacci initial depth h_p.
Consequently gcd{h_p:p|B_j}=1 for every j. No index-generated square is
being counted as an initial anomaly.

DCE.2 also shows that for every fixed e>=2 there are infinitely many
split primes of exact Fibonacci ranks 2*3^s, s>=2, whose initial depth is
not divisible by e. It does not show that infinitely many of them have
depth one, or that any have depth at least two. The common gcd of all
depths in each tail of this particular prime-support family is one.

DCE.3 proves the resulting all-depth covering budget: if every depth in
a block is at least H>=2, the total multiplicity is at least 2H+1. Equality
forces two distinct primes with depths H,H+1. For H=2 the only possible
fivefold all-WSS pattern is P^2 Q^3; the existing block balances further
require Q=19 modulo40 and the stated exact ternary class of P. These are
proved specializations using the actual block, not claims made by the
source paper or a constructed WSS example.

DCE.4 excludes every pure odd-prime-power input p^a, a>=2, from the fixed
D=5 fibre of McConnell's varying-field dimension map. Odd dimension
indices use this D=3 input; even indices use two coprime factors L_n-1
and L_n+1. This extends the earlier square-seed obstruction without using
Catalan's theorem. It excludes a family of construction inputs, not the
same rational primes from the WSS set.

## Mathematical and formal boundaries

Non-perfect-power and non-powerful are different conclusions. A mixed
exponent vector such as (2,3) has gcd one and has no simple prime factor.
Neither this source nor DCE turns gcd one into the assertion that an
individual original h_p is one. Mixed-depth covering is the remaining
branch and is explicitly retained.

The cited classical theorem is an external premise of the ordinary DCE
proof. No new Lean declaration, kernel certification, first-discovery
claim, solved external problem, or actual WSS prime-family decision is
attached to this note. The existing trace-image Scribe links this result
only as related ordinary arithmetic in its owner's research line; its
formal theorem has no new conclusion about these Diophantine blocks.
