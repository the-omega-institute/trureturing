---
bibkey: bugeaud2006fibonaccipowers
authors: Yann Bugeaud; Maurice Mignotte; Samir Siksek
year: 2006
title: Classical and modular approaches to exponential Diophantine equations I. Fibonacci and Lucas perfect powers
doi: 10.4007/annals.2006.163.969
url: https://arxiv.org/pdf/math/0403046v1
claim: Theorem 2 classifies the only Lucas perfect powers as L_1 = 1 and L_3 = 4; in particular, L_k is not a square for k >= 5.
strata_touched: []
license: citation-only
triage: anchor
---

# Lucas square exceptions in the character slice

The published article is in *Annals of Mathematics* 163 (2006), 969–1018.
Theorem 2 on printed page 971 (PDF page 3) defines `L_0 = 2`, `L_1 = 1`,
`L_(n+2) = L_(n+1) + L_n` for `n >= 0`, and states that its only perfect
powers are `L_1 = 1` and `L_3 = 4`. The authors' arXiv version states the
same theorem on PDF page 2. Both full-text versions were checked.

FIB theory §180.3 uses only the consequence that `L_k` is nonsquare for
odd `k >= 5`. This removes the possible principal character from the
source `D = (-1)^b L_(a-b)` at those gaps. The remaining gap three has the
elementary factorization `F_(b+3) + F_b = 2 F_(b+2)` and is treated by
the existing Fibonacci-factor estimate.

The uniform Robin-ratio deduction for gaps `o(log a)` is a project
combination with the character Euler-weight estimate; it is not a theorem
attributed to this article. The article does not supply a bound for all
opposite-parity gaps, arbitrary ATOM norms, or the Riemann hypothesis.
In particular, its Lucas-square classification does not exclude the
primitive ATOM composition `(16,29)`, whose negative golden norm is 121.
