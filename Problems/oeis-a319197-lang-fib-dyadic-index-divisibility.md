---
slug: oeis-a319197-lang-fib-dyadic-index-divisibility
bibkey: lang2018a319197
doi: null
url: https://oeis.org/A319197
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LangFibDyadicIndexDivisibility
---

# Dyadic divisibility at Lang's Fibonacci indices

## Problem

OEIS A319197 states in its NAME field:

> All entries from a(3) to a(n) appear in addition to 2^n as factors in the conjectured factorization of Fibonacci(2^(n-2)*3*m) for n >= 3 and all m >= 0.

The existing proved-resolution address
`D5/S1/Recurrence/LangFibDyadicIndexDivisibility.result` resolves exactly the
entry's first COMMENT sentence:

> It appears that Fibonacci(2^(n-2)*3*m)/(2^n) is a nonnegative integer for n >= 3 and all m >= 0.

Its theorem states that for natural numbers `n` and `m`, if `3 <= n`, then
`2^n` divides `Nat.fib (2^(n-2)*3*m)`. This includes `m = 0`;
natural-number subtraction in `n-2` agrees with ordinary subtraction under
`3 <= n`. Because `2^n` is positive, the divisibility statement is
equivalent to the quoted nonnegative-integral quotient assertion. That
address does not resolve the product factorization, its claimed sharpness,
or an exact two-adic valuation.

Its FORMULA field gives the sharper target:

> I(n; m) := F(2^(n-2)*3*m) / ((2^n)* Product_{j=3..n} a(j)) is conjectured to be a nonnegative integer for n >= 3 and all m >= 0, where F = A000045. There are no more factors > 1 for all m >= 0 because I(n, 1) = 1.

The power-of-two clause is true, but the claimed sharpness is false at
`n = 7`. With

$$D_7=2^7\cdot1\cdot9\cdot161\cdot51841\cdot6989569,$$

the corrected arithmetic is

$$
D_7=67205083036226688,
\qquad
F_{96}=51680708854858323072=769D_7.
$$

Equivalently,

$$F_{96}=2^7\cdot3^2\cdot7\cdot23\cdot47\cdot769\cdot1103\cdot2207\cdot3167.$$

Thus the listed level-seven product is a proper divisor of the uniform
divisor already obtained at `m = 1`.

## Motivation

The correction separates two statements. For every natural number `k` and
every integer `d`, published Fibonacci divisibility gives the exact
characterization

$$
\left(\forall m\in\mathbb N,\ d\mid F_{6\cdot2^k m}\right)
\quad\Longleftrightarrow\quad
d\mid F_{6\cdot2^k}.
$$

The forward direction is the case `m = 1`; for positive `m`, the reverse
direction uses `F_a | F_{am}`, while `m = 0` follows from `F_0 = 0`. This is
an immediate consequence of Jeffery--Pereira (2014), Proposition 6. Their
Theorem 7 also gives
`gcd(F_a,F_b)=F_gcd(a,b)`, although that stronger result is not needed here.

The power-of-two part is also settled: Lengyel (1995), Lemma 2 gives
`v_2(F_r)=v_2(r)+2` for every positive multiple `r` of `6`. In particular,
`v_2(F_{6\cdot2^k})=k+3` for every `k >= 0`.

## Gap

There is no remaining mathematical gap in the level-seven correction.
Define the true layers by

$$\ell_0=9,\qquad \ell_{k+1}=2\ell_k^2-1\quad(k\ge0).$$

These are not new: `ell_k = A081459(k+2)`. The recurrence was recorded by
Artur Jasinski on 2008-10-12, and Ehren Metcalfe recorded
`ell_k = Lucas(6*2^k)/2` on 2017-10-05. The first five values are

$$9,\ 161,\ 51841,\ 5374978561,\ 57780789062419261441.$$

OEIS A081460 gives

$$A081460(k+2)=F_{6\cdot2^k}/2$$

for every `k >= 0`; its Lucas-product formula, recorded by Amiram Eldar on
2023-04-07, yields

$$F_{6\cdot2^k}=2^{k+3}\prod_{0\le j<k}\ell_j.$$

At `k = 3`,

$$6989569\cdot769=5374978561=\ell_3,$$

so A319197's listed factor at external level seven omits exactly the prime
`769` from the true layer.

## Route

For each natural `k` and integer `d`, Jeffery--Pereira Proposition 6 supplies
the characterization over every natural multiplier `m`; its positive cases
come from `F_a | F_{am}`, the zero case from `F_0 = 0`, and the converse from
`m = 1`. Their Theorem 7 supplies the compatible Fibonacci gcd law. A081459
and A081460 supply the layer and product identities for every natural `k`.
Lengyel's valuation formula applies at each positive index `6*2^k`; under
`n = k+3`, it settles the power-of-two comment for every natural `n >= 3`.

The correction itself fixes external level `n = 7`, whose Fibonacci index
uses `k = 4` in `6*2^k`; the omitted factor belongs to layer `ell_3`.
Consequently it proves only `769 D_7 | F_{96m}` for every natural `m`, not a
claim about sharpness at every level. The published results above suffice
for the withdrawal.

## Falsifier

The level-seven correction would fail if any of the exact equalities

$$
F_{96}=51680708854858323072,
\quad
D_7=67205083036226688,
\quad
F_{96}/D_7=769,
\quad
6989569\cdot769=5374978561
$$

failed, or if some natural `m` satisfied
`769 D_7 \nmid F_{96m}`. The latter includes `m = 0`, where `F_0 = 0`.
This single external level `n = 7` (index parameter `k = 4`, omitted layer
`ell_3`) refutes the entry's sharpness claim without asserting failure at
any other level. Separately, the existing proved-resolution clause would be
falsified by natural numbers `n >= 3` and `m` for which
`2^n \nmid F_{2^(n-2)*3*m}`.

## Evidence

- Thomas Jeffery and Rajesh Pereira, *Divisibility Properties of the
  Fibonacci, Lucas, and Related Sequences*, ISRN Algebra 2014, Article
  750325, Proposition 6 and Theorem 7,
  DOI `10.1155/2014/750325`.
- OEIS A081459 records the layer recurrence and Lucas formula; OEIS A081460
  records `F(6*2^k)/2` and the Lucas-product formula.
- T. Lengyel, *The Order of the Fibonacci and Lucas Numbers*, Fibonacci
  Quarterly 33(3) (1995), 234--239, Lemma 2,
  DOI `10.1080/00150517.1995.12429139`.
- The arithmetic identities above agree with the full prime factorization
  of `F_96`; the factor `6989569` is `2207*3167`, and multiplying by `769`
  gives the true layer `ell_3`.
## Triage

Nothing in this correction is first-frozen, and the existing proved address
retains its original power-of-two scope. The exact common-divisor
characterization is dominated by Jeffery--Pereira, the layer recurrence and
product are published in A081459 and A081460, and the two-adic clause is
Lengyel's theorem. Those published results alone suffice for withdrawal.
The corrected sharpness question therefore does not qualify as an
unresolved external open problem. `admission_basis: none`; this dossier and
its Library sources are the complete disposition.

## ASSUMED-UNVERIFIED

The independent literature audit reported the same `769` witness in the
repository `umaia1234/agentic-conjectures`, commit
`fc19768996bd3c749f685e2399580fe678e86ebd`, whose recorded commit date is
2026-08-12. A commit date alone does not establish when the contents became
publicly available, and this pipeline did not independently verify public
availability on that date. This unverified chronology is unnecessary to the
withdrawal, which follows from the published results cited above.
