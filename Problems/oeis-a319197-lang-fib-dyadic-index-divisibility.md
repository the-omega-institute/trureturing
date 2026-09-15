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

The correction separates two statements. For every integer `k >= 0` and
every integer `d`, published Fibonacci divisibility gives the exact
characterization

$$
\left(\forall m\in\mathbb N,\ d\mid F_{6\cdot2^k m}\right)
\quad\Longleftrightarrow\quad
d\mid F_{6\cdot2^k}.
$$

The forward direction is the case `m = 1`; the reverse direction uses
`F_a | F_{am}`. This is an immediate consequence of Jeffery--Pereira
(2014), Proposition 6. Their Theorem 7 also gives
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

The characterization is supplied by Jeffery--Pereira's published
Fibonacci divisibility theorem. The layer recurrence and Lucas description
are supplied by A081459, while A081460 supplies the Fibonacci value and
Lucas-product formula. Lengyel's valuation formula settles the separate
power-of-two comment. Together these published results determine every
quantified statement above for all `k >= 0` and all `m >= 0`.

The same `769` witness was disclosed in the public repository
`umaia1234/agentic-conjectures`, commit
`fc19768996bd3c749f685e2399580fe678e86ebd`, repository-dated 2026-08-12.
The prime also appears in Lang's 2018-10-09 factorization of `a(9)` in
A319197, but not in the entry's listed `a(7)`.

## Falsifier

The correction would fail if any of the exact equalities

$$
F_{96}=51680708854858323072,
\quad
D_7=67205083036226688,
\quad
F_{96}/D_7=769,
\quad
6989569\cdot769=5374978561
$$

failed, or if a cited source did not contain the stated universally
quantified divisibility, recurrence, product, or valuation result. The
level-seven counterexample does not assert failure at every level: it
refutes the entry's universal sharpness claim by the single case `n = 7`,
and its all-multiplier conclusion is only
`769 D_7 | F_{96m}` for every `m >= 0`.

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
- The repository-dated prior disclosure contains the same level-seven
  witness in commit `fc19768996bd3c749f685e2399580fe678e86ebd`.

## Triage

Nothing in this correction is first-frozen. The exact common-divisor
characterization is dominated by published Fibonacci divisibility, the
layer recurrence and product are published in A081459 and A081460, the
two-adic clause is Lengyel's theorem, and the level-seven witness has a
repository-dated public disclosure predating this dossier. The named
conjecture therefore does not qualify as an unresolved external open
problem. `admission_basis: none`; this dossier and its Library sources are
the complete disposition.

## ASSUMED-UNVERIFIED

The 2026-08-12 date attached to commit
`fc19768996bd3c749f685e2399580fe678e86ebd` is a repository-dated
disclosure. It establishes prior art within the searched scope, but no
independent first-publication timestamp for that repository content is
claimed.
