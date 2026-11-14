---
slug: englander-a081215-xiv-cubic-remainders
bibkey: englander2020a081215
doi: null
url: https://oeis.org/A081215/a081215.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/SelfPowerQuotient
  - D5/S3/Arith/Congruence/SelfPowerCubicRemainders
---

# Englander's XIV: all six cubic least remainders

## Problem

[Physical page 63](https://oeis.org/A081215/a081215.pdf#page=63) of Mathew
Englander's *Comments on OEIS A081215* states
Conjecture XIV for every integer $n>2$. With the exact integer quotient
$a(n)=(n^{n+1}+(-1)^n)/(n+1)^2$, let $M=n^3-1$.
Twice the least nonnegative remainder of $a(n)$ modulo $M$ is
$n^3+n^2-n$, $n^3-2n^2+2n-1$, $n^3+3n^2-n-2$,
$n^3-2n^2+1$, $n^3+n^2+n-2$, or $n^3-1$, respectively for
$n$ congruent to $0,1,2,3,4,5$ modulo six.

## Motivation

This is the complete first-tier, externally numbered cubic conjecture.
All six branches and the full lower bound are retained. The exact quotient
is shared with the separate XVII assertion, while XX is outside the scope.

## Gap

[Preregistration #30323](https://github.com/the-omega-institute/trureturing/issues/30323)
records the full target and bounded literature/reuse boundary. The inspected
original source and current OEIS material did not supply a located complete
proof. Rubey–Yin's arXiv:2403.17110v3 gives a known parking-function
interpretation. No assertion of exhaustive worldwide openness or priority
follows from this bounded search.

## Route

For $S_j(y)=\sum_{i<j}y^i$ and $T_j(y)=\sum_{i<j}S_i(y)$, direct use
of Mathlib's geometric-sum identity gives
$T_j(y)(y-1)^2=y^j-1-j(y-1)$. At $j=n+1,y=-n$ this proves
$a(n)=(-1)^n(1-T_{n+1}(-n))$ and exact denominator divisibility.

Finite-sum splitting gives
$T_{j+k}=T_j+y^jT_k+kS_j$. The six-step block identity yields
$T_{6h+t}(y)\equiv3h(1+y+y^2)+T_t(y)\pmod{y^3+1}$ for every
natural $h,t$ and integer $y$. This is an unbounded induction, not a
finite-prefix test.

At $n=6h+c$, evaluating this congruence constructs the six integer
representatives printed in the source's $h$-form. Their differences from
$a(n)$ are explicit multiples of $M$; direct bounds place every
representative in $[0,M)$. Euclidean remainder uniqueness gives the least
remainder. Polynomial expansion identifies twice that value with the six
$n$-form branches. No cancellation of two modulo an even modulus is used.

## Falsifier

An allowed integer $n>2$ with a different exact quotient remainder would
contradict the full formal result. Omitting a branch, changing the lower
bound or assuming integrality would fail to address this problem.

## Evidence

The common sequence and integrality theorem are in
`SelfPowerQuotient.exact_quotient`. The uniform descent is
`SelfPowerCubicRemainders.tail_blocks`, and the full endpoint is
`SelfPowerCubicRemainders.result : SelfPowerCubicRemainders.claim`.
The claim includes both exact quotient identity and the six-branch
least-remainder equality. All arithmetic is over integers with natural
exponents; natural indices above two correspond exactly to the printed
integer domain. Corresponding canonical Blueprint sources spell out the
complete formulas and the integral representative argument.

## Triage

`theorem`: `SelfPowerCubicRemainders.result` proves the complete XIV
statement. The canonical Scribe resolution claim binds this endpoint to
`englander-a081215-xiv-cubic-remainders` with kind `Proved`.

**What the settlement shows.** Uniform six-step divisibility descent,
exact quotient integrality and representative bounds establish all six
least-remainder branches for every integer $n>2$. There is no parity,
primality or eventual-domain restriction. The shared quotient helpers are
consumed by this proof and supply no independent settlement. This result
does not settle the source's other numbered conjectures, including XX.
Any additional downstream consequence not established by these declarations
remains open.

The [definition on physical page 1](https://oeis.org/A081215/a081215.pdf#page=1)
and the six branches on physical page 63 are the authoritative source
statements. Source identity, bounded literature coverage and the unverified
PDF redistribution permission are given in the Library entry. Citation
and mathematical paraphrase do not assert worldwide priority.

## ASSUMED-UNVERIFIED

Worldwide priority and complete citation closure are unverified. Source
provenance and the PDF-specific license boundary are recorded in the
Library entry. No full PDF is redistributed. Search failures are
inconclusive. Audit validation and its current evidence are separate from
the mathematical theorem.
