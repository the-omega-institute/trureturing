---
slug: arxiv-2610-00765-cube-recursion-family
bibkey: matijasevick2026squares
doi: 10.48550/arXiv.2610.00765
url: https://arxiv.org/abs/2610.00765v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/CubeRecursionFamily
  - D5/S3/Arith/CubeRecursionProjective
---

# A uniform family of reduced-coordinate cube recursions

## Problem

Matijasevick, Rodriguez and Salazar, *Perfect squares in reciprocal-sum
sequences and primes that are inert in quadratic fields*, arXiv:2610.00765v1,
Section 7, question 2, asks:

> For the recursions of this paper the exponent m=2 is forced. Is there a natural family of rational recursions for which c a_n+b_n is always a cube, other than those conjugate to z -> z^3?

The reduced-fraction convention is inherited from Problem 1.1: a_n,b_n are
coprime positive integers, starts are positive integers, c is positive rational,
and indices are n>=2. “Natural” is undefined. The explicit minimal reading here
is a uniform autonomous rational family over Q of fixed degree, parameterized
by a nonnegative integer, with one formula and a single c independent of the
parameter, initial value and index. An unstated stricter author intent is not
resolved by this reading.

For every t in N, including zero, put

$$F_t(x)=\frac{x+t}{(x+t+1)^3-(x+t)},\qquad x_n=F_t^{\circ n}(x_0).$$

The proved endpoint is: for every positive rational x_0, the intrinsic reduced
numerator a_n and denominator b_n are positive and coprime for every n>=0;
for every n>=1,

$$a_n+b_n=\bigl(a_{n-1}+(t+1)b_{n-1}\bigr)^3.$$

Thus c=1 works uniformly and the inherited integer starts and n>=2 follow.
Each map has degree exactly 3 and no M in PGL_2(C) has
M F_t M^{-1}(z)=z^3 on the entire projective line. No assertion at n=0 of
a cube sum, or classification of all cube recursions, is made.

## Motivation

The question asks whether its square phenomenon has a cubic analogue beyond
a coordinate copy of the power map. The exact question, quantifiers and Tier 1
classification were preregistered in issue
[#18920](https://github.com/the-omega-institute/trureturing/issues/18920).
The tier is a recent closing question with a complete elementary constructive
route, rather than a central longstanding conjecture.

## Gap

The supplied ordinary qualification read the complete primary source and
relevant scope passages of Jones--Manes arXiv:1101.4339v3 and
Cahn--Jones--Spear arXiv:1512.03085v2. The former's displayed families have
degree two; the latter studies rational values that are powers. Neither
inspected scope supplies the whole assertion about reduced numerator plus
denominator. In particular F_0(1)=1/7 has sum 8 while its value is not a
rational cube. The primary source's reciprocal-sum argument forcing squares
does not range over this cubic family.

No equivalent whole answer was identified in the supplied bounded comparison.
The primary source's two companion preprints were unlocated. Global priority
is UNDETERMINED. This is not an exhaustive literature finding. An attributable
equivalent whole answer, if located, removes new-resolution eligibility and
routes to reuse. The repository and pinned-Mathlib searches did not identify
an existing whole theorem. Existing rational reduction, polynomial gcd,
projectivization and PGL action APIs are reused directly.

## Route

For a,b positive coprime integers let u=a+tb and w=u+b. Substitution gives

$$F_t(a/b)=N/D,\quad N=ub^2,\quad
D=w^3-ub^2=u^3+3u^2b+2ub^2+b^3.$$

Both entries are positive. Since gcd(u,b)=1, w is coprime to u and b, so
N is coprime to w^3 and hence to D. Mathlib's canonical rational numerator
and denominator lemmas identify N,D with the actual reduced pair. Their sum
is w^3. Induction applies this exact reduction to every positive rational
iterate without a finite-orbit assumption.

The complex polynomials x+t and (x+t+1)^3-(x+t) are coprime, with monic cubic
denominator. The true map degree is the maximum of their reduced degrees,
1 and 3; RatFunc.intDegree, their difference, is not used. The homogeneous
pair is

$$P_t(X,Y)=(X+tY)Y^2,\quad
Q_t(X,Y)=(X+(t+1)Y)^3-(X+tY)Y^2.$$

It has no common zero at any nonzero pair (X,Y). The coordinate theorem
identifies its projectivization with the full OnePoint(C) map, including
infinity and poles. The rational-function evaluation theorem identifies the
affine chart; the rational orbit theorem identifies the rational iterates
with that same projective map. The PGL action is the actual Mathlib action
transported through the canonical projective-line equivalence. Every PGL
class has a GL representative, and the coordinate theorem proves the usual
fractional-linear formulas at finite points, poles and infinity.

The zero fibre of F_t has exactly two points, -t and infinity. In contrast,
if two distinct points have equal images under the cubic power map, a third
point has the same image. For finite u,v the third root is -u-v; the
factorization of u^3-v^3 proves its image and distinctness. Infinity has a
singleton power-map fibre. Bijections preserve these fibre properties, so
no element of the full PGL_2(C) conjugates F_t to the power map. This proof
uses no analytic critical-point formalization or unproved normal form.

The admission basis is `open-problem-resolution` under #18920. The result is
the single source settlement; the remaining public theorems are consumed
reduction and projective bridges. Their proof shape is conservatively
`bind-only`: existing arithmetic and projective APIs, algebraic normalization,
logical combination and induction supply the chain. No escape-witness claim
is used to admit an unconsumed wrapper. Utility is `none`: the proofs are
unbounded symbolic results, not a finite enumeration, checker, numeric
reduction or certified finite instance.

## Falsifier

A nonnegative t and positive rational start with a nonpositive iterate or an
incorrect intrinsic reduced-pair identity at any n>=1 would refute the
endpoint. A degree below 3 after true polynomial reduction, a common
homogeneous zero, a failure of chart correspondence, or an actual complex
PGL conjugacy to the power map would also refute it. Testing finitely many
orbits cannot establish these universal claims.

## Evidence

The native source endpoint is `D5/S3/Arith/CubeRecursionFamily.result` with
claim definition `originalClaim`. It includes intrinsic positive reduced
pairs, all positive rational starts, every n>=1, degree 3, full rational-map
and homogeneous-coordinate semantics, every PGL representative, the
fractional-linear action and nonconjugacy. The projective bridges live in
`D5/S3/Arith/CubeRecursionProjective`. No numerical experiment is a premise.
Kernel verification, axiom closure, audit status and admission are distinct
obligations; mathematical compilation does not certify priority or completion
of independent reviews, freezing or required CI.


The information-escape audit is unfinished. All eight same-author compiled
registration attempts remain `declared_unresolved`, with `certificate: null`
and `IE-C050 ClosedTruthReadout reason=unclassified_form`. The actual published
issue [#18969](https://github.com/the-omega-institute/trureturing/issues/18969)
discloses the missing source bindings; publication is not validation.

| Original theorem | Missing binding |
| --- | --- |
| `D5.S3.Arith.CubeRecursionFamily.reduced_step` | `source.selection_missing` |
| `D5.S3.Arith.CubeRecursionFamily.positive_orbit_cube` | `source.selection_missing` |
| `D5.S3.Arith.CubeRecursionFamily.result` | `source.residual_requires_open` |
| `D5.S3.Arith.CubeRecursionProjective.map_degree_three` | `source.selection_missing` |
| `D5.S3.Arith.CubeRecursionProjective.homogeneous_coordinates` | `source.selection_missing` |
| `D5.S3.Arith.CubeRecursionProjective.rational_map_semantics` | `source.selection_missing` |
| `D5.S3.Arith.CubeRecursionProjective.not_conjugate` | `source.selection_missing` |
| `D5.S3.Arith.CubeRecursionProjective.mobius_coordinates` | `source.selection_missing` |

The seven absent selections still require faithful compiler readout-occurrence
selectors, source-coordinate selection, full-statement reconstruction,
state/escape identity and current binding evidence. The aggregate result's
residual/reconstruction binding remains unresolved. An explicitly unknown
continuation supplies neither those bindings nor a validation certificate.
The mathematical proof terms and the author's Reg attempts are retained.
No native acceptance or solve credit is claimed.

## Triage

`theorem`; mathematical resolution `proved` under the stated interpretation.
Independent source/judgement review and canonical repository admission remain
separate from the construction and proof.

### What the settlement shows

- **Proved**, `D5/S3/Arith/CubeRecursionFamily`: the no-cancellation mechanism
  gives a cube already at the first step from every positive rational start,
  strengthening the inherited positive-integer/n>=2 domain.
- **Proved**, `D5/S3/Arith/CubeRecursionProjective`: the two-point fibre is
  incompatible with the cubic power map under every projective change of
  coordinates. Affine nonconjugacy alone is not the conclusion.
- **Open**: any stricter intended meaning of “natural,” classification of all
  such recursions, and the other closing questions. The source's square
  theorems concern a different class and remain unchanged. No conclusion
  depending on a hypothetical negative answer to question 2 is used.

## ASSUMED-UNVERIFIED

The ordinary qualification supplies bounded source and literature readings;
worldwide originality and the unlocated companion works are unverified.
No claim of global priority, accepted solve credit, full repository checks,
completed four-slot source binding or frozen status follows from the prose.
