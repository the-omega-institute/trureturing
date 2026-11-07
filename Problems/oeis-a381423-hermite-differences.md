---
slug: oeis-a381423-hermite-differences
bibkey: sheppard2025a381423
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Polynomial/HermiteSignedMode.result
url: https://oeis.org/A381423/internal
---

## Problem

OEIS A381423 revision 8, Mike Sheppard, has the independent conjecture clause:
“Differences are either 1 or -3”. Its full comment continues with finer patterns,
spacing and square-root growth. The independent target is preregistered at
[#25634](https://github.com/the-omega-institute/trureturing/issues/25634).

For every natural n, including zero, let a(n) be the smallest j in zero through n
maximizing the signed coefficient of $x^j$ in the physicists Hermite polynomial
$H_n$. The exact assertion is

$$ (a(n+1):\mathbb Z)-(a(n):\mathbb Z)=1\quad\text{or}\quad-3. $$

The source's Mathematica first PositionLargest and PARI upward scan establish
the tie convention. Its n=5 example selects exponent 1, distinguishing signed
order from absolute coefficient order.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Physicists H_n | `physicistsHermite n`, the literal DLMF 18.5.13 finite factorial expansion over ℚ. |
| Coefficient at exponent j | `polynomial_coeff` proves extraction equals `signedCoeff n j` throughout zero through n. |
| Signed maximum | `IsSmallestMax` compares rational coefficients directly, with no absolute value. |
| Smallest tied exponent | The last conjunct of `IsSmallestMax`; the proof chooses the largest positive-term index. |
| Every n, including zero | Unrestricted `∀ n : ℕ` in both conjuncts of `claim`. |
| Integer difference | Both values of `a` are cast to ℤ before subtraction. |
| No uniqueness assumption | No assumption is present; all tied maximizers enter the selector predicate. |

## Motivation

Alternating signs restrict a positive signed maximum to exponents congruent to
n modulo four. Their adjacent coefficient ratios identify a threshold that
moves by at most one lattice site when n increases by one.

## Gap

The supplied research screen found no exact settlement in its inspected
OEIS/DLMF material, the bounded portions of Bonneux–Dunning–Stevens
arXiv:1909.03874v2, or Dudeja–Hsu Lemma 35. The latter concerns a normalized
absolute coefficient bound. No global openness or priority claim follows.

The local statement search covered public and private D5 Hermite declarations,
the corresponding theory sources and pinned Mathlib at
56a005855ea17e0b0958f73ec801ae140b0a1679. Mathlib's explicit Hermite formulas
use probabilists normalization. Existing Jensen top-coefficient suppliers also
use that convention; no private exposure is required for this proof.
Bounded GitHub Lean searches for A381423, Hermite argmax and Hermite unimodal
returned zero code hits. These are bounded searches, not exhaustive ecosystem
or literature coverage. Generic finite extrema and factorial identities are
reused; no exact matching transition theorem was found in the searched scope.

## Route

Set $j=n-4r$ and

$$ w(n,r)=\frac{2^{n-4r}}{(2r)!\,(n-4r)!},\qquad 4r\le n. $$

The signed coefficient at this exponent is $n!w(n,r)>0$. Every other
coefficient is nonpositive. The exact adjacent relation, whenever
$4(r+1)\le n$, is

$$
w(n,r+1)16(2r+2)(2r+1)
=w(n,r)(n-4r)(n-4r-1)(n-4r-2)(n-4r-3).
$$

Define the threshold predicate at r by

$$
4r\le n,\qquad
16(2r)(2r-1)\le
(n-4r+1)(n-4r+2)(n-4r+3)(n-4r+4).
$$

Zero satisfies it. Its true indices form an initial segment: the left side
increases with r and the right side decreases. Let m(n) be the largest true
index. For r at most m(n), the weights rise weakly; past m(n), they fall
strictly. Induction gives global maximality and strict exclusion of every
larger r. Thus $a(n)=n-4m(n)$ is precisely the smallest exponent among signed
maximizers, including any ties.

Every true threshold for n remains true for n+1. Conversely, a true threshold
at r+1 for n+1 implies a true threshold at r for n: its left side decreases,
and the right-side argument increases by three. Hence
$m(n)\le m(n+1)\le m(n)+1$. Substituting into $a(n)=n-4m(n)$ proves the
integer difference assertion for all n. The endpoint constraints make each
natural subtraction agree with ordinary subtraction in these calculations.

## Falsifier

A natural n and the two actual smallest signed maximizers with integer
difference outside {1,-3} would refute the assertion. Finite testing, an
absolute coefficient selector, a probabilists polynomial, or a uniqueness
assumption would not establish this target.

## Evidence

`HermiteSignedMode.result : claim` includes both the exact selector certificate
and the universal difference assertion.

The source-owner Reg mirror observes the complete natural sequence. Its law
preserves the selector and every integer difference. The constant-zero family
violates the difference law at zero and supplies whole-family variation and
one-role sensitivity. The actual sequence has different observations at zero
and one, directly from the proved nonzero difference. Continuation is unknown;
no undecidability or inexhaustibility conclusion follows.

## Triage

Proved: the threshold mechanism gives a rightmost positive-term mode whose
index moves by zero or one; the smallest maximizing exponent therefore moves
by one or minus three. This proof handles ties without settling their absence.
The coefficient formula defines the actual physicists polynomial directly;
no unproved invariance of argmax under rescaling is used.

Unresolved and outside this independent target: the fine patterns
(1,1,1,-3) and (1,1,1,1,-3), their proposed spacing, square-root asymptotics,
and the source's separate uniqueness assertion. No dependent source theorem
requiring these finer assertions is established by this result. The threshold
method suggests related mode interlacing questions, which require separate
statements and eligibility decisions.

## ASSUMED-UNVERIFIED

Literature completeness and global priority remain unverified because the
source screen is bounded. The unknown audit continuation supplies no further
mathematical conclusion.
