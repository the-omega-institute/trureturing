---
slug: oeis-a189733-curtz-denominator-conjecture
bibkey: curtz2011a189733
doi: null
url: https://oeis.org/A189733
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.result
---

# Curtz's six-residue denominator conjecture

## Problem

OEIS A189733, revision 36, states:

> a(n) = denominator(B(0,n)). Conjecture: a(6*n)=1, a(1+6*n)=1+3*n, a(2+6*n)=1+2*n, a(3+6*n)=2+3*n, a(4+6*n)=1, a(5+6*n)=6+6*n. a(n) = 2*a(n-6) - a(n-12).

All indices are natural numbers. Define the actual rational triangle by
T(m,0)=0, T(m,1)=(-1)^m/(m+1), and
T(m,k+2)=T(m,k+1)+T(m+1,k), with boundary cases taking precedence.
The public `triangle` implements these three branches, and the public `a`
is exactly its zeroth-row reduced denominator. In particular, a zero
rational has denominator one. The theorem `result` is the equality of
the six-tuples for every natural k, including zero, with no extra premise.

## Motivation

This is Paul Curtz's externally named OEIS conjecture. Its exact statement
and quantifiers appear in issue
[#25342](https://github.com/the-omega-institute/trureturing/issues/25342).
The proof concerns the six formulas; no separate theorem about the entry's
empirical generating function or the lower-triangular extension is claimed.

## Gap

The directly read source JSON, revision 36, still labels the six formulas
as a conjecture and supplies no proof annotation. The bounded literature
screen recorded in #25342 checked arXiv and related entries A189731 and
A242926. No prior exact settlement was found by identifier and structural searches
in the repository, including private Lean declarations, or by authenticated
GitHub Lean code search for A189733. Pinned Mathlib provides the
finite polynomial sums, derivative rules and reduced-rational denominator
lemmas, but no source-triangle identity. Unindexed proofs and worldwide
priority remain unverified; this is not an exhaustive literature claim.

## Route

Use Q(0)=0, Q(1)=1, Q(n+2)=Q(n+1)-X Q(n). The finite coefficient
moment J(m,P) sums coeff(P,i)/(m+i+1) over the support. Multiplication
by X increments the moment index, proving T(m,n)=(-1)^m J(m,Q(n))
by the literal recursion.

The companion polynomials start at L(0)=2 and L(1)=1 with the same
recurrence. Their identity L(n+1)=Q(n+1)-2X Q(n) proves
L'(n+1)=-(n+1)Q(n). Applying J(0,.) to the derivative yields the
endpoint difference. Since L(n+1)(0)=1, this gives
T(0,n)=(1-L(n+1)(1))/(n+1).

The recurrence at X=1 has period six, with values 2,1,-1,-2,-1,1.
Consequently the zeroth-row values are respectively
0, 1/(3k+1), 1/(2k+1), 1/(3k+2), 0, and -1/(6k+6).
All displayed nonzero denominators are positive, so reduction gives
the six claimed denominators.

## Falsifier

A natural index k for which the six actual reduced denominators differ
from the displayed tuple would refute the assertion. The zeroth-row
values and denominators are taken from the literal recursive array,
including the denominator-one convention for zero.

## Evidence

The source-triangle moment identity and the companion derivative identity
are intermediate propositions on the proof path to the public theorem
`D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.result`.
The argument derives an exact formula for every natural index before
extracting reduced denominators; no finite table supplies the universal claim.

## Triage

Theorem: the target consists of all six formulas, universally over Nat.
The associated formal assertion has no cutoff and no additional hypothesis.

## ASSUMED-UNVERIFIED

No exhaustive literature coverage or worldwide priority is asserted.
Unindexed proofs remain outside the bounded source and literature screen
recorded in issue #25342. The generating-function comment and the
lower-triangular extension are outside this resolution.
