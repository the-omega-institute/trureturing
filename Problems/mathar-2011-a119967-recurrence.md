---
slug: mathar-2011-a119967-recurrence
bibkey: mathar2011a119967
doi: null
url: https://oeis.org/A119967/internal
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MatharA119967Refutation
---

# The literal A119967 recurrence

## Problem

OEIS A119967, FORMULA fields, verbatim:

> a(n) = sum{k=0..floor(n/2), C(n,2k)*C(k,floor(k/2))}.
>
> Conjecture: (n+2)*(n-3)*a(n) +(2+2*n-n^2)*a(n-1) +(3*n-5)*(n-2)*a(n-2) -(n-2)*(n-3)*a(n-3) -(n-2)*(n-3)*a(n-4)=0. - _R. J. Mathar_, Nov 14 2011

Write L(n) for this signed left side. The source prints no onset. The
literal valid-lag reading is ∀n≥4, L(n)=0. The eventual reading is
∃N≥4, ∀n≥N, L(n)=0. Both use the original finite sum and coefficients.

## Motivation

This first-tier named OEIS conjecture connects a nonnegative binomial
transform to a signed polynomial recurrence. A failure at one index
excludes the first reading; excluding every eventual onset requires an
all-index argument. The result concerns the printed event, with no
claim about an intended sign correction or priority.

## Gap

The bounded original-entry and full history-listing checks found no
complete proof or refutation. Supplied jOEIS and paper comparisons found
sequence computation and generic methods, not a full answer to this
literal event. Current exact repository/issue searches found no matching
owner or existing formalization before preregistration #30175.
The Library note gives source locators and the limits of these findings.

## Route

All summands are nonnegative and the k=0 term is one. Monotonicity of
C(n,2k) and inclusion of summation ranges imply a(n)≥a(n-1)≥1.
For n≥4, put A=(n+2)(n-3) and D=(n-2)(n-3). Then

L(n) = A(a(n)-a(n-1)) + (n-4)a(n-1)
       + D(a(n-2)-a(n-3)) + D(a(n-2)-a(n-4))
       + (n-2)(n+1)a(n-2).

Every term is nonnegative and the last is positive. Thus L(n)>0 for
every n≥4. At n=4 the values 1,1,2,4,9 and coefficients 6,-6,14,-2,-2
give L(4)=54. At any proposed later onset N, positivity of L(N)
contradicts the claimed zero.

## Falsifier

A nonpositive L(n) at any n≥4 would falsify the all-index positivity
claim. A mismatch in a summation limit, binomial operand, lag, cast or
printed coefficient would invalidate the correspondence to the source.
A finite prefix cannot establish the eventual-onset conclusion.

## Evidence

The source unit is `D5/S1/Recurrence/MatharA119967Refutation.lean`.
`residual_pos` states positivity at every n≥4; `result : ¬ claim`
negates the disjunction of the two onset readings. The definitions use
natural binomial sums and integer signed coefficients. The independent
arithmetic recomputation gives a(0),...,a(4)=1,1,2,4,9 and L(4)=54.
Kernel compilation, current axiom evidence and source-binding checks
must be assessed from their actual scoped outputs; source text alone
is not verification or publication.

## Triage

Proposed all-index mechanism: the leading two terms have combined coefficient n-4 after replacing
a(n) by its smaller predecessor. The three trailing terms leave the
strictly positive coefficient (n-2)(n+1) after bounding both subtracted
lags by a(n-2). This sign imbalance explains failure at every valid
index and rules out a later onset. No additional hypothesis on the
already fixed source sequence can remove this positive residual.

Computed directly from the defining sum: the residual at n=4 is 54.
No kernel-verified conclusion is claimed for this source-only unit;
the all-index proof, axiom closure and audit binding remain unverified
under the cache capability boundary recorded in issue #30175.
Open: any repaired-sign recurrence or separately printed generating
function claim requires its own faithful statement and proof. No such
repair or companion claim is inferred here. No source-stated dependent
conclusion was identified as relying on this conjecture in the bounded
entry reading; sequence computation using other recurrences survives.

## ASSUMED-UNVERIFIED

World priority, exhaustive prior-work absence, unread/unavailable
sources and the inaccessible individual historical snapshot remain
unverified. The source JSON endpoint returned HTTP 403 on refresh;
the immutable export and current internal entry were readable.
Stage A is source preparation and scoped checking only: no freeze,
deposit, publication, merge or external-problem KPI credit is asserted.
