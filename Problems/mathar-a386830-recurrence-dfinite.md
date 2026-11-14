---
slug: mathar-a386830-recurrence-dfinite
bibkey: mathar2025a386830
doi: null
url: https://oeis.org/A386830
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/MatharA386830.result
---

# Mathar's A386830 recurrence and ordinary D-finiteness

## Problem

For every natural m, including zero, define the inclusive integer sum

$$
a(m)=\sum_{k=0}^{m}3^k2^{m-k}
\binom{3m+1}{k}\binom{3m-k}{m-k}.
$$

The Online Encyclopedia of Integer Sequences, A386830 revision 10,
attributes this sequence to Seiichi Manyama and the following conjecture to
R. J. Mathar:

> Conjecture D-finite with recurrence +8*n*(2*n-3)*a(n) +6*(-108*n^2+207*n-80)*a(n-1) +405*(3*n-2)*(3*n-4)*a(n-2)=0.

The complete target is the conjunction of

$$
\forall n\in\mathbb N,\ n\ge2\Longrightarrow
8n(2n-3)a(n)+6(-108n^2+207n-80)a(n-1)
+405(3n-2)(3n-4)a(n-2)=0
$$

in the integers and the existence of a nonzero homogeneous
polynomial-coefficient differential operator annihilating the entire ordinary
formal series

$$
A(X)=\sum_{m\ge0}a(m)X^m\in\mathbb Q[[X]].
$$

All polynomial coefficient subtractions occur after casting n to the
integers. Sequence backshifts are natural subtractions guarded by n >= 2.
The source has OFFSET 0,2 and states no recurrence onset. The n >= 2 domain
is the adopted nonnegative-backshift interpretation, not an author-stated
bound or the meaning of the second OFFSET component.

## Motivation

The recurrence and a genuine homogeneous ordinary-series certificate close
one source event. Neither a finite residual screen nor an equivalent-looking
alternate sum alone closes the conjunction. No exponential generating series,
convergence hypothesis or unspecified negative-index sequence is involved.

## Gap

The source calls the conjunction a conjecture. The bounded duplicate screen
and prior-work boundary are recorded in
[the prospective event](https://github.com/the-omega-institute/trureturing/issues/30405)
and its library note. Generic finite-binomial identities are reusable
ingredients, not an already verified settlement of the literal conjunction.
Global solvedness, priority and exhaustive absence of prior proofs remain
ASSUMED-UNVERIFIED.

## Route

Expanding 5 = 3 + 2, exchanging finite triangular sums, applying
`Nat.choose_mul`, and using `Int.alternating_sum_range_choose_eq_choose`
prove, at every natural n,

$$
a(n)=\sum_{j=0}^{n}5^j(-2)^{n-j}\binom{3n+1}{j}.
$$

For b(n) = 5^n binomial(3n-2,n), the finite contiguous and cross-multiplied
binomial identities are

$$
4a(n)-27a(n-1)=9b(n)\quad(n\ge1),
$$

$$
2n(2n-3)b(n)=15(3n-2)(3n-4)b(n-1)\quad(n\ge2).
$$

Eliminating b proves the exact published recurrence. The n = 1 contiguous
boundary is included, so elimination also covers n = 2.

The ordinary-series certificate has order three:

$$
(16X-648X^2+3645X^3)A'''
+(8-1998X+21870X^2)A''
+(-588+25110X)A'+3240A=0.
$$

Coefficient comparison reduces this homogeneous equation to the recurrence
at n+2, multiplied by n+1, for every natural coefficient index n. The
constant coefficient of the polynomial multiplying A'' is 8. Thus this
operator is genuinely nonzero; minimal order is not part of the target.

## Falsifier

A nonzero exact recurrence residual for a literal-sum index n >= 2 refutes
the first clause. A nonzero coefficient of the displayed homogeneous
expression refutes that proposed certificate. Failure of a bounded formal
attempt supplies neither counterexample.

## Evidence

The mathematical source is `D5/S3/ArithSums/MatharA386830.lean`. Its public
objects are `a`, `series` and `result`. The result proves the conjunction of
the exact guarded integer recurrence and a nonzero homogeneous operator for
the ordinary series defined directly from `a`. Its actual axiom closure is
limited to `Classical.choice`, `Quot.sound` and `propext`.

The private theorem `literal_eq_transform` establishes the all-index source
bridge, using `signed_partial`. The finite coefficient identities
`f_geometric`, `f_pascal` and `f_cubic`, together with `choose_boundary`, feed
`contiguous`. The private steps `b_ratio` and `recurrence` eliminate the
auxiliary sequence. The private `homogeneous_equation` supplies the entire
ordinary-series certificate consumed by `result`. No frozen D5 mathematical
supplier is an input; the source imports pinned Mathlib ingredients directly.

## Triage

The admission basis for the exact complete source endpoint is
`open-problem-resolution`, with `utility: none`. All authored theorem proofs are classified `bind-only` under the repository's
inlining and normalization rule. Each auxiliary theorem has the live consumer
listed above; the public `result` owns the exact external source endpoint.
These are consumed proof steps, not additional external problems or a
manufactured escape witness. No source-event KPI or worldwide priority follows merely
from implementing the proof.

## ASSUMED-UNVERIFIED

Independent review, freezing, required CI and publication remain separate
delivery obligations. The scoped formal certificate does not establish
minimal differential order, analytic asymptotics, all other OEIS formulas,
or the completion of a continuing research goal.

The four-slot escape audit is unfinished under
[the concrete source-binding issue](https://github.com/the-omega-institute/trureturing/issues/30408).
The Reg mirror supplies typed whole-family bridge, variation, sensitivity
and observational-dependence evidence. It does not supply an outer
`Contract.Registration` or producer-validated occurrence ties between the
three recurrence values and the coefficients hidden in `series`. The linked
issue exception permits mathematical delivery without calling this audit
`declared_validated`.
