# Cumulative histories and the difference inverse

## Abstract

Integer-time cumulative histories have an exact adjacent-difference inverse.

Cumulative summation records all past increments at every integer time. The admissible histories have a zero left tail and a constant right tail, which may be nonzero. The construction first works for any additive commutative coefficient group and then specializes to the original jointly finite time-space profiles.

**Definition 1.1 (Finitely supported increments).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Signal`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Signal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Signal R consists of R-valued increments indexed by all integers, with only finitely many nonzero time components.

**Definition 1.2 (Zero left tail and constant right tail).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.TailCondition`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.TailCondition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A history has integer thresholds l and u and a value B. Every value before l is zero, and every value at or after u equals B. The final constant B may be nonzero.

**Definition 1.3 (Admissible cumulative histories).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.History`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.History` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

History R is the subtype of all integer-indexed R-valued sequences satisfying both tail conditions. Pointwise addition uses the smaller left threshold and the larger right threshold; pointwise negation preserves the thresholds. These operations give an additive commutative group.

**Definition 1.4 (Cumulative sum over the finite past support).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At integer time n, cumulative c sums c t over the finite support entries t with t at most n. This is a finite sum at every time, including negative times.

**Theorem 1.5 (One time step adds its increment).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_succ`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support entries at most n consist of the entries at most n minus one together with the increment at n when it is nonzero. Thus the current cumulative value equals its predecessor plus c n.

**Definition 1.6 (Cumulative sums satisfy both tails).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulativeHistory`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulativeHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonempty support, its minimum gives a zero left tail and its maximum gives an eventual constant right tail equal to the total sum. Empty support gives the zero history.

**Theorem 1.7 (Both tails force finite difference support).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference_finite`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjacent difference vanishes before the left threshold because both values are zero, and after the right threshold because both values are B. Its support is contained in a finite integer interval.

**Definition 1.8 (Adjacent differences as a finite signal).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value at n is the history value at n minus its value at n minus one. The proved finite support makes this an element of Signal R.

**Theorem 1.9 (The difference formula at every integer).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference_apply`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation of the finite signal produced by difference is exactly the adjacent subtraction at the chosen integer time.

**Theorem 1.10 (Differences recover every finite signal).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference_cumulative`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference_cumulative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying difference after cumulativeHistory recovers the original increment profile at every integer, using the one-step recurrence and additive cancellation.

**Theorem 1.11 (Cumulative sums recover every admissible history).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_difference`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal adjacent differences and a shared zero point on the left imply equal histories: natural-number induction reaches every time to the right, and the left tail handles earlier times. Applying this uniqueness argument to the differences of C proves exact recovery of C.

**Theorem 1.12 (Cumulative summation preserves addition).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_add`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjacent differences preserve pointwise addition. Uniqueness of a history with those differences and the zero left tail therefore makes the cumulative history of a sum equal to the sum of cumulative histories.

**Definition 1.13 (The additive equivalence for coefficient groups).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulativeEquiv`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulativeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cumulative and difference operators, the two inverse identities, and preservation of addition form an additive equivalence for every additive commutative coefficient group.

**Theorem 1.14 (Bijectivity of cumulative summation).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_inverse_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_inverse_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The additive equivalence supplies injectivity and surjectivity of cumulativeHistory on the full integer-time carriers.

**Definition 1.15 (Three-dimensional integer space).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Space`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Space` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A spatial point has three integer coordinates, represented by a function from Fin 3 to the integers.

**Definition 1.16 (Finite spatial coefficient profiles).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Spatial`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Spatial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A spatial coefficient is an integer-valued function on the three-dimensional lattice with finite support. This theorem uses its additive group structure.

**Definition 1.17 (Jointly finite time-space profiles).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Profile`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A profile has integer coefficients indexed by integer time and a spatial point. Its joint time-space support is finite.

**Definition 1.18 (The equivalence on the original time-space carrier).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.profileCumulativeEquiv`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.profileCumulativeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib Finsupp.curryAddEquiv identifies joint finite support with finitely many finitely supported spatial components. Composing it with cumulativeEquiv gives the additive equivalence on time-space profiles.

**Theorem 1.19 (The forward map is the stated cumulative sum).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.profile_cumulative_apply`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.profile_cumulative_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At time n, the time-space equivalence evaluates to the cumulative sum of the curried spatial increments through n.

**Theorem 1.20 (The inverse formula at each time-space coordinate).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.profile_inverse_apply`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.profile_inverse_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse profile at a pair consisting of time n and spatial point p equals C n p minus C at n minus one and p. Uncurrying preserves joint finite support.

**Theorem 1.21 (Additive bijection with the difference inverse).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On jointly finitely supported profiles, cumulative summation is bijective and preserves addition, and its inverse is adjacent subtraction at every integer time and every spatial point. The target retains both tail conditions and its pointwise additive group structure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.History`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Profile`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Signal`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Space`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.Spatial`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.TailCondition`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulativeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulativeHistory`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_add`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_difference`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_inverse`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_inverse_bijective`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.cumulative_succ`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference_apply`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference_cumulative`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.difference_finite`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.profileCumulativeEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.profile_cumulative_apply`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse.profile_inverse_apply`
