# Bisection Completion

## Abstract

Rational midpoint bisection identifies its lower Cauchy class as a least upper bound.

All sequences and subsets here are native Lean mathematical objects. QSeq is the full rational Cauchy sequence type and QHat its zero-difference quotient. For S : Set QHat and l u : ℚ, write hl for lower non-upperness and hu for upperness. The consequences O1–O11 below preserve complete statements by direct derivation; they have no separate declaration anchors or independent coverage claim. This component does not establish the rich-real interpretation, internal ZFC coding, definition elimination or conservativity.

**Definition 1.1 (Rational Cauchy sequences).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.QSeq`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.QSeq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence type consists of all rational sequences satisfying the rational absolute-value Cauchy condition.

**Definition 1.2 (The rational Cauchy quotient).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.QHat`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.QHat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the standard quotient of rational Cauchy sequences by zero-limit difference, with its existing field operations.

O4 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: (q : ℚ) : CauSeq.Completion.mk (CauSeq.const abs q) = (q : QHat).

Derivation: Use toReal.injective, O3 on the constant sequence, supplied Real.mk_const, and map_ratCast, exactly the original proof's normalization.

O5 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: : Function.Injective (fun q : ℚ => CauSeq.Completion.mk (CauSeq.const abs q)).

Derivation: Substitute the equality of O4 for each q, then apply Rat.cast_injective into the existing characteristic-zero quotient field. This is the original proof with the omitted equation expanded.

**Definition 1.3 (The ring equivalence with the reals).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.toReal`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.toReal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse of Real.ringEquivCauchy identifies this quotient with the real field.

O1 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: : QHat ≃o ℝ.

Derivation: Use the existing record expression { toReal.toEquiv with map_rel_iff' := Iff.rfl }; completionOrder is exactly the lifted real order.

O3 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: (a : QSeq) : toReal (CauSeq.Completion.mk a) = Real.mk a.

Derivation: Unfold the surviving toReal and the supplied Real.ringEquivCauchy/Real.mk definitions; the equality is reflexive, as in the original body.

O7 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: (x : QHat) : ∃ l u : ℤ, (l : QHat) < x ∧ x < (u : QHat).

Derivation: Apply existing exists_int_lt and exists_int_gt to toReal x. Normalize toReal of integer casts by the ring equivalence and the lifted order. Keep both strict inequalities and both integer witnesses, as in the original body.

**Definition 1.4 (The induced linear order).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.completionOrder`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.completionOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x y : QHat, x ≤ y means toReal x ≤ toReal y, and likewise for strict order.

**Definition 1.5 (Order agrees with field operations).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.completionOrderedRing`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.completionOrderedRing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing quotient field operations satisfy IsStrictOrderedRing under this induced order, by Function.Injective.isStrictOrderedRing.

**Definition 1.6 (The induced metric).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.completionMetric`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.completionMetric` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x y : QHat, dist x y = dist (toReal x) (toReal y) by definition of MetricSpace.induced.

O2 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: : Isometry toReal.

Derivation: Apply the existing Mathlib Isometry.of_dist_eq to the definitional equality of the induced distance with dist (toReal x) (toReal y), exactly the original one-line body.

**Theorem 1.7 (Rational and real Cauchy conditions).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.rational_cauchy_iff_real`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.rational_cauchy_iff_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational sequence satisfies the absolute-value Cauchy condition exactly when its real casts form a metric Cauchy sequence.

**Theorem 1.8 (Terms converge to their own class).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.rational_terms_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.rational_terms_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the real metric, the terms of a rational Cauchy sequence converge to the real image of their own completion class. The estimate comes directly from the Cauchy condition.

**Definition 1.9 (Dyadic approximation errors).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.dyadicRadius`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.dyadicRadius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The error at index n is the reciprocal of the nth power of two.

O6 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: (n : ℕ) : 0 < dyadicRadius n.

Derivation: Unfold the surviving radius definition; positivity of 2, its nth power and its inverse yields the original assertion. This is the existing positivity normalization, with no additional premise.

**Theorem 1.10 (Errors tend to zero).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.dyadic_radius_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.dyadic_radius_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dyadic approximation errors converge to zero.

**Definition 1.11 (The rational midpoint step).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.midpointStep`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.midpointStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Test whether the constant class of the rational midpoint is an upper bound of the set. If so, retain the lower half of the interval; otherwise retain the upper half. The test is classical and asserts no executable decision procedure.

**Definition 1.12 (Iteration from a rational bracket).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisect`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Begin with the given pair of rational endpoints and iterate the midpoint step.

**Definition 1.13 (Lower endpoints).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.lower`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower endpoint sequence is the first coordinate of each iterated rational interval.

**Definition 1.14 (Upper endpoints).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.upper`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.upper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper endpoint sequence is the second coordinate of each iterated rational interval.

**Theorem 1.15 (The endpoints are strictly ordered).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.nonupper_lt_upper`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.nonupper_lt_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational whose class is not an upper bound is strictly below any rational whose class is an upper bound.

**Theorem 1.16 (Preservation of bound properties).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.midpoint_step_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.midpoint_step_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A midpoint step preserves the fact that the lower endpoint is not an upper bound and the upper endpoint is an upper bound.

**Theorem 1.17 (Exact halving).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.midpoint_step_halves`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.midpoint_step_halves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either outcome of the midpoint test, the new rational width is exactly half the previous width.

**Theorem 1.18 (The midpoint invariant).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every index, the lower class is not an upper bound, the upper class is an upper bound, and the rational width equals the initial width divided by the corresponding power of two. The lower endpoint need not bound all members below.

**Theorem 1.19 (Monotone endpoints).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_nested`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_nested` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower endpoint sequence is monotone, the upper endpoint sequence is antitone, and the lower endpoint is always strictly below the upper endpoint.

O8 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: (S : Set QHat) (l u : ℚ) (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) {n m : ℕ} (hnm : n ≤ m) : Icc (lower S l u m) (upper S l u m) ⊆ Icc (lower S l u n) (upper S l u n).

Derivation: From the retained bisection_nested take hlo and hup; apply Icc_subset_Icc (hlo hnm) (hup hnm). No new hypothesis or reduced quantification.

**Theorem 1.20 (Vanishing widths).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_width_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_width_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real casts of the rational interval widths converge to zero, by exact halving and the vanishing dyadic radius.

**Theorem 1.21 (Both endpoints are Cauchy).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_endpoints_cauchy`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_endpoints_cauchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nesting bounds the distance between two later endpoints by an earlier interval width. Consequently both rational endpoint sequences are Cauchy.

**Definition 1.22 (The lower Cauchy sequence).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.lowerSeq`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.lowerSeq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower endpoint sequence, together with its Cauchy proof, defines a rational Cauchy representative.

Write L = lowerSeq S l u hl hu and c = CauSeq.Completion.mk L; these proof arguments specify the actual lower endpoint representative.

**Definition 1.23 (The upper Cauchy sequence).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.upperSeq`

*Formalization.* `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.upperSeq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper endpoint sequence, together with its Cauchy proof, defines a rational Cauchy representative.

Write U = upperSeq S l u hl hu. Both endpoint Cauchy proofs and representatives are retained for the completion-class consequence O9.

**Theorem 1.24 (A common real limit).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_common_limit_real`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_common_limit_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real casts of both endpoint sequences tend to the real image of the lower endpoint class.

O9 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: (S : Set QHat) (l u : ℚ) (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) : CauSeq.Completion.mk (upperSeq S l u hl hu) = CauSeq.Completion.mk (lowerSeq S l u hl hu) ∧ Tendsto (fun n => (lower S l u n : QHat)) atTop (𝓝 (CauSeq.Completion.mk (lowerSeq S l u hl hu))) ∧ Tendsto (fun n => (upper S l u n : QHat)) atTop (𝓝 (CauSeq.Completion.mk (lowerSeq S l u hl hu))).

Derivation: Let hlo,hup be the two projections of the retained bisection_common_limit_real. The retained rational_terms_tendsto U gives convergence of the upper real terms to Real.mk U; tendsto_nhds_unique with hup gives Real.mk U = Real.mk L. Use toReal.injective and O3 to obtain class equality. For each of the two QHat term sequences, apply Isometry.tendsto_nhds_iff with the direct O2 isometry; Function.comp_def, map_ratCast and O3 identify its real image with hlo or hup. Assemble exactly these three assertions. This is the original common_limit body with its omitted trivial wrapper names expanded.

Here L = lowerSeq S l u hl hu, U = upperSeq S l u hl hu, and c = CauSeq.Completion.mk L. Class equality and both QHat sequence limits are asserted separately from the real-limit theorem.

**Theorem 1.25 (The midpoint limit is a least upper bound).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_isLUB`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_isLUB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper endpoint limit bounds every member of the set. If an upper bound were below the lower endpoint limit, a sufficiently late lower endpoint would itself be an upper bound, contradicting the invariant.

O10 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: (S : Set QHat) (hne : S.Nonempty) (hb : BddAbove S) : ∃ l u : ℚ, (∃ x ∈ S, (l : QHat) < x) ∧ (l : QHat) ∉ upperBounds S ∧ (u : QHat) ∈ upperBounds S.

Derivation: Choose x∈S from hne and y∈upperBounds S from hb. O7 at x supplies integer a<x; O7 at y supplies integer b>y. Set l=(a:ℚ), u=(b:ℚ). Rat.cast_intCast identifies their QHat casts. The same x witnesses the first conjunct. Upperness of l contradicts l<x; every z∈S satisfies z≤y<u, so u is an upper bound. These are exactly the witnesses and argument of the original bracket proof, with O7 expanded.

S may be unbounded below. Only l below one member is required; no lower bound of S is assumed or selected.

O11 (direct consequence, without a separate declaration). Exact statement, with the displayed binders: (S : Set QHat) (hne : S.Nonempty) (hb : BddAbove S) : ∃ l u : ℚ, ∃ hl : (l : QHat) ∉ upperBounds S, ∃ hu : (u : QHat) ∈ upperBounds S, (∃ x ∈ S, (l : QHat) < x) ∧ IsLUB S (CauSeq.Completion.mk (lowerSeq S l u hl hu)).

Derivation: Take exactly l,u,hx,hl,hu from O10 and form the original existential tuple with the retained bisection_isLUB S l u hl hu. Keep the dependent proof arguments of lowerSeq and the below-member witness. No pre-existing arbitrary supremum replaces this endpoint.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.QHat`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.QSeq`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisect`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_common_limit_real`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_endpoints_cauchy`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_invariant`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_isLUB`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_nested`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.bisection_width_tendsto`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.completionMetric`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.completionOrder`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.completionOrderedRing`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.dyadicRadius`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.dyadic_radius_tendsto`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.lower`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.lowerSeq`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.midpointStep`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.midpoint_step_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.midpoint_step_halves`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.nonupper_lt_upper`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.rational_cauchy_iff_real`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.rational_terms_tendsto`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.toReal`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.upper`
- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion.upperSeq`
