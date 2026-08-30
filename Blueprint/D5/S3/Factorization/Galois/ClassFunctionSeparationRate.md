# Class-Function Separation Rate

## Abstract

Finite class-function separation is exactly computable from conjugacy classes.

**Definition 1.1 (A conjugacy-invariant target).**

$$\operatorname{IsConj}(sigma, tau) \Rightarrow f(sigma) = f(tau).$$

*Formalization.* `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.IsConjugacyInvariantTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A target is constant on every Mathlib conjugacy class.

**Definition 1.2 (A conjugacy-invariant target pair).**

$$\operatorname{ClassFunction}(f) \land \operatorname{ClassFunction}(g).$$

*Formalization.* `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.AreConjugacyInvariantTargets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both readings in the pair are class functions.

**Definition 1.3 (The finite separation event).**

$$U_{f,g} = \{sigma \in G \mid f(sigma) \neq g(sigma)\}.$$

*Formalization.* `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.separationSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named event contains exactly the elements where the readings differ.

**Definition 1.4 (The exact uniform success rate).**

$$\operatorname{SuccessRate}(f, g) = \frac{\lvert U_{f,g} \rvert}{\lvert G \rvert}.$$

*Formalization.* `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.finiteGroupSuccessRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rate is the rational cardinality ratio of the separation event.

**Definition 1.5 (A separating conjugacy class).**

$$\operatorname{Separates}(C) \iff \exists sigma \in C, f(sigma) \neq g(sigma).$$

*Formalization.* `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.conjugacyClassSeparates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A class is selected when it contains at least one successful element.

**Definition 1.6 (The separating conjugacy classes).**

$$S = \{C \in \operatorname{ConjClasses}(G) \mid \operatorname{Separates}(C)\}.$$

*Formalization.* `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.separatingConjugacyClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This named finite set filters all conjugacy classes by separation.

**Definition 1.7 (The conjugacy-class separation count).**

$$N = \sum C_{C \in S} \lvert C \rvert.$$

*Formalization.* `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.conjugacyClassSeparationCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count sums the cardinalities of all selected classes.

**Lemma 1.8 (The separation event is a union of conjugacy classes).**

$$\operatorname{IsConj}(sigma, tau) \Rightarrow (sigma \in U_{f,g}) \iff (tau \in U_{f,g}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.separation_set_membership_is_conjugacy_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both targets are class functions, conjugate elements either both belong to the separation event or both lie outside it.

**Theorem 1.9 (Uniform success is a conjugacy-class cardinality ratio).**

$$\operatorname{SuccessRate}(f, g) = \frac{N}{\lvert G \rvert}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.finite_group_success_rate_eq_conjugacy_class_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's conjugacy classes partition the finite carrier. Since the separation predicate is constant on each class, fiberwise cardinality reduces the numerator to a sum of whole classes.

The proof needs only a finite monoid, weakening the finite-group structure from the Galois source without changing its instance.

This closes only the finite counting half. Pinned Mathlib has no Chebotarev density theorem, so no prime-ideal frequency transfer is asserted.

**Lemma 1.10 (The empty finite carrier has zero totalized rate).**

$$\operatorname{SuccessRateFin}(0, f, g) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.empty_carrier_has_zero_success_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Fin zero the event is empty and rational zero divided by zero is totalized to zero. A monoid carrier itself cannot realize this case.

**Lemma 1.11 (Every monoid carrier is nonempty).**

$$\operatorname{Nonempty}(G).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.monoid_carrier_is_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity element excludes an empty group or monoid carrier.

**Lemma 1.12 (Identical targets have zero success rate).**

$$\operatorname{SuccessRate}(f, f) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.identical_targets_have_zero_success_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This includes identity, constant, and zero maps when used on both sides.

**Lemma 1.13 (Distinct constant targets have full rate on the trivial group).**

$$\operatorname{SuccessRate}(true, false) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.trivial_group_distinct_targets_have_full_success_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sole group element receives different Boolean readings, so the successful set has cardinality one out of one.

**Lemma 1.14 (Conjugacy invariance is necessary for the class-union step).**

$$\exists sigma, tau \in S3, \operatorname{IsConj}(sigma, tau) \land f(sigma) \neq 0 \land f(tau) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.conjugacy_invariance_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the symmetric group on three letters, evaluation at zero separates one transposition from a conjugate transposition. The comparison target is constant and conjugacy invariant, so the missing premise is isolated to the nonconstant target.

## References

- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.AreConjugacyInvariantTargets`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.IsConjugacyInvariantTarget`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.conjugacyClassSeparates`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.conjugacyClassSeparationCount`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.conjugacy_invariance_is_necessary`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.empty_carrier_has_zero_success_rate`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.finiteGroupSuccessRate`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.finite_group_success_rate_eq_conjugacy_class_count`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.identical_targets_have_zero_success_rate`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.monoid_carrier_is_nonempty`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.separatingConjugacyClasses`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.separationSet`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.separation_set_membership_is_conjugacy_invariant`
- Truth anchor: `D5/S3/Factorization/Galois/ClassFunctionSeparationRate.trivial_group_distinct_targets_have_full_success_rate`
