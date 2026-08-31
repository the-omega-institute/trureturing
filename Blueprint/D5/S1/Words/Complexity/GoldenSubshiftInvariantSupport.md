# Invariant Measures Have Full Support

## Abstract

Every shift-invariant Borel probability measure on the golden word subshift has full support and is therefore positive on every nonempty open set.

Write X_g for the golden word subshift, sigma for its one-step forward shift, and supp(mu) for the support of a measure mu. Mathlib proves that positivity on every nonempty open set implies full support. The result below supplies the converse needed here: if every point lies in the support, then any nonempty open set is a neighbourhood of one of those points and consequently has positive measure.

**Theorem 1.1 (Full support makes every nonempty open set positive).**

$$\forall \mu \in \operatorname{Measure}(X_g), \operatorname{supp}(\mu) = X_g \Rightarrow \operatorname{IsOpenPosMeasure}(\mu)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.isOpenPosMeasure_of_support_eq_univ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a point in a nonempty open set. Full support puts that point in the support, whose neighbourhood characterization says that every neighbourhood of the point has nonzero measure. Applied to the given open set, this is precisely positivity on nonempty open sets.

**Theorem 1.2 (An invariant shift carries support points to support points).**

$$\forall \mu \in \operatorname{Measure}(X_g), \operatorname{map}(\sigma)(\mu) = \mu \Rightarrow \forall x \in X_g, x \in \operatorname{supp}(\mu) \Rightarrow \sigma(x) \in \operatorname{supp}(\mu)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.support_mem_of_map_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a neighbourhood U of sigma(x) and choose a smaller open neighbourhood V inside it. Continuity makes the inverse image of V a neighbourhood of x, so membership of x in the support gives that inverse image positive mass. The pushforward identity transfers the same mass to V, and monotonicity transfers positivity from V to U.

Iterating the one-step statement shows that every natural translate of the support is contained in the support. The support is closed. Since the golden subshift action is minimal, a closed subset with this forward invariance is either empty or all of X_g. A probability measure is nonzero, so its support cannot be empty.

**Theorem 1.3 (Invariant probability measures have full support).**

$$\forall \mu \in \operatorname{Prob}(X_g), \operatorname{map}(\sigma)(\mu) = \mu \Rightarrow \operatorname{supp}(\mu) = X_g$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.invariant_support_eq_univ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preceding support propagation gives the invariant-subset input to minimality, while the standard closedness of support gives the topological input. Minimality leaves the empty and universal cases; the nonzero total mass of a probability measure excludes the empty case.

**Theorem 1.4 (Invariant probability measures charge every nonempty open set).**

$$\forall \mu \in \operatorname{Prob}(X_g), \operatorname{map}(\sigma)(\mu) = \mu \Rightarrow \operatorname{IsOpenPosMeasure}(\mu)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.invariantMeasure_isOpenPosMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the full-support conclusion to the invariant probability measure, then use the converse to Mathlib's support theorem established at the start. Thus every nonempty open subset of X_g has positive measure.

**Theorem 1.5 (The golden subshift carries an open-positive invariant measure).**

$$\exists \mu \in \operatorname{Prob}(X_g), (\operatorname{Measurable}(\sigma) \land \operatorname{map}(\sigma)(\mu) = \mu) \land \operatorname{IsOpenPosMeasure}(\mu)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.golden_invariant_isOpenPosMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the invariant probability measure constructed upstream. Its measure-preserving certificate supplies both displayed fields: sigma is measurable and its pushforward fixes the measure. The general result above supplies positivity on every nonempty open set.

## References

- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.golden_invariant_isOpenPosMeasure`
- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.invariantMeasure_isOpenPosMeasure`
- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.invariant_support_eq_univ`
- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.isOpenPosMeasure_of_support_eq_univ`
- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftInvariantSupport.support_mem_of_map_eq`
- Dependency: [D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure](GoldenSubshiftInvariantMeasure.md)
- Dependency: [D5/S1/Words/Complexity/GoldenSubshiftMinimalAction](GoldenSubshiftMinimalAction.md)
