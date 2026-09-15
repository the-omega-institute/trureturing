# Prime History Normal Forms

## Abstract

Complete guarded prime histories have canonical interval-translation semantics.

A true command raises the excursion by one, and a false command lowers it by one. The frozen word coordinates are the least and greatest prefix displacements, including the empty prefix, and the final displacement. These are not independently selected edge witnesses.

**Theorem 1.1 (Evaluation determines an interval translation).**

$$\forall a \in \mathbb{N},\; Function.Injective\left(evaluate\left(a := a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/PrimeHistoryNormalForm.evaluate_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defined and undefined inputs recover the source interval. Evaluating its lower endpoint then recovers the translation shift, while the empty map is distinguished from every nonempty interval.

**Theorem 1.2 (The explicit realization has the prescribed signature).**

$$\forall a \in \mathbb{N},\; \forall t \in IntervalMap\left(a\right),\; low\left(realize\left(t\right)\right) = -t.lo \land \left(high\left(realize\left(t\right)\right) = (a: \mathbb{Z}) - t.hi \land displacement\left(realize\left(t\right)\right) = t.shift\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/PrimeHistoryNormalForm.realize_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three monotone legs visit the prescribed lower and upper extremes and finish at the prescribed translation shift. Their nonnegative lengths follow from the interval-map bounds.

**Theorem 1.3 (Every admissible interval translation is actually realizable).**

$$\forall a \in \mathbb{N},\; Function.Surjective\left(normal\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/PrimeHistoryNormalForm.normal_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty form [l,u] with shift d, run l divisions, a-u+l multiplications and a-u-d divisions. Its three extrema are derived from the actual concatenation signatures. The admissibility conditions prove that all lengths are nonnegative. Capacity+1 multiplications realize the empty map. Thus the carrier has neither unrealized forms nor multiple encodings of the empty behavior.

The three-invariant word structure is classical: the monogenic free inverse monoid uses precisely a visited interval and a terminal displacement. See Silva, arXiv:2205.08854v2, Section 2.2, equation (1). The present source establishes its concrete bounded-prime execution and realization, not a new discovery of that abstract normal form or a full formalization of the free inverse monoid universal property.

## References

- Truth anchor: `D5/S3/Factorization/Automata/PrimeHistoryNormalForm.evaluate_injective`
- Truth anchor: `D5/S3/Factorization/Automata/PrimeHistoryNormalForm.normal_surjective`
- Truth anchor: `D5/S3/Factorization/Automata/PrimeHistoryNormalForm.realize_signature`
- Dependency: [D5/S3/Factorization/Automata/WordExcursionLowerBound](WordExcursionLowerBound.md)
