# Finite Observation Quotient Range

## Abstract

A finite joint-readout quotient is equivalent to its realized image.

**Theorem 1.1 (The finite observation quotient is its realized range).**

$$\forall I, X: \operatorname{Type}, O: I \to \operatorname{Type}, q: \forall i: I, X \to \operatorname{O}(i), J: \operatorname{Finset}(I),\ \operatorname{Nonempty}({\operatorname{EffectiveObservationQuotient}(q, J) \equiv \operatorname{range}(\operatorname{finiteObservationReadout}(q, J))}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange.finite_observation_quotient_equiv_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a state type, I an observation-index type, O a dependent output family, q the corresponding readout family, and J a finite subset of I. FiniteObservationOutput is the dependent product over J, and finiteObservationReadout is the imported jointReadout restricted to indices in J.

staticRelativeIdentity is exactly the equality kernel of that finite readout, and EffectiveObservationQuotient is its Setoid quotient. The displayed Nonempty equivalence identifies this named quotient with precisely the Set.range of the same finite readout.

Pinned Mathlib and Loogle provide the exact arbitrary-function result Setoid.quotientKerEquivRange. The Lean theorem applies it directly; there is no finiteness condition on X, no injectivity or surjectivity premise, and no claim about the full output type.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange.finite_observation_quotient_equiv_range`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
