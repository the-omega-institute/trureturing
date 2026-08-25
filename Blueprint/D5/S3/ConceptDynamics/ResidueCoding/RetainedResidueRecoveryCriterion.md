# Retained Residue Recovery Criterion

## Abstract

Retained coprime residue coordinates recover a bounded state exactly when their product has sufficient capacity.

**Theorem 1.1 (Retained residues are injective exactly at product capacity).**

$$\begin{gathered}\forall R, m, K,\\{}\operatorname{Finite}(R) \land (\forall i \in R, 0 < m_{i}) \land \operatorname{PairwiseCoprime}(m) \Rightarrow\\{}\operatorname{Injective}(\operatorname{jointReadout}(i \mapsto x \mapsto x \operatorname{mod} m_{i}): X_{K} \to \prod_{i \in R} \operatorname{ZMod}(m_{i})) \iff K \leq \prod_{i \in R} m_{i}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ResidueCoding/RetainedResidueRecoveryCriterion.retained_residue_recovery_iff_product_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be the finite family of retained coordinates. Each retained modulus is positive, and distinct retained moduli are coprime.

The observation is the canonical dependent joint readout whose ith coordinate reduces a bounded natural state modulo the ith modulus.

Injectivity forces the state-space cardinality not to exceed the product of the output cardinalities. Conversely, the finite-family Chinese remainder equivalence identifies equal residue words modulo the product, and the capacity bound makes the representatives equal.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ResidueCoding/RetainedResidueRecoveryCriterion.retained_residue_recovery_iff_product_capacity`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
