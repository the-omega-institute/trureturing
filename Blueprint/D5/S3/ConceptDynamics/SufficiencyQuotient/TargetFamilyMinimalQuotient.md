# Minimal Quotient for a Target Family

## Abstract

The simultaneous target-kernel quotient is the coarsest state sufficient for every member of a dependent target family.

**Theorem 1.1 (The target-family quotient is minimally sufficient).**

$$\begin{gathered}\forall I, X, O: \operatorname{Type},\\{}Y: I \to \operatorname{Type}, K: \forall i: I, X \to Y\left(i\right),\\{}q: X \to O,\\{}(\forall i: I, \exists factor: O \to Y\left(i\right), K\left(i\right) = \operatorname{compose}\left(factor, q\right)) \Rightarrow\\{}[(\forall i: I, \exists! descend: \operatorname{Quotient}\left(\operatorname{ker}\left(\operatorname{jointReadout}\left(K\right)\right)\right) \to Y\left(i\right), K\left(i\right) = \operatorname{compose}\left(descend, \operatorname{quotientClassMap}\left(\operatorname{jointReadout}\left(K\right)\right)\right)) \land\\{}\operatorname{ker}\left(q\right) \subseteq \operatorname{ker}\left(\operatorname{jointReadout}\left(K\right)\right) \land\\{}\operatorname{ker}\left(q\right) \subseteq \operatorname{ker}\left(\operatorname{quotientClassMap}\left(\operatorname{jointReadout}\left(K\right)\right)\right)].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.target_family_minimal_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is arbitrary, the target output type may depend on its index, and the joint readout is the repository's canonical dependent product of all target values.

The quotient is taken by equality of that joint readout. Its canonical projection admits a unique descended readout for every target, so the quotient itself decides the whole target family.

If another readout decides every target, equality under that readout forces equality of the complete target profile. Its kernel is therefore contained in both the profile kernel and the kernel of the canonical quotient projection.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.target_family_minimal_quotient`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
