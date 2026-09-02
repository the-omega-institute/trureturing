# Strict Kernel Tower Has No Finite Terminal Self

## Abstract

Strictly refining finite interaction profiles have no finite terminal agency-self quotient.

**Theorem 1.1 (No finite interaction stage is terminal).**

$$\forall H \in Type, I \in \mathbb{N} \to Type, O \in Type, Gamma \in \left(\forall n \in \mathbb{N},\; H \to \left(\operatorname{I}\left(n\right) \to \operatorname{PMF}\left(O\right)\right)\right),\; \left(\forall n \in \mathbb{N},\; \operatorname{StrictSubset}\left(\operatorname{ker}\left(\operatorname{Gamma}\left(n+1\right)\right), \operatorname{ker}\left(\operatorname{Gamma}\left(n\right)\right)\right)\right) \Rightarrow \left(\left(\forall n \in \mathbb{N},\; \neg \left(\exists E \in \operatorname{Equiv}\left(\operatorname{Quotient}\left(\operatorname{ker}\left(\operatorname{Gamma}\left(n\right)\right)\right), \operatorname{Quotient}\left(\operatorname{ker}\left(\operatorname{jointReadout}\left(Gamma\right)\right)\right)\right),\; \forall h \in H,\; \operatorname{E}\left(\operatorname{quotientClass}\left(\operatorname{ker}\left(\operatorname{Gamma}\left(n\right)\right), h\right)\right) = \operatorname{quotientClass}\left(\operatorname{ker}\left(\operatorname{jointReadout}\left(Gamma\right)\right), h\right)\right)\right) \land \left(\forall n \in \mathbb{N},\; \exists h \in H, hPrime \in H,\; \operatorname{Gamma}\left(n, h\right) = \operatorname{Gamma}\left(n, hPrime\right) \land \operatorname{Gamma}\left(n+1, h\right) \ne \operatorname{Gamma}\left(n+1, hPrime\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/StrictKernelTowerNoFiniteTerminal.strict_kernel_tower_no_finite_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A level-indexed interaction profile maps each history to a probability law for every intervention available at that level. The complete profile is the canonical dependent joint readout of all finite profiles.

Assume every successor profile has an equality kernel strictly contained in its predecessor's kernel. No finite quotient then admits an equivalence to the complete-profile quotient that sends every history class to the class of the same representative.

The representative law is public because a bare equivalence of carrier types does not identify quotient kernels. Strict descent also gives, at every finite level, two histories that the current profile identifies and the successor profile separates.

## References

- Truth anchor: `D5/S3/Observer/AgencySelf/StrictKernelTowerNoFiniteTerminal.strict_kernel_tower_no_finite_terminal`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
