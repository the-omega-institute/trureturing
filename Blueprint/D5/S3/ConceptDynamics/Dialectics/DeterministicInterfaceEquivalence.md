# Deterministic Interface Equivalence

## Abstract

Six deterministic interface criteria are equivalent on the realized readout image.

**Theorem 1.1 (Six interface criteria are equivalent).**

$$\begin{gathered}\forall X, B: \operatorname{Type}, q: X \to B, F: X \to X,\\{}\operatorname{ListTFAE}\left({[\operatorname{EffectiveDescent}\left(q, F\right), \operatorname{InterfaceCongruence}\left(q, F\right), \forall x, y\in X, \neg \operatorname{IsCarryWitness}\left(q, F, q, x, y\right), \operatorname{FactorsThrough}\left(q \circ F, q\right), \operatorname{PullbackInvariant}\left(q, F\right), \operatorname{depthZeroKernel}\left(q\right) = \operatorname{depthOneKernel}\left(q, F\right)]}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence.deterministic_interface_sixfold_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a state type X, interface type B, readout q, and deterministic update F, the theorem compares six descriptions of the same interface behavior. Effective descent asks for a unique update on the realized readout image, while interface congruence says that F preserves every q-fiber.

The remaining four entries express the same condition in different languages: no pair of equal-readout states is a carry witness, the composite q after F factors through q, every proposition constant on q-fibers remains so after F, and the depth-zero and depth-one kernels coincide.

The equivalence is proved on the realized image of q and uses no finiteness hypothesis. The factorization and kernel arguments also make explicit why one-step interface equality already captures the full deterministic descent criterion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence.deterministic_interface_sixfold_equivalence`
- Dependency: [D5/S0/Rewriting/Quotients/DynamicsDescent](../../../S0/Rewriting/Quotients/DynamicsDescent.md)
- Dependency: [D5/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry](ExactDescentNoCarry.md)
