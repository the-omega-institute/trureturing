# Existence for the Frozen Streamline Structure

## Abstract

Canonical solenoid streamline data instantiate the frozen observer decomposition with a constant throat.

**Definition 1.1 (The hidden kernel has canonical additive coordinates).**

$$canonicalHidden\in \operatorname{AddEquiv}(hiddenAddress, \ker(\pi))$$

*Formalization.* `D5/S3/Observer/HiddenFlow/StreamlineExistence.hiddenKernelAddEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Chinese remaindering is additive in every modulus, and the residue-to-kernel map is additive coordinatewise. Upgrading the repository's two existing bijections and composing them gives a fixed additive identification of prime-adic hidden addresses with the visible kernel.

**Definition 1.2 (Canonical data instantiate the frozen structure).**

$$(\forall t,\ \gamma(t)= realFlow(r(t))+ k) \Rightarrow frozen(\gamma, r, k)= (\gamma, realFlow\circ r, canonicalHidden)$$

*Formalization.* `D5/S3/Observer/HiddenFlow/StreamlineExistence.toFrozenDecomposition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adapter places the original path, its solenoid-valued real-flow lift, their visible-projection equality, and the canonical additive hidden coordinate equivalence into the existing frozen StreamlineDecomposition structure.

**Theorem 1.3 (The frozen throat is the constant hidden offset).**

$$(\forall u,\ \gamma(u)= realFlow(r(u))+ k) \Rightarrow \forall t,\ throat(frozen(\gamma, r, k), t)= canonicalHidden^{-1}(k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/StreamlineExistence.frozen_streamline_throat_component_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen kernel difference subtracts the real-flow lift from the path. The reconstruction equation cancels that lift and leaves precisely the constant kernel element, expressed in the frozen hidden-address coordinates.

**Theorem 1.4 (Every path instantiates the frozen decomposition uniquely).**

$$\forall \gamma,\ \exists! r, k,\ r(0)= rep(\gamma) \land \forall t,\ \gamma(t)= realFlow(r(t))+ k \land \forall t,\ throat(frozen(\gamma, r, k), t)= canonicalHidden^{-1}(k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/StreamlineExistence.existsUnique_frozen_streamline_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower-stratum theorem supplies the unique normalized real lift and hidden kernel element. The adapter then constructs the frozen observer structure and proves its throat component is constant. The existing profinite-kernel classification is upgraded locally to an additive equivalence, so the public existence theorem requires no coordinate choice from its caller.

**Theorem 1.5 (The constructed frozen throat is continuous).**

$$(\forall t,\ \gamma(t)= realFlow(r(t))+ k) \Rightarrow \operatorname{Continuous}(throat(frozen(\gamma, r, k)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/StreamlineExistence.frozen_streamline_throat_component_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant-throat identity satisfies the right-hand side of the frozen StreamlineTheorem equivalence on the whole real line. Applying that frozen theorem yields continuity, so the former conditional result is now a corollary after existence supplies its input structure.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/StreamlineExistence.existsUnique_frozen_streamline_decomposition`
- Truth anchor: `D5/S3/Observer/HiddenFlow/StreamlineExistence.frozen_streamline_throat_component_constant`
- Truth anchor: `D5/S3/Observer/HiddenFlow/StreamlineExistence.frozen_streamline_throat_component_continuous`
- Truth anchor: `D5/S3/Observer/HiddenFlow/StreamlineExistence.hiddenKernelAddEquiv`
- Truth anchor: `D5/S3/Observer/HiddenFlow/StreamlineExistence.toFrozenDecomposition`
- Dependency: [D5/S1/Solenoid/StreamlineDecomposition](../../../S1/Solenoid/StreamlineDecomposition.md)
- Dependency: [D5/S3/Factorization/SolenoidProfiniteKernel](../../Factorization/SolenoidProfiniteKernel.md)
- Dependency: [D5/S3/Observer/StreamlineTheorem](../StreamlineTheorem.md)
