# Heisenberg Channel Compression Equivalence

## Abstract

Compatibility of a finite POVM family under every isometric compression is equivalent to compatibility under every unital completely positive map.

All dimensions and index types are finite. A family M assigns to each setting x a finite outcome-indexed family of complex d by d matrices. Joint measurability means that one parent POVM indexed by all outcome choices has the given marginal at every setting.

**Definition 1.1 (Joint measurability with a parent POVM).**

$$\forall d \in \mathbb{N},\; \forall X \in Type,\; [\operatorname{Fintype}\left(X\right)] \forall \omega \in X \to Type,\; [((x : X) \to \operatorname{Fintype}\left(\omega\left(x\right)\right))] \forall M \in ((x : X) \to \omega\left(x\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)),\; \operatorname{FamilyJointlyMeasurable}\left(M\right) \Leftrightarrow (\exists G \in ((x : X) \to \omega\left(x\right)) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{IsPOVM}\left(G\right)) \land (\forall x \in X,\; \forall b \in \omega\left(x\right),\; \sum_{(a : ((x : X) \to \omega\left(x\right)) \text{with} a\left(x\right) = b)} G\left(a\right) = M\left(x\right)\left(b\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.FamilyJointlyMeasurable` (`✓ std3`).

*Citation.* Roope Uola; Tristan Kraft; Sébastien Designolle; Nikolai Miklin; Armin Tavakoli; Juha-Pekka Pellonpää; Otfried Gühne; Nicolas Brunner (2021). *Quantum measurement incompatibility in subspaces*. DOI: [10.1103/PhysRevA.103.022203](https://doi.org/10.1103/PhysRevA.103.022203). URL: <https://arxiv.org/abs/2010.04048v2>.

*Commentary.*

The parent G is indexed by dependent outcome choices a, one outcome for each setting. It is a POVM, and summing G over choices whose x-coordinate is b recovers M x b. This is the finite joint-measurability condition.

**Definition 1.2 (Compression and channel compatibility).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; ((1 \le n) \land (n \le d)) \Rightarrow (\forall X \in Type,\; [\operatorname{Fintype}\left(X\right)] \forall \omega \in X \to Type,\; [((x : X) \to \operatorname{Fintype}\left(\omega\left(x\right)\right))] \forall M \in ((x : X) \to \omega\left(x\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)),\; (\forall x \in X,\; \operatorname{IsPOVM}\left(M\left(x\right)\right)) \Rightarrow (\left(\forall V \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (((V)^{H}) \cdot (V) = 1) \Rightarrow (\operatorname{FamilyJointlyMeasurable}\left((fun (x : X) \mapsto (fun (b : \omega\left(x\right)) \mapsto (((V)^{H}) \cdot (M\left(x\right)\left(b\right))) \cdot (V)))\right))\right) \Leftrightarrow (\forall \phi \in \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (\operatorname{IsCompletelyPositive}\left(\phi\right)) \Rightarrow ((\phi\left(1\right) = 1) \Rightarrow (\operatorname{FamilyJointlyMeasurable}\left((fun (x : X) \mapsto (fun (b : \omega\left(x\right)) \mapsto \phi\left(M\left(x\right)\left(b\right)\right)))\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.claim` (`✓ std3`).

*Citation.* Roope Uola; Tristan Kraft; Sébastien Designolle; Nikolai Miklin; Armin Tavakoli; Juha-Pekka Pellonpää; Otfried Gühne; Nicolas Brunner (2021). *Quantum measurement incompatibility in subspaces*. DOI: [10.1103/PhysRevA.103.022203](https://doi.org/10.1103/PhysRevA.103.022203). URL: <https://arxiv.org/abs/2010.04048v2>.

*Commentary.*

For 1 at most n at most d, the family is required to be a POVM at every setting. The first side asks for joint measurability after every isometric compression V from dimension n into dimension d. The second asks for joint measurability after every completely positive unital matrix map from d by d matrices to n by n matrices. The two quantified conditions are asserted to be equivalent.

**Theorem 1.3 (Compatibility is unchanged by replacing compressions with channels).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.result` (`✓ std3`). ∎

*Resolves.* `Problems/uola-et-al-2021-heisenberg-channel-compression-equivalence` (proved) by `D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"uola-et-al-2021-heisenberg-channel-compression-equivalence","declaration_gid":"D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Roope Uola; Tristan Kraft; Sébastien Designolle; Nikolai Miklin; Armin Tavakoli; Juha-Pekka Pellonpää; Otfried Gühne; Nicolas Brunner (2021). *Quantum measurement incompatibility in subspaces*. DOI: [10.1103/PhysRevA.103.022203](https://doi.org/10.1103/PhysRevA.103.022203). URL: <https://arxiv.org/abs/2010.04048v2>.

*Commentary.*

An isometry V gives the unital completely positive map X ↦ Vᴴ X V, so every channel-compatible family is compatible after every compression. Conversely, a unital completely positive map has a finite Kraus decomposition Φ(X) = sum_r K_rᴴ X K_r with sum_r K_rᴴ K_r = I. Because n is at most d, each Kraus operator factors as K_r = V_r C_r through an isometry V_r from dimension n into dimension d. A parent POVM for each compressed family is then combined as H_a = sum_r C_rᴴ G^(r)_a C_r. Positivity and the Kraus normalization make H a parent POVM, and its x-marginal is exactly Φ(M x b).

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.FamilyJointlyMeasurable`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](ConcealmentKernelNecessityRefutation.md)
