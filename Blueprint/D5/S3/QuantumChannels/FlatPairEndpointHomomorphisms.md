# Flat-pair endpoint homomorphisms

## Abstract

Endpoint and negative tropical homomorphisms fail monotonicity on everywhere overlapping flat pairs.

**Definition 1.1 (Finite block vectors).**

$$\operatorname{FlatPair} : \operatorname{Type} = \{ n: \mathbb{N}; d: (\operatorname{Fin}\left(n\right)) \to \mathbb{N}; \alpha: \forall i: \operatorname{Fin}\left(n\right), (\operatorname{Fin}\left(d\left(i\right)\right)) \to \mathbb{C}; \beta: \forall i: \operatorname{Fin}\left(n\right), (\operatorname{Fin}\left(d\left(i\right)\right)) \to \mathbb{C} \}$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.FlatPair` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Section 4.1, Eq. (31), p. 9: “A = ⊕ᵢ |αᵢ⟩⟨αᵢ|, B = ⊕ᵢ |βᵢ⟩⟨βᵢ|”. The vectors may be zero. FlatPair stores the number of blocks, their dimensions and their two complex vectors.

**Definition 1.2 (First block matrix).**

$$\forall x: \operatorname{FlatPair}, x.A = \operatorname{Matrix}.\operatorname{blockDiagonal}'\left(\lambda i \mapsto \operatorname{Matrix}.\operatorname{vecMulVec}\left(x.\alpha\left(i\right), \operatorname{star}\left(x.\alpha\left(i\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.A` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Eq. (31), p. 9: “A = ⊕ᵢ |αᵢ⟩⟨αᵢ|, B = ⊕ᵢ |βᵢ⟩⟨βᵢ|”. The first matrix is the block diagonal sum of the unnormalized rank-one matrices.

**Definition 1.3 (Second block matrix).**

$$\forall x: \operatorname{FlatPair}, x.B = \operatorname{Matrix}.\operatorname{blockDiagonal}'\left(\lambda i \mapsto \operatorname{Matrix}.\operatorname{vecMulVec}\left(x.\beta\left(i\right), \operatorname{star}\left(x.\beta\left(i\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.B` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Eq. (31), p. 9: “A = ⊕ᵢ |αᵢ⟩⟨αᵢ|, B = ⊕ᵢ |βᵢ⟩⟨βᵢ|”. The second matrix uses the second vector in each block.

**Definition 1.4 (Everywhere overlapping pairs).**

$$\forall x: \operatorname{FlatPair}, x.IsEverywhereOverlapping = (\forall i: \operatorname{Fin}\left(x.n\right), (\operatorname{dotProduct}\left(\operatorname{star}\left(x.\alpha\left(i\right)\right), x.\beta\left(i\right)\right) \ne 0) \lor ((x.\alpha\left(i\right) = 0) \land (x.\beta\left(i\right) = 0)))$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.IsEverywhereOverlapping` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Eqs. (33)–(34), p. 9: “Also, we define the set of everywhere overlapping pairs Vₑ.ₒ. ⊊ Vₘ.ᵣ. to be those (A, B) ∈ Vₘ.ᵣ. such that, for any i ∈ [n], we have either ⟨αᵢ|βᵢ⟩ ≠ 0 or |αᵢ⟩ = 0 = |βᵢ⟩.” Every block has nonzero cross dot product or both vectors vanish.

**Definition 1.5 (First block weight).**

$$\forall x: \operatorname{FlatPair}, \forall i: \operatorname{Fin}\left(x.n\right), x.p\left(i\right) = (\operatorname{dotProduct}\left(\operatorname{star}\left(x.\alpha\left(i\right)\right), x.\alpha\left(i\right)\right)).\operatorname{re}$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.p` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Eq. (37), p. 10: “the vector |αᵢ⟩ is normalized when pᵢ > 0 and equal to the zero vector when pᵢ = 0, and similarly for the |βᵢ⟩, qᵢ.” In the unnormalized representation the first weight is the real part of the self dot product.

**Definition 1.6 (Second block weight).**

$$\forall x: \operatorname{FlatPair}, \forall i: \operatorname{Fin}\left(x.n\right), x.q\left(i\right) = (\operatorname{dotProduct}\left(\operatorname{star}\left(x.\beta\left(i\right)\right), x.\beta\left(i\right)\right)).\operatorname{re}$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.q` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Eq. (37), p. 10: “the vector |αᵢ⟩ is normalized when pᵢ > 0 and equal to the zero vector when pᵢ = 0, and similarly for the |βᵢ⟩, qᵢ.” The second weight is the real part of the second self dot product.

**Definition 1.7 (Squared normalized overlap).**

$$\forall x: \operatorname{FlatPair}, \forall i: \operatorname{Fin}\left(x.n\right), x.overlapSq\left(i\right) = \frac{\operatorname{Complex}.\operatorname{normSq}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(x.\alpha\left(i\right)\right), x.\beta\left(i\right)\right)\right)}{x.p\left(i\right) \cdot x.q\left(i\right)}$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.overlapSq` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Eq. (37) normalizes the vectors in every nonzero block. Their squared overlap is the squared modulus of the cross dot product divided by the two weights. Division is real division.

**Definition 1.8 (One channel acts on both matrices).**

$$\forall x: \operatorname{FlatPair}, \forall y: \operatorname{FlatPair}, \operatorname{Majorizes}\left(x, y\right) = (\exists C: \operatorname{QuantumChannel}\left((\Sigma i: \operatorname{Fin}\left(x.n\right), \operatorname{Fin}\left(x.d\left(i\right)\right)), (\Sigma i: \operatorname{Fin}\left(y.n\right), \operatorname{Fin}\left(y.d\left(i\right)\right))\right), (C.toCompletelyPositiveMap\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(x.A\right)\right) = \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(y.A\right)) \land (C.toCompletelyPositiveMap\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(x.B\right)\right) = \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(y.B\right)))$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.Majorizes` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Section 4.1, pp. 9–10: “(A, B) ≽ (C, D) if and only if there exists a quantum channel 𝒞 … such that 𝒞(A) = C and 𝒞(B) = D”. Majorizes x y uses a completely positive trace-preserving channel between the two sigma index types.

**Definition 1.9 (Scalar homomorphisms).**

$$\forall a: \mathbb{R}, \forall z: \mathbb{R}, \forall x: \operatorname{FlatPair}, \operatorname{Phi}\left(a, z, x\right) = \sum_{i: \operatorname{Fin}\left(x.n\right)} (\operatorname{if} \operatorname{dotProduct}\left(\operatorname{star}\left(x.\alpha\left(i\right)\right), x.\beta\left(i\right)\right) = 0 \operatorname{then} 0 \operatorname{else} (x.p\left(i\right))^{a} \cdot (x.q\left(i\right))^{1 - a} \cdot (x.overlapSq\left(i\right))^{z})$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.Phi` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Eq. (84), p. 16: “Φ_{α,z}(A, B) := Σᵢ (pᵢ)^α (qᵢ)^{1−α} |⟨αᵢ|βᵢ⟩|^{2z}”. The formula uses the normalized form of Eq. (37). Blocks with zero cross dot product contribute zero.

**Definition 1.10 (Tropical homomorphisms).**

$$\forall z: \mathbb{R}, \forall x: \operatorname{FlatPair}, \operatorname{PhiT}\left(z, x\right) = \operatorname{Finset}.\operatorname{fold}\left(\operatorname{max}, 0, \lambda i \mapsto \operatorname{if} \operatorname{dotProduct}\left(\operatorname{star}\left(x.\alpha\left(i\right)\right), x.\beta\left(i\right)\right) = 0 \operatorname{then} 0 \operatorname{else} (x.overlapSq\left(i\right))^{z}, (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(x.n\right)\right))\right)$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.PhiT` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Eq. (85), p. 17: “Φ^𝕋_z(A, B) := max_{i=1,…,n} |⟨αᵢ|βᵢ⟩|^{2z}”. The formula takes the maximum of the real z-th powers of the squared normalized overlaps. The finite maximum is initialized at zero; zero blocks contribute zero.

**Definition 1.11 (Ordinary target order).**

$$\forall f: (\operatorname{FlatPair}) \to \mathbb{R}, \operatorname{IsMonotone}\left(f\right) = (\forall x: \operatorname{FlatPair}, \forall y: \operatorname{FlatPair}, (x.IsEverywhereOverlapping) \Rightarrow ((y.IsEverywhereOverlapping) \Rightarrow ((\operatorname{Majorizes}\left(x, y\right)) \Rightarrow (f\left(y\right) \le f\left(x\right)))))$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.IsMonotone` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Section 3.1, p. 7: “x ≼ y ⇒ Φ(x) ≼ Φ(y)”. With Majorizes x y, this target order requires the value at y to be at most the value at x.

**Definition 1.12 (Opposite target order).**

$$\forall f: (\operatorname{FlatPair}) \to \mathbb{R}, \operatorname{IsMonotoneOp}\left(f\right) = (\forall x: \operatorname{FlatPair}, \forall y: \operatorname{FlatPair}, (x.IsEverywhereOverlapping) \Rightarrow ((y.IsEverywhereOverlapping) \Rightarrow ((\operatorname{Majorizes}\left(x, y\right)) \Rightarrow (f\left(x\right) \le f\left(y\right)))))$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.IsMonotoneOp` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Section 3.1, p. 7: “x ≼ y ⇒ Φ(x) ≼ Φ(y)”. For the opposite real order the numerical inequality is reversed.

**Definition 1.13 (Endpoint and tropical nonmonotonicity).**

$$\operatorname{claim} = ((\forall a: \mathbb{R}, ((a = 0) \lor (a = 1)) \Rightarrow (\forall z: \mathbb{R}, (z < 1) \Rightarrow ((z \ne 0) \Rightarrow ((\neg (\operatorname{IsMonotone}\left(\operatorname{Phi}\left(a, z\right)\right))) \land (\neg (\operatorname{IsMonotoneOp}\left(\operatorname{Phi}\left(a, z\right)\right))))))) \land (\forall z: \mathbb{R}, (z < 0) \Rightarrow (\neg (\operatorname{IsMonotone}\left(\operatorname{PhiT}\left(z\right)\right)))))$$

*Formalization.* `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.claim` (`✓ std3`).

*Citation.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

Remark 15, p. 21: “We suspect that these additional homomorphisms are in fact not monotone either, since they correspond to parameters α, z for which the α-z relative entropy is known not to satisfy DPI for general pairs of quantum states (with some conditions on the support).” The endpoint parameters are a = 0 or a = 1 and z < 1, excluding the degenerate z = 0 trace maps; both real target orders are tested. The tropical statement uses z < 0 and the ordinary order.

**Theorem 1.14 (The endpoint suspicion holds).**

$$(\forall a: \mathbb{R}, ((a = 0) \lor (a = 1)) \Rightarrow (\forall z: \mathbb{R}, (z < 1) \Rightarrow ((z \ne 0) \Rightarrow ((\neg (\operatorname{IsMonotone}\left(\operatorname{Phi}\left(a, z\right)\right))) \land (\neg (\operatorname{IsMonotoneOp}\left(\operatorname{Phi}\left(a, z\right)\right))))))) \land (\forall z: \mathbb{R}, (z < 0) \Rightarrow (\neg (\operatorname{IsMonotone}\left(\operatorname{PhiT}\left(z\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frits Verhagen; Marco Tomamichel; Erkka Haapasalo (2026). *Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies*. DOI: [10.1007/s00220-026-05675-5](https://doi.org/10.1007/s00220-026-05675-5). URL: <https://arxiv.org/abs/2507.07520v3>.

*Commentary.*

An orthogonally flagged two-outcome filter takes one squared overlap 1/2 to squared overlaps 1/4 and 3/4 with equal second weights. Strict concavity for 0 < z < 1 and strict convexity for z < 0 give opposite strict inequalities. Erasure gives the other failed order. Swapping the two matrices transfers a = 0 to a = 1. For negative z the tropical maximum increases from (1/2)^z to (1/4)^z. The tropical opposite order and monotone derivations remain separate questions.

## References

- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.A`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.B`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.FlatPair`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.IsEverywhereOverlapping`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.IsMonotone`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.IsMonotoneOp`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.Majorizes`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.Phi`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.PhiT`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.claim`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.overlapSq`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.p`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.q`
- Truth anchor: `D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.result`
- Dependency: [D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation](../Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Quantum/Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Quantum/Foundation/FiniteStateChannel.md)
