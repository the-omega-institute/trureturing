# Flat spectra and the width-three bridge

## Abstract

A scalar Gram imposes a dimension obstruction on native width-three bridge matrices.

All dimensions are natural numbers and all local matrices are unrestricted complex rectangular matrices. The native map F is QuantumMaxFlowBound.flow M N, the sum over r in Fin 3 of M r tensor N r. Its rows are Fin a times Fin d and its columns are Fin b times Fin c. The notation conjTranspose means the complex conjugate transpose, ofReal is the real-to-complex embedding, and smul is scalar multiplication of a matrix. Each displayed identity has its indicated matrix index type.

**Definition 1.1 (The universal ordered-cone assertion).**

$$\operatorname{claim} \iff (\forall (a : \mathbb{N}), (\forall (b : \mathbb{N}), (\forall (c : \mathbb{N}), (\forall (d : \mathbb{N}), ((0 < a) \Rightarrow ((a \le b) \Rightarrow ((0 < c) \Rightarrow ((c \le d) \Rightarrow ((((a \cdot a) + (b \cdot b)) \le ((3 \cdot a) \cdot b)) \Rightarrow ((((c \cdot c) + (d \cdot d)) \le ((3 \cdot c) \cdot d)) \Rightarrow (\exists (M : \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\exists (N : \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), \mathbb{C}\right)), (\exists (lam : \mathbb{R}), ((0 < lam) \land ((((b \cdot c) \le (a \cdot d)) \Rightarrow ((\operatorname{conjTranspose}\left(\operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)\right) \cdot \operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)) = \operatorname{smul}\left(\operatorname{ofReal}\left(lam\right), (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(b\right) \times \operatorname{Fin}\left(c\right)), (\operatorname{Fin}\left(b\right) \times \operatorname{Fin}\left(c\right)), \mathbb{C}\right))\right))) \land (((a \cdot d) \le (b \cdot c)) \Rightarrow ((\operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right) \cdot \operatorname{conjTranspose}\left(\operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)\right)) = \operatorname{smul}\left(\operatorname{ofReal}\left(lam\right), (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right))\right))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six domain premises are positivity and ordering for each pair and the two quadratic cone inequalities. The same positive real scalar occurs in both implications. When ad equals bc, both implications apply, so both Gram identities are required.

**Theorem 1.2 (The structural dimension obstruction).**

$$\forall (a : \mathbb{N}), (\forall (b : \mathbb{N}), (\forall (c : \mathbb{N}), (\forall (d : \mathbb{N}), (\forall (M : \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\forall (N : \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), \mathbb{C}\right)), ((0 < c) \Rightarrow (((5 \cdot a) < (2 \cdot b)) \Rightarrow (\forall (lam : \mathbb{R}), ((0 < lam) \Rightarrow (((\operatorname{conjTranspose}\left(\operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)\right) \cdot \operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)) = \operatorname{smul}\left(\operatorname{ofReal}\left(lam\right), (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(b\right) \times \operatorname{Fin}\left(c\right)), (\operatorname{Fin}\left(b\right) \times \operatorname{Fin}\left(c\right)), \mathbb{C}\right))\right)) \Rightarrow ((3 \cdot c) \le d)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction.obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scalar column Gram and the strict inequality 5a < 2b force 3c <= d. The theorem only needs c positive; it therefore includes the positive dimension case. The proof first makes the common kernel of the three M maps trivial. For each r, the kernel of the other two maps has dimension at least b-2a, and its image under M r has the same dimension. Two such images cannot be orthogonal because their dimensions sum to more than a. Testing a relation between the nine products M r adjoint times M s on vectors in these kernels isolates each coefficient and proves linear independence. The native Gram equation then forces every N r adjoint times N s to be a scalar identity. Taking the scalar from any fixed diagonal coordinate gives a matrix H. The stacked M map satisfies J adjoint (H tensor I a) J = ofReal lam times I b, so b <= a rank H and rank H = 3. The concatenated N map has Gram H tensor I c, of rank 3c, and consequently d >= 3c. The block-rank formula is applied from ConstructionReduction.Blocks.rank_block.

**Theorem 1.3 (Failure at the equality boundary).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitute a=c=5 and b=d=13. The cone expressions are 194 <= 195 on both sides, and ad=bc=65. The required column Gram would force 15 <= 13, since 26 > 25. Thus the universal flat-spectrum assertion is false. This concerns equal nonzero singular values in the finite native family; it does not dispute rank attainment, change the tensor grouping, assert a physical realization, or establish a continuum or RT claim.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction.claim`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction.obstruction`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction.result`
- Dependency: [D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction](../../Entanglement/ChoiKiemKye/ConstructionReduction.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound](QuantumMaxFlowBound.md)
