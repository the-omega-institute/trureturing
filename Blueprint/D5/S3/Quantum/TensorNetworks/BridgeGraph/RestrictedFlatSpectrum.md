# The restricted flat-spectrum cone

## Abstract

Coefficient-direction rigidity refutes the restricted native scalar-Gram cone.

All dimensions are natural numbers and all local matrices are unrestricted complex rectangular matrices. The native map F is QuantumMaxFlowBound.flow M N, the sum over r in Fin 3 of M r tensor N r. Its rows are Fin a times Fin d and its columns are Fin b times Fin c. The notation conjTranspose means the complex conjugate transpose, ofReal is the real-to-complex embedding, and smul is scalar multiplication of a matrix. Each displayed identity has its indicated matrix index type.

**Definition 1.1 (The universal eight-premise assertion).**

$$\operatorname{claim} \iff (\forall (a : \mathbb{N}), (\forall (b : \mathbb{N}), (\forall (c : \mathbb{N}), (\forall (d : \mathbb{N}), ((0 < a) \Rightarrow ((a \le b) \Rightarrow ((0 < c) \Rightarrow ((c \le d) \Rightarrow ((((a \cdot a) + (b \cdot b)) \le ((3 \cdot a) \cdot b)) \Rightarrow ((((c \cdot c) + (d \cdot d)) \le ((3 \cdot c) \cdot d)) \Rightarrow (((2 \cdot b) \le (5 \cdot a)) \Rightarrow (((2 \cdot d) \le (5 \cdot c)) \Rightarrow (\exists (M : \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\exists (N : \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), \mathbb{C}\right)), (\exists (lam : \mathbb{R}), ((0 < lam) \land ((((b \cdot c) \le (a \cdot d)) \Rightarrow ((\operatorname{conjTranspose}\left(\operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)\right) \cdot \operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)) = \operatorname{smul}\left(\operatorname{ofReal}\left(lam\right), (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(b\right) \times \operatorname{Fin}\left(c\right)), (\operatorname{Fin}\left(b\right) \times \operatorname{Fin}\left(c\right)), \mathbb{C}\right))\right))) \land (((a \cdot d) \le (b \cdot c)) \Rightarrow ((\operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right) \cdot \operatorname{conjTranspose}\left(\operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)\right)) = \operatorname{smul}\left(\operatorname{ofReal}\left(lam\right), (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right))\right))))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The eight premises are positivity and ordering for each pair, the two quadratic cone inequalities, 2b <= 5a and 2d <= 5c. The same positive real scalar occurs in both implications. When ad equals bc, both implications apply, so both Gram identities are required.

**Theorem 1.2 (The structural dimension obstruction).**

$$\forall (a : \mathbb{N}), (\forall (b : \mathbb{N}), (\forall (c : \mathbb{N}), (\forall (d : \mathbb{N}), (\forall (M : \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)), (\forall (N : \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), \mathbb{C}\right)), ((0 < c) \Rightarrow (((2 \cdot a) < b) \Rightarrow (\forall (lam : \mathbb{R}), ((0 < lam) \Rightarrow (((\operatorname{conjTranspose}\left(\operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)\right) \cdot \operatorname{QuantumMaxFlowBound}.\operatorname{flow}\left(M, N\right)) = \operatorname{smul}\left(\operatorname{ofReal}\left(lam\right), (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(b\right) \times \operatorname{Fin}\left(c\right)), (\operatorname{Fin}\left(b\right) \times \operatorname{Fin}\left(c\right)), \mathbb{C}\right))\right)) \Rightarrow ((3 \cdot c) \le d)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum.obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scalar column Gram with c positive and b > 2a forces 3c <= d; no positivity assumption on a is needed. The common kernel of the M maps is trivial. Their stack has b-dimensional range in the 3a-dimensional ambient space. For each nonzero z in C^3, the a-dimensional subspace of vectors (z r times u) intersects this range nontrivially, since b+a > 3a. Thus there are x and nonzero u with M r x = z r times u for every r. Applying a proposed relation between the nine adjoint products to x on both sides gives the quadratic form of its coefficient matrix times the nonzero inner product of u with itself. This vanishes for every z, so complex polarization forces the coefficient matrix to vanish. The original scalar_cross_grams lemma then makes every N r adjoint times N s a scalar identity. The original stack_gram, concat_gram and rank_kronecker_one lemmas give b <= a rank H, rank H = 3, and 3c <= d.

**Theorem 1.3 (Failure at the equality boundary).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitute a=c=2 and b=d=5. Both quadratic inequalities are 29 <= 30, both ratio premises are 10 <= 10, and ad=bc=10. All eight premises hold. Equality requires both Gram identities for the same M, N and positive scalar. The column identity alone would force 6 <= 5 because 5 > 4, which is impossible. The old strict hypothesis 5a < 2b fails here: both sides equal 10. This is a result about arbitrary finite complex rectangular matrices in the native width-three grouping. It does not dispute rank attainment and carries no physical realization, continuum, RT, optimal-threshold or literature-originality claim.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum.claim`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum.obstruction`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum.result`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction](FlatSpectrumObstruction.md)
