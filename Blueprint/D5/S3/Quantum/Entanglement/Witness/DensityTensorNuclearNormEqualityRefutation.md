# Refuting the density-tensor nuclear-norm equality conjecture

## Abstract

A mixed flagged Bell density tensor attains the conjectured nuclear-norm maximum.

**Definition 1.1 (The complex nuclear norm).**

$$\forall (\kappa: \operatorname{Type}), ([\operatorname{Fintype}\left(\kappa\right)] (\forall (m: (\kappa) \to (\mathbb{N})), (\forall (t: ((j: \kappa) \to \operatorname{Fin}\left(m\left(j\right)\right)) \to (\mathbb{C})), (\operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.nuclearNorm}\left(m, t\right) = \left\lVert \operatorname{LinearEquiv.symm}\left(\operatorname{Basis.equivFun}\left(\operatorname{Basis.piTensorProduct}\left(\lambda (j: \kappa) \mapsto (\operatorname{PiLp.basisFun}\left(2, \mathbb{C}, \operatorname{Fin}\left(m\left(j\right)\right)\right))\right)\right), t\right) \right\rVert))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.nuclearNorm` (`✓ std3`).

*Citation.* Harm Derksen, Shmuel Friedland, Lek-Heng Lim and Li Wang (2017). *Theoretical and computational aspects of entanglement*. URL: <https://arxiv.org/abs/1705.07160v1>.

*Commentary.*

For a finite mode type κ, nuclearNorm is Mathlib's projective tensor norm of the tensor whose coefficients are t in the product of the standard Euclidean bases. Basis.piTensorProduct constructs this product basis, and its equivFun.symm sends the coefficient array to the tensor. Mathlib supplies the infimum over finite product decompositions, with Euclidean factor norms, matching the source's definition at TeX lines 494–497.

**Definition 1.2 (The maximal nuclear norm of unit tensors).**

$$\forall (\kappa: \operatorname{Type}), ([\operatorname{Fintype}\left(\kappa\right)] (\forall (m: (\kappa) \to (\mathbb{N})), (\operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.alpha}\left(m\right) = \operatorname{sSup}\left(\{(s: \mathbb{R}) \mid (\exists (t: ((j: \kappa) \to \operatorname{Fin}\left(m\left(j\right)\right)) \to (\mathbb{C})), ((\left\lVert \operatorname{WithLp.toLp}\left(2, t\right) \right\rVert = (1: \mathbb{R})) \land (s = \operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.nuclearNorm}\left(m, t\right))))\}\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.alpha` (`✓ std3`).

*Citation.* Harm Derksen, Shmuel Friedland, Lek-Heng Lim and Li Wang (2017). *Theoretical and computational aspects of entanglement*. URL: <https://arxiv.org/abs/1705.07160v1>.

*Commentary.*

For a finite mode type κ and mode sizes m, alpha is the supremum of nuclearNorm over coefficient tensors whose Mathlib Euclidean norm is one. This is the source's α(n,ℂ) definition at TeX lines 525–526.

**Definition 1.3 (A matrix as a doubled density tensor).**

$$\forall (d: \mathbb{N}), (\forall (n: (\operatorname{Fin}\left(d\right)) \to (\mathbb{N})), (\forall (a: \operatorname{Matrix}\left((j: \operatorname{Fin}\left(d\right)) \to \operatorname{Fin}\left(n\left(j\right)\right), (j: \operatorname{Fin}\left(d\right)) \to \operatorname{Fin}\left(n\left(j\right)\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.densityTensor}\left(a\right) = \lambda (i: (j: \operatorname{Sum}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right)) \to \operatorname{Fin}\left(\operatorname{Sum.elim}\left(n, n, j\right)\right)) \mapsto (a\left(\lambda (j: \operatorname{Fin}\left(d\right)) \mapsto (i\left(\operatorname{Sum.inl}\left(j\right)\right)), \lambda (j: \operatorname{Fin}\left(d\right)) \mapsto (i\left(\operatorname{Sum.inr}\left(j\right)\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.densityTensor` (`✓ std3`).

*Citation.* Harm Derksen, Shmuel Friedland, Lek-Heng Lim and Li Wang (2017). *Theoretical and computational aspects of entanglement*. URL: <https://arxiv.org/abs/1705.07160v1>.

*Commentary.*

The matrix indexed by tuples over Fin d is read as a tensor with separate row and column modes. At an index in Fin d ⊕ Fin d, the inl coordinates select the matrix row and the inr coordinates select its column. This is the density-tensor construction described at TeX lines 680–695.

**Definition 1.4 (The equality-case conjecture).**

$$\operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.claim} = (\forall (d: \mathbb{N}), (\forall (n: (\operatorname{Fin}\left(d\right)) \to (\mathbb{N})), (\forall (a: \operatorname{Matrix}\left((j: \operatorname{Fin}\left(d\right)) \to \operatorname{Fin}\left(n\left(j\right)\right), (j: \operatorname{Fin}\left(d\right)) \to \operatorname{Fin}\left(n\left(j\right)\right), \mathbb{C}\right)), ((\operatorname{Matrix.PosSemidef}\left(a\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(a\right) = (1: \mathbb{C})) \Rightarrow ((\operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.nuclearNorm}\left(\operatorname{Sum.elim}\left(n, n\right), \operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.densityTensor}\left(a\right)\right) = \operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.alpha}\left(n\right)^{2}) \Rightarrow (\exists (t: ((j: \operatorname{Fin}\left(d\right)) \to \operatorname{Fin}\left(n\left(j\right)\right)) \to (\mathbb{C})), ((\left\lVert \operatorname{WithLp.toLp}\left(2, t\right) \right\rVert = (1: \mathbb{R})) \land ((\operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.nuclearNorm}\left(n, t\right) = \operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.alpha}\left(n\right)) \land (a = \operatorname{Matrix.vecMulVec}\left(t, \operatorname{star}\left(t\right)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Harm Derksen, Shmuel Friedland, Lek-Heng Lim and Li Wang (2017). *Theoretical and computational aspects of entanglement*. URL: <https://arxiv.org/abs/1705.07160v1>.

*Commentary.*

For every number of modes, mode-size function and positive semidefinite trace-one complex matrix, equality of the doubled density tensor's nuclear norm with alpha squared is asserted to produce a tensor t with Mathlib Euclidean norm one whose nuclear norm is alpha and whose rank-one density matrix is the given matrix. This is the repository's formal reading of the equality conjecture stated at TeX line 878.

**Theorem 1.5 (A mixed equality-case counterexample).**

$$\neg (\operatorname{D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/derksen-friedland-lim-wang-2017-density-tensor-nuclear-norm-equality` (refuted) by `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"derksen-friedland-lim-wang-2017-density-tensor-nuclear-norm-equality","declaration_gid":"D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Harm Derksen, Shmuel Friedland, Lek-Heng Lim and Li Wang (2017). *Theoretical and computational aspects of entanglement*. URL: <https://arxiv.org/abs/1705.07160v1>.

*Commentary.*

Set n to the two-mode size function [2, 4] and identify its index type with Fin 2 × Fin 4. For b in Fin 2, let v b place the coefficient (√2)⁻¹ on the two positions whose second coordinate is the first coordinate plus 2b, and put zero elsewhere. The two vectors have Euclidean norm one. Define a as one half of the sum of the two rank-one matrices vecMulVec (v b) (star (v b)). Their Gram matrix is the identity, so a is positive semidefinite and has trace one.

The row decomposition of any tensor of shape (2,4) gives nuclearNorm at most √2 times its Euclidean norm. For v 0, the linear functional that adds the (0,0) and (1,1) entries has norm at most one on every product tensor and takes v 0 to √2. The dual bound therefore gives nuclearNorm (v 0) = √2. The row upper bound applies to every Euclidean-unit tensor, while v 0 attains it, so alpha n = √2.

Expand densityTensor a into eight product tensors, one for each choice of the two flagged Bell components and their four mode coordinates. Each product has nuclear cost 1/4, giving the upper bound nuclearNorm (densityTensor a) ≤ 2. For the reverse inequality, use the four-mode linear functional that sums the two Bell contractions in each flag block. Its value on a product tensor is bounded by Cauchy–Schwarz after splitting the second and fourth factors into their two two-coordinate blocks; the resulting bound is the product of the four Euclidean norms. The functional takes densityTensor a to 2, so the dual bound gives nuclearNorm (densityTensor a) ≥ 2.

Consequently nuclearNorm (densityTensor a) = 2 = alpha n squared. If claim held, its witness t would have unit Euclidean norm and would satisfy a = vecMulVec t (star t). The unit norm makes this rank-one matrix idempotent, so a squared would equal a. Direct multiplication of the two orthogonal flagged rank-one summands instead gives a squared = (1/2) • a. Since a has trace one and is nonzero, these equalities contradict each other. Thus the equality case need not be a pure density state.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.alpha`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.densityTensor`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.nuclearNorm`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.result`
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../PureState/PureStateHandshake.md)
