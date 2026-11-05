# Orthogonal pointwise stabilizers

## Abstract

Orthogonal pointwise stabilizers.

**Definition 1.1 (stabilizer).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\operatorname{stabilizer}\left(B, W\right) = (\{f : \operatorname{Module}.\operatorname{End}\left(k, V\right) \mid (f \in \operatorname{skewAdjointLieSubalgebra}\left(B\right)) \land (\forall (w : V), ((w \in W) \Rightarrow (f\left(w\right) = (0))))\})))))$$

*Formalization.* `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.stabilizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

This Lie subalgebra consists of skew-adjoint endomorphisms that vanish on the specified subspace.

**Theorem 1.2 (quotientForm symm).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), ((\operatorname{LinearMap}.\operatorname{IsRefl}.\operatorname{liftQ}_{2}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right), \operatorname{LinearMap}.\operatorname{ker}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right)\right), (\operatorname{fun} x \mapsto (\operatorname{fun} y \mapsto hB.\operatorname{isRefl}\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)))\right)).\operatorname{IsSymm}\left(\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientForm_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The form induced on the orthogonal subspace modulo its restricted radical is symmetric.

**Theorem 1.3 (quotientForm nondegenerate).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), ((\operatorname{LinearMap}.\operatorname{IsRefl}.\operatorname{liftQ}_{2}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right), \operatorname{LinearMap}.\operatorname{ker}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right)\right), (\operatorname{fun} x \mapsto (\operatorname{fun} y \mapsto hB.\operatorname{isRefl}\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)))\right)).\operatorname{Nondegenerate}\left(\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientForm_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The form induced on the orthogonal subspace modulo its restricted radical is nondegenerate.

**Theorem 1.4 (stabilizer equiv of trivialRadical).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), ([\operatorname{FiniteDimensional}\left(k, V\right)] (B.\operatorname{Nondegenerate}\left(\right)) \Rightarrow ([\operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, \operatorname{stabilizer}\left(B, W\right)\right)] \operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{stabilizer}\left(B, W\right), \operatorname{skewAdjointLieSubalgebra}\left(\operatorname{LinearMap}.\operatorname{IsRefl}.\operatorname{liftQ}_{2}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right), \operatorname{LinearMap}.\operatorname{ker}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right)\right), (\operatorname{fun} x \mapsto (\operatorname{fun} y \mapsto hB.\operatorname{isRefl}\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)))\right)\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.stabilizer_equiv_of_trivialRadical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Restriction to the orthogonal subspace and passage to its radical quotient give a Lie equivalence when the stabilizer has trivial solvable radical. The restriction kernel has vanishing triple products, and every quotient skew endomorphism extends by an orthogonal projection.

**Theorem 1.5 (standardForm symm).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (n : \operatorname{Type}), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] (\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(n, n, k\right)\right)).\operatorname{IsSymm}\left(\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.standardForm_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The bilinear form of the identity matrix is symmetric.

**Theorem 1.6 (skewAdjoint equiv so).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), ((B.\operatorname{IsSymm}\left(\right)) \Rightarrow ((B.\operatorname{Nondegenerate}\left(\right)) \Rightarrow (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{skewAdjointLieSubalgebra}\left(B\right), \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(\operatorname{Module}.\operatorname{finrank}\left(k, V\right)\right), k\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.skewAdjoint_equiv_so` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Over an algebraically closed field of characteristic zero, a finite-dimensional nondegenerate symmetric form has the standard orthogonal Lie algebra of its dimension.

## References

- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientForm_nondegenerate`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientForm_symm`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.skewAdjoint_equiv_so`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.stabilizer`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.stabilizer_equiv_of_trivialRadical`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.standardForm_symm`
