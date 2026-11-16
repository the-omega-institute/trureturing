# Orthogonal pointwise stabilizers

## Abstract

Orthogonal pointwise stabilizers.

**Definition 1.1 (The pointwise-stabilizer quotient action).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), (\operatorname{LieHom}\left(k, \operatorname{stabilizer}\left(B, W\right), \operatorname{skewAdjointLieSubalgebra}\left(\operatorname{LinearMap}.\operatorname{IsRefl}.\operatorname{liftQ}_{2}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right), \operatorname{LinearMap}.\operatorname{ker}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right)\right), (\operatorname{fun} x \mapsto (\operatorname{fun} y \mapsto hB.\operatorname{isRefl}\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)))\right)\right)\right))))))$$

*Formalization.* `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientLieHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical restriction and radical-quotient action is a Lie homomorphism from the actual pointwise stabilizer to the actual skew algebra of the reduced form. Its original proof body is reused by both the semisimple and full derivation constructions.

**Theorem 1.2 (Surjectivity without a trivial-radical assumption).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), ([\operatorname{FiniteDimensional}\left(k, V\right)] \operatorname{Function}.\operatorname{Surjective}\left(\operatorname{quotientLieHom}\left(B, W, hB\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientLieHom_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In finite dimension, the canonical pointwise-stabilizer quotient map is surjective. Neither nondegeneracy of the original ambient form nor trivial radical of the stabilizer is assumed. A nondegenerate complement to the restricted radical gives an orthogonal extension of every quotient skew operator. Zero and isotropic subspaces are included.

**Theorem 1.3 (The actual quotient kernel is two-step nilpotent).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), ([\operatorname{FiniteDimensional}\left(k, V\right)] (B.\operatorname{Nondegenerate}\left(\right)) \Rightarrow (\forall (f : \operatorname{LieHom}.\operatorname{ker}\left(\operatorname{quotientLieHom}\left(B, W, hB\right)\right)), (\forall (g : \operatorname{LieHom}.\operatorname{ker}\left(\operatorname{quotientLieHom}\left(B, W, hB\right)\right)), (\forall (h : \operatorname{LieHom}.\operatorname{ker}\left(\operatorname{quotientLieHom}\left(B, W, hB\right)\right)), (\operatorname{lie}\left(f, \operatorname{lie}\left(g, h\right)\right) = (0))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientLieHom_kernel_triple_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the ambient form is nondegenerate, every nested triple bracket in the actual kernel vanishes. This exposes the stronger bound from the canonical nilpotent-kernel proof for use in the full evolution-derivation kernel. It does not require the restricted subspace or its span to be nondegenerate.

**Definition 1.4 (Setwise skew preserver).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\operatorname{preserver}\left(B, W\right) = (\{f : \operatorname{Module}.\operatorname{End}\left(k, V\right) \mid (f \in \operatorname{skewAdjointLieSubalgebra}\left(B\right)) \land (\forall (w : V), ((w \in W) \Rightarrow (f\left(w\right) \in W)))\})))))$$

*Formalization.* `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.preserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any bilinear form B over a field and subspace W, these are the actual B-skew endomorphisms carrying W into W. Pointwise stabilizers are included. This is the carrier needed after subtracting the class scalar diagonal of a full evolution derivation.

**Definition 1.5 (Action on the nondegenerate quotient).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), (\operatorname{LieHom}\left(k, \operatorname{preserver}\left(B, W\right), \operatorname{skewAdjointLieSubalgebra}\left(\operatorname{LinearMap}.\operatorname{IsRefl}.\operatorname{liftQ}_{2}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right), \operatorname{LinearMap}.\operatorname{ker}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right)\right), (\operatorname{fun} x \mapsto (\operatorname{fun} y \mapsto hB.\operatorname{isRefl}\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)))\right)\right)\right))))))$$

*Formalization.* `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.preserverQuotientLieHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For symmetric B, restriction to W-perpendicular preserves the kernel of the restricted form and therefore induces an actual skew Lie action on the quotient. This construction retains every zero, isotropic and degenerate subspace, and does not require B itself to be nondegenerate or the Lie algebra to be semisimple. The existing pointwise-stabilizer action factors through this canonical construction.

**Definition 1.6 (stabilizer).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\operatorname{stabilizer}\left(B, W\right) = (\{f : \operatorname{Module}.\operatorname{End}\left(k, V\right) \mid (f \in \operatorname{skewAdjointLieSubalgebra}\left(B\right)) \land (\forall (w : V), ((w \in W) \Rightarrow (f\left(w\right) = (0))))\})))))$$

*Formalization.* `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.stabilizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

This Lie subalgebra consists of skew-adjoint endomorphisms that vanish on the specified subspace.

**Theorem 1.7 (quotientForm symm).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), ((\operatorname{LinearMap}.\operatorname{IsRefl}.\operatorname{liftQ}_{2}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right), \operatorname{LinearMap}.\operatorname{ker}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right)\right), (\operatorname{fun} x \mapsto (\operatorname{fun} y \mapsto hB.\operatorname{isRefl}\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)))\right)).\operatorname{IsSymm}\left(\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientForm_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The form induced on the orthogonal subspace modulo its restricted radical is symmetric.

**Theorem 1.8 (quotientForm nondegenerate).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), ((\operatorname{LinearMap}.\operatorname{IsRefl}.\operatorname{liftQ}_{2}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right), \operatorname{LinearMap}.\operatorname{ker}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right)\right), (\operatorname{fun} x \mapsto (\operatorname{fun} y \mapsto hB.\operatorname{isRefl}\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)))\right)).\operatorname{Nondegenerate}\left(\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientForm_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The form induced on the orthogonal subspace modulo its restricted radical is nondegenerate.

**Theorem 1.9 (stabilizer equiv of trivialRadical).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), (\forall (W : \operatorname{Submodule}\left(k, V\right)), (\forall (hB : B.\operatorname{IsSymm}\left(\right)), ([\operatorname{FiniteDimensional}\left(k, V\right)] (B.\operatorname{Nondegenerate}\left(\right)) \Rightarrow ([\operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, \operatorname{stabilizer}\left(B, W\right)\right)] \operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{stabilizer}\left(B, W\right), \operatorname{skewAdjointLieSubalgebra}\left(\operatorname{LinearMap}.\operatorname{IsRefl}.\operatorname{liftQ}_{2}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right), \operatorname{LinearMap}.\operatorname{ker}\left(B.\operatorname{restrict}\left(B.\operatorname{orthogonal}\left(W\right)\right)\right), (\operatorname{fun} x \mapsto (\operatorname{fun} y \mapsto hB.\operatorname{isRefl}\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right)))\right)\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.stabilizer_equiv_of_trivialRadical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Restriction to the orthogonal subspace and passage to its radical quotient give a Lie equivalence when the stabilizer has trivial solvable radical. The restriction kernel has vanishing triple products, and every quotient skew endomorphism extends by an orthogonal projection.

**Theorem 1.10 (standardForm symm).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (n : \operatorname{Type}), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] (\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(n, n, k\right)\right)).\operatorname{IsSymm}\left(\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.standardForm_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The bilinear form of the identity matrix is symmetric.

**Theorem 1.11 (skewAdjoint equiv so).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (B : \operatorname{LinearMap}.\operatorname{BilinForm}\left(k, V\right)), ((B.\operatorname{IsSymm}\left(\right)) \Rightarrow ((B.\operatorname{Nondegenerate}\left(\right)) \Rightarrow (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{skewAdjointLieSubalgebra}\left(B\right), \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(\operatorname{Module}.\operatorname{finrank}\left(k, V\right)\right), k\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.skewAdjoint_equiv_so` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Over an algebraically closed field of characteristic zero, a finite-dimensional nondegenerate symmetric form has the standard orthogonal Lie algebra of its dimension.

## References

- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.preserver`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.preserverQuotientLieHom`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientForm_nondegenerate`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientForm_symm`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientLieHom`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientLieHom_kernel_triple_zero`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.quotientLieHom_surjective`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.skewAdjoint_equiv_so`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.stabilizer`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.stabilizer_equiv_of_trivialRadical`
- Truth anchor: `D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers.standardForm_symm`
- Dependency: [D5/S3/QuadraticForms/LieRadicalTransfer](LieRadicalTransfer.md)
