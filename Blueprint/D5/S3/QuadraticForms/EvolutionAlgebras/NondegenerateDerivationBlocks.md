# Derivation blocks of nondegenerate evolution algebras

## Abstract

Derivation blocks of nondegenerate evolution algebras.

**Theorem 1.1 (Equations.mul_basis_right).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), ((\forall (i : I), (\forall (j : I), ((i \ne j) \Rightarrow (mu\left(b\left(i\right), b\left(j\right)\right) = (0))))) \Rightarrow ([\operatorname{Fintype}\left(I\right)] \forall (x : V), (\forall (i : I), (mu\left(x, b\left(i\right)\right) = (\operatorname{SMul}.\operatorname{smul}\left(b.\operatorname{repr}\left(x, i\right), mu\left(b\left(i\right), b\left(i\right)\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.mul_basis_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying a vector on the right by one natural-basis vector keeps exactly that coordinate times its square.

**Theorem 1.2 (Equations.mul_basis_left).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), ((\forall (i : I), (\forall (j : I), ((i \ne j) \Rightarrow (mu\left(b\left(i\right), b\left(j\right)\right) = (0))))) \Rightarrow ([\operatorname{Fintype}\left(I\right)] \forall (x : V), (\forall (i : I), (mu\left(b\left(i\right), x\right) = (\operatorname{SMul}.\operatorname{smul}\left(b.\operatorname{repr}\left(x, i\right), mu\left(b\left(i\right), b\left(i\right)\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.mul_basis_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying a vector on the left by one natural-basis vector keeps exactly that coordinate times its square.

**Definition 1.3 (piLieRing).**

$$\forall (\alpha : \operatorname{Type}), (\forall (H : (\alpha \to \operatorname{Type})), ([\forall (a : \alpha), (\operatorname{LieRing}\left(H\left(a\right)\right))] \operatorname{Pi}.\operatorname{piLieRing}\left(H\right) : \operatorname{LieRing}\left(\forall (a : \alpha), (H\left(a\right))\right) = (\{\operatorname{inferInstance}\left(\right) : \operatorname{AddCommGroup}\left(\forall (a : \alpha), (H\left(a\right))\right) \operatorname{with} \operatorname{bracket} := (\operatorname{fun} f \mapsto (\operatorname{fun} g \mapsto (\operatorname{fun} a \mapsto \operatorname{Bracket}.\operatorname{bracket}\left(f\left(a\right), g\left(a\right)\right))))\})))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piLieRing` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The dependent product has the pointwise Lie bracket and the existing pointwise additive group. Its Lie identities hold at every coordinate.

**Definition 1.4 (piLieAlgebra).**

$$\forall (k : \operatorname{Type}), ([\operatorname{CommRing}\left(k\right)] \forall (\alpha : \operatorname{Type}), (\forall (H : (\alpha \to \operatorname{Type})), ([\forall (a : \alpha), (\operatorname{LieRing}\left(H\left(a\right)\right))] [\forall (a : \alpha), (\operatorname{LieAlgebra}\left(k, H\left(a\right)\right))] \operatorname{Pi}.\operatorname{piLieAlgebra}\left(k, H\right) : \operatorname{LieAlgebra}\left(k, \forall (a : \alpha), (H\left(a\right))\right) = (\{(\operatorname{inferInstance}\left(\right) : \operatorname{Module}\left(k, \forall (a : \alpha), (H\left(a\right))\right)) \operatorname{with}\}))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piLieAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The dependent product extends the existing pointwise module with the coordinatewise proof of compatibility between the Lie bracket and scalar multiplication. The record has no additional data fields.

**Definition 1.5 (piDirectSumEquiv).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (\beta : \operatorname{Type}), ([\operatorname{Fintype}\left(\beta\right)] \forall (H : (\beta \to \operatorname{Type})), ([\forall (a : \beta), (\operatorname{LieRing}\left(H\left(a\right)\right))] [\forall (a : \beta), (\operatorname{LieAlgebra}\left(k, H\left(a\right)\right))] \operatorname{BlockLinear}.\operatorname{piDirectSumEquiv}\left(H\right) = (\{\operatorname{toLinearEquiv} := \operatorname{DirectSum}.\operatorname{linearEquivFunOnFintype}\left(k, \beta, H\right).\operatorname{symm}\}))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piDirectSumEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For a finite index type, the standard linear equivalence from products to direct sums preserves the componentwise Lie bracket.

**Definition 1.6 (blockW).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\iota : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (\alpha : \operatorname{Type}), (\forall (label : (\iota \to \alpha)), (\forall (w : (\alpha \to V)), (\forall (a : \alpha), (\operatorname{Decomposition}.\operatorname{blockW}\left(b, label, w, a\right) = (\operatorname{Submodule}.\operatorname{span}\left(k, \operatorname{Set}.\operatorname{range}\left((\operatorname{fun} c \mapsto (\operatorname{fun} (i : \{i : \iota \mid label\left(i\right) = (a)\}) \mapsto b.\operatorname{repr}\left(w\left(c\right), \operatorname{val}\left(i\right)\right)))\right)\right))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.blockW` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The subspace in each block is spanned by the coordinate restrictions of all square representatives.

**Definition 1.7 (squareRepresentative).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (\iota : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (a : \operatorname{Set}.\operatorname{range}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)), (\operatorname{Rescaling}.\operatorname{squareRepresentative}\left(\mu, b\right)\left(a\right) = (\mu\left(b\left(\operatorname{Classical}.\operatorname{choose}\left(a.\operatorname{property}\left(\right)\right)\right), b\left(\operatorname{Classical}.\operatorname{choose}\left(a.\operatorname{property}\left(\right)\right)\right)\right))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.squareRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For each line spanned by a natural square, choose one basis index generating that line and take its square.

**Theorem 1.8 (nonzero square block decomposition).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ([\operatorname{IsAlgClosed}\left(k\right)] \forall (\iota : \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, \operatorname{derivations}\left(\mu\right)\right)] (\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b\left(i\right), b\left(j\right)\right) = (0))))) \Rightarrow ((\forall (i : \iota), (\mu\left(b\left(i\right), b\left(i\right)\right) \ne 0)) \Rightarrow (\exists (b' : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), ((\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b'\left(i\right), b'\left(j\right)\right) = (0))))) \land ((\forall (i : \iota), (\mu\left(b'\left(i\right), b'\left(i\right)\right) = (\operatorname{Rescaling}.\operatorname{squareRepresentative}\left(\mu, b\right)\left(\operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)\left(i\right)\right)))) \land (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{derivations}\left(\mu\right), \operatorname{DirectSum}\left(\operatorname{Set}.\operatorname{range}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right), (\operatorname{fun} a \mapsto \operatorname{stabilizer}\left(\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(\{i : \iota \mid \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)\left(i\right) = (a)\}, \{i : \iota \mid \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)\left(i\right) = (a)\}, k\right)\right), \operatorname{Decomposition}.\operatorname{blockW}\left(b', \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right), \operatorname{Rescaling}.\operatorname{squareRepresentative}\left(\mu, b\right), a\right)\right))\right)\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.nonzero_square_block_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Rescaling the natural basis makes squares identical within each proportionality class. Perfectness eliminates diagonal coefficients of derivations. Independent skew maps killing the projected squares then give all derivations, including the converse construction.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.blockW`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.mul_basis_left`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.mul_basis_right`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.nonzero_square_block_decomposition`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piDirectSumEquiv`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piLieAlgebra`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piLieRing`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.squareRepresentative`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction](DerivationAnnihilatorObstruction.md)
- Dependency: [D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers](../OrthogonalPointwiseStabilizers.md)
