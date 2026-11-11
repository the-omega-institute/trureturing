# Derivation blocks of nondegenerate evolution algebras

## Abstract

Stabilizer kernels and derivation blocks of nondegenerate evolution algebras.

**Definition 1.1 (The actual nondegenerate reduced block space).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\iota : \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] \forall (\alpha : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (label : (\iota \to \alpha)), (\forall (w : (\alpha \to V)), (\forall (a : \alpha), (\operatorname{Decomposition}.\operatorname{reducedBlockSpace}\left(b, label, w, a\right) = (\operatorname{Quotient}\left(\operatorname{orthogonal}\left(\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(\{i : \iota \mid label\left(i\right) = (a)\}, \{i : \iota \mid label\left(i\right) = (a)\}, k\right)\right), \operatorname{Decomposition}.\operatorname{blockW}\left(b, label, w, a\right)\right), \operatorname{ker}\left(\operatorname{restrict}\left(\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(\{i : \iota \mid label\left(i\right) = (a)\}, \{i : \iota \mid label\left(i\right) = (a)\}, k\right)\right), \operatorname{orthogonal}\left(\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(\{i : \iota \mid label\left(i\right) = (a)\}, \{i : \iota \mid label\left(i\right) = (a)\}, k\right)\right), \operatorname{Decomposition}.\operatorname{blockW}\left(b, label, w, a\right)\right)\right)\right)\right))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.reducedBlockSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a field k, a k-vector space V, a finite index type I, an arbitrary class index type alpha, a basis b, a class label and square representatives w, put B equal to the standard symmetric form on the coordinate space of the fiber over a, W equal to blockW(b,label,w,a), and U equal to the B-orthogonal complement of W. The reduced space is the actual quotient U/ker(B restricted to U), with its canonical additive group, k-module and finite-dimensional structure. This definition permits empty fibers and degenerate or isotropic W.

**Definition 1.2 (The induced nondegenerate block form).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\iota : \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] \forall (\alpha : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (label : (\iota \to \alpha)), (\forall (w : (\alpha \to V)), (\forall (a : \alpha), (\forall (x : \operatorname{orthogonal}\left(\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(\{i : \iota \mid label\left(i\right) = (a)\}, \{i : \iota \mid label\left(i\right) = (a)\}, k\right)\right), \operatorname{Decomposition}.\operatorname{blockW}\left(b, label, w, a\right)\right)), (\forall (y : \operatorname{orthogonal}\left(\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(\{i : \iota \mid label\left(i\right) = (a)\}, \{i : \iota \mid label\left(i\right) = (a)\}, k\right)\right), \operatorname{Decomposition}.\operatorname{blockW}\left(b, label, w, a\right)\right)), (\operatorname{Decomposition}.\operatorname{reducedBlockForm}\left(b, label, w, a\right)\left(\operatorname{quotientClass}\left(x\right), \operatorname{quotientClass}\left(y\right)\right) = (\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(\{i : \iota \mid label\left(i\right) = (a)\}, \{i : \iota \mid label\left(i\right) = (a)\}, k\right)\right)\left(\operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right))))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.reducedBlockForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the actual reduced block quotient, the induced bilinear form evaluates representatives by the restriction of B to U. The kernel has been divided out, so the form is nondegenerate. The canonical pointwise-stabilizer quotient construction supplies its symmetry, nondegeneracy and the surjective reduced Lie action used below.

**Definition 1.3 (The actual reduced orthogonal Lie algebra).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\iota : \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] \forall (\alpha : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (label : (\iota \to \alpha)), (\forall (w : (\alpha \to V)), (\forall (a : \alpha), (\operatorname{Decomposition}.\operatorname{reducedBlockLie}\left(b, label, w, a\right) = (\operatorname{skewAdjointLieSubalgebra}\left(\operatorname{Decomposition}.\operatorname{reducedBlockForm}\left(b, label, w, a\right)\right))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.reducedBlockLie` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the actual Lie subalgebra of skew-adjoint endomorphisms for the reduced block form, with its inherited commutator and k-linear structure. Naming its carrier and canonical Lie instances shares the same mathematical object throughout the dependent product and the full derivation action.

**Theorem 1.4 (Full derivations and nondegenerate reduced blocks).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ([\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (\iota : \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), ((\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b\left(i\right), b\left(j\right)\right) = (0))))) \Rightarrow ((\forall (i : \iota), (\mu\left(b\left(i\right), b\left(i\right)\right) \ne 0)) \Rightarrow (\exists (b' : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), ((\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b'\left(i\right), b'\left(j\right)\right) = (0))))) \land (\exists (f : \operatorname{LieHom}\left(k, \operatorname{derivations}\left(\mu\right), \forall (a : \operatorname{Set}.\operatorname{range}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)), (\operatorname{skewAdjointLieSubalgebra}\left(\operatorname{Decomposition}.\operatorname{reducedBlockForm}\left(b', \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right), \operatorname{Rescaling}.\operatorname{squareRepresentative}\left(\mu, b\right), a\right)\right))\right)), ((\operatorname{Function}.\operatorname{Surjective}\left(f\right)) \land (\operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(\operatorname{LieHom}.\operatorname{ker}\left(f\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.nonzero_square_reduced_orthogonal_surjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over an algebraically closed field of characteristic zero, every finite natural basis with nonzero squares admits a normalization and an actual surjective Lie map from all actual derivations to the product of the reduced block skew algebras. The kernel is solvable. The map subtracts each class scalar diagonal before applying the canonical setwise-preserver quotient action. Pointwise-stabilizer lifts prove surjectivity. The common diagonal and reduced kernel embeds into a product of canonical kernels with zero triple brackets, and the remaining diagonal quotient is abelian. Every small, empty, isotropic and degenerate block is retained here; no semisimplicity hypothesis on derivations is imposed. The original semisimple full block decomposition remains a separate theorem with its original hypotheses. This is part of the supplied Ma-then-Zhang credited argument; the linear and Lie constructions retain classical credit.

**Definition 1.5 (piLieRing).**

$$\forall (\alpha : \operatorname{Type}), (\forall (H : (\alpha \to \operatorname{Type})), ([\forall (a : \alpha), (\operatorname{LieRing}\left(H\left(a\right)\right))] \operatorname{Pi}.\operatorname{piLieRing}\left(H\right) : \operatorname{LieRing}\left(\forall (a : \alpha), (H\left(a\right))\right) = (\{\operatorname{inferInstance}\left(\right) : \operatorname{AddCommGroup}\left(\forall (a : \alpha), (H\left(a\right))\right) \operatorname{with} \operatorname{bracket} := (\operatorname{fun} f \mapsto (\operatorname{fun} g \mapsto (\operatorname{fun} a \mapsto \operatorname{Bracket}.\operatorname{bracket}\left(f\left(a\right), g\left(a\right)\right))))\})))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piLieRing` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The dependent product has the pointwise Lie bracket and the existing pointwise additive group. Its Lie identities hold at every coordinate.

**Definition 1.6 (piLieAlgebra).**

$$\forall (k : \operatorname{Type}), ([\operatorname{CommRing}\left(k\right)] \forall (\alpha : \operatorname{Type}), (\forall (H : (\alpha \to \operatorname{Type})), ([\forall (a : \alpha), (\operatorname{LieRing}\left(H\left(a\right)\right))] [\forall (a : \alpha), (\operatorname{LieAlgebra}\left(k, H\left(a\right)\right))] \operatorname{Pi}.\operatorname{piLieAlgebra}\left(k, H\right) : \operatorname{LieAlgebra}\left(k, \forall (a : \alpha), (H\left(a\right))\right) = (\{(\operatorname{inferInstance}\left(\right) : \operatorname{Module}\left(k, \forall (a : \alpha), (H\left(a\right))\right)) \operatorname{with}\}))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piLieAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The dependent product extends the existing pointwise module with the coordinatewise proof of compatibility between the Lie bracket and scalar multiplication. The record has no additional data fields.

**Definition 1.7 (piDirectSumEquiv).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (\beta : \operatorname{Type}), ([\operatorname{Fintype}\left(\beta\right)] \forall (H : (\beta \to \operatorname{Type})), ([\forall (a : \beta), (\operatorname{LieRing}\left(H\left(a\right)\right))] [\forall (a : \beta), (\operatorname{LieAlgebra}\left(k, H\left(a\right)\right))] \operatorname{BlockLinear}.\operatorname{piDirectSumEquiv}\left(H\right) = (\{\operatorname{toLinearEquiv} := \operatorname{DirectSum}.\operatorname{linearEquivFunOnFintype}\left(k, \beta, H\right).\operatorname{symm}\}))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piDirectSumEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For a finite index type, the standard linear equivalence from products to direct sums preserves the componentwise Lie bracket.

**Definition 1.8 (blockW).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\iota : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (\alpha : \operatorname{Type}), (\forall (label : (\iota \to \alpha)), (\forall (w : (\alpha \to V)), (\forall (a : \alpha), (\operatorname{Decomposition}.\operatorname{blockW}\left(b, label, w, a\right) = (\operatorname{Submodule}.\operatorname{span}\left(k, \operatorname{Set}.\operatorname{range}\left((\operatorname{fun} c \mapsto (\operatorname{fun} (i : \{i : \iota \mid label\left(i\right) = (a)\}) \mapsto b.\operatorname{repr}\left(w\left(c\right), \operatorname{val}\left(i\right)\right)))\right)\right))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.blockW` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

The subspace in each block is spanned by the coordinate restrictions of all square representatives.

**Definition 1.9 (squareRepresentative).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (\iota : \operatorname{Type}), (\forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (a : \operatorname{Set}.\operatorname{range}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)), (\operatorname{Rescaling}.\operatorname{squareRepresentative}\left(\mu, b\right)\left(a\right) = (\mu\left(b\left(\operatorname{Classical}.\operatorname{choose}\left(a.\operatorname{property}\left(\right)\right)\right), b\left(\operatorname{Classical}.\operatorname{choose}\left(a.\operatorname{property}\left(\right)\right)\right)\right))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.squareRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

For each line spanned by a natural square, choose one basis index generating that line and take its square.

**Theorem 1.10 (The diagonal kernel without semisimplicity).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ([\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (\iota : \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), ((\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b\left(i\right), b\left(j\right)\right) = (0))))) \Rightarrow ((\forall (i : \iota), (\mu\left(b\left(i\right), b\left(i\right)\right) \ne 0)) \Rightarrow (\exists (b' : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), ((\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b'\left(i\right), b'\left(j\right)\right) = (0))))) \land ((\forall (i : \iota), (\mu\left(b'\left(i\right), b'\left(i\right)\right) = (\operatorname{Rescaling}.\operatorname{squareRepresentative}\left(\mu, b\right)\left(\operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)\left(i\right)\right)))) \land (\exists (K : \operatorname{LieIdeal}\left(k, \operatorname{derivations}\left(\mu\right)\right)), ((\operatorname{IsLieAbelian}\left(\operatorname{Quotient}\left(\operatorname{derivations}\left(\mu\right), K\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, K, \operatorname{DirectSum}\left(\operatorname{Set}.\operatorname{range}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right), (\operatorname{fun} a \mapsto \operatorname{stabilizer}\left(\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(\{i : \iota \mid \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)\left(i\right) = (a)\}, \{i : \iota \mid \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)\left(i\right) = (a)\}, k\right)\right), \operatorname{Decomposition}.\operatorname{blockW}\left(b', \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right), \operatorname{Rescaling}.\operatorname{squareRepresentative}\left(\mu, b\right), a\right)\right))\right)\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.nonzero_square_diagonal_kernel_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Over an algebraically closed field of characteristic zero, let mu be any bilinear product on a vector space with a finite natural basis whose squares are all nonzero. Normalize those squares within their proportionality classes. The diagonal coefficients define an actual Lie homomorphism from derivations to the abelian algebra of scalar coordinate functions: every commutator has zero diagonal. Its actual kernel K is Lie equivalent to the finite direct sum of skew endomorphisms in each class that kill all projected square representatives. Thus Der(mu)/K is abelian, even when Der(mu) is not semisimple. Empty natural bases and empty sums are allowed. The kernel K here is not identified with the solvable radical, and this theorem does not yet give the radical quotient or the simple-ideal classification. The argument factors the existing general derivation equations, class normalization, assembly and restriction proofs; it does not remove the semisimplicity hypothesis from the existing full block equivalence. The underlying evolution-algebra source is the Ma-then-Zhang credited KMV note, alongside standard orthogonal Lie-algebra constructions.

**Theorem 1.11 (nonzero square block decomposition).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ([\operatorname{IsAlgClosed}\left(k\right)] \forall (\iota : \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, \operatorname{derivations}\left(\mu\right)\right)] (\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b\left(i\right), b\left(j\right)\right) = (0))))) \Rightarrow ((\forall (i : \iota), (\mu\left(b\left(i\right), b\left(i\right)\right) \ne 0)) \Rightarrow (\exists (b' : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), ((\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(b'\left(i\right), b'\left(j\right)\right) = (0))))) \land ((\forall (i : \iota), (\mu\left(b'\left(i\right), b'\left(i\right)\right) = (\operatorname{Rescaling}.\operatorname{squareRepresentative}\left(\mu, b\right)\left(\operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)\left(i\right)\right)))) \land (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{derivations}\left(\mu\right), \operatorname{DirectSum}\left(\operatorname{Set}.\operatorname{range}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right), (\operatorname{fun} a \mapsto \operatorname{stabilizer}\left(\operatorname{Matrix}.\operatorname{toLinearMap}_{2}'\left(k, 1 : \operatorname{Matrix}\left(\{i : \iota \mid \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)\left(i\right) = (a)\}, \{i : \iota \mid \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right)\left(i\right) = (a)\}, k\right)\right), \operatorname{Decomposition}.\operatorname{blockW}\left(b', \operatorname{Set}.\operatorname{rangeFactorization}\left((\operatorname{fun} i \mapsto k \cdot \mu\left(b\left(i\right), b\left(i\right)\right))\right), \operatorname{Rescaling}.\operatorname{squareRepresentative}\left(\mu, b\right), a\right)\right))\right)\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.nonzero_square_block_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Rescaling the natural basis makes squares identical within each proportionality class. Perfectness eliminates diagonal coefficients of derivations. Independent skew maps killing the projected squares then give all derivations, including the converse construction.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.blockW`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.nonzero_square_block_decomposition`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.nonzero_square_diagonal_kernel_decomposition`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.nonzero_square_reduced_orthogonal_surjection`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piDirectSumEquiv`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piLieAlgebra`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.piLieRing`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.reducedBlockForm`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.reducedBlockLie`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.reducedBlockSpace`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks.squareRepresentative`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations](NaturalBasisDerivationEquations.md)
- Dependency: [D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers](../OrthogonalPointwiseStabilizers.md)
