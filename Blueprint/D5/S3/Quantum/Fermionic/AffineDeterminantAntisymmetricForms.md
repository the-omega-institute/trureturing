# Low-degree alternating polynomials and the affine determinant

## Abstract

Alternating complex polynomials of total degree at most d in d+1 vector variables are scalar affine determinants; with more variables they vanish.

**Definition 1.1 (Alternation in the vector variables).**

$$\forall (r: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (f: \operatorname{MvPolynomial}\left((\operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.IsAlternating}\left(f\right)) \Leftrightarrow (\forall (\sigma: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(r\right)\right)), (\operatorname{DFunLike.coe}\left(\operatorname{MvPolynomial.rename}\left(\operatorname{DFunLike.coe}\left(\operatorname{Equiv.prodCongr}\left(\sigma, \operatorname{Equiv.refl}\left(\operatorname{Fin}\left(d\right)\right)\right)\right)\right)\right)\left(f\right) = ((\operatorname{Int.cast}\left((\operatorname{Units.val}\left(\operatorname{DFunLike.coe}\left(\operatorname{Equiv.Perm.sign}\right)\left(\sigma\right)\right): \mathbb{Z})\right): \mathbb{C})) \cdot (f))))))$$

*Formalization.* `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.IsAlternating` (`✓ std3`).

*Citation.* Michel Rouleux (2019). *Multimode entanglement for fermions*. DOI: [10.48550/arXiv.1910.04790](https://doi.org/10.48550/arXiv.1910.04790). URL: <https://arxiv.org/abs/1910.04790v1>.

*Commentary.*

The indices in Fin r label vectors, and those in Fin d label their coordinates. A permutation acts on the vector index and fixes the coordinate index. IsAlternating requires renaming the polynomial by this action to multiply it by the permutation sign. The sign is first mapped from the units of the integers to the integers by Units.val, then to the complex numbers by Int.cast. DFunLike.coe displays the underlying functions of the permutation equivalence, renaming algebra homomorphism and sign homomorphism. This is the polynomial form of the source's antisymmetry in Section 3, lines 234–248 of 3fermiProc.tex in arXiv:1910.04790v1; no multilinearity is required.

**Definition 1.2 (The determinant of differences).**

$$\forall (d: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.affineDet}\left(d\right): \operatorname{MvPolynomial}\left((\operatorname{Fin}\left(d + 1\right)) \times (\operatorname{Fin}\left(d\right)), \mathbb{C}\right)) = \operatorname{Matrix.det}\left(\lambda (j: \operatorname{Fin}\left(d\right)) \mapsto (\lambda (k: \operatorname{Fin}\left(d\right)) \mapsto (\operatorname{MvPolynomial.X}\left((\operatorname{Fin.succ}\left(k\right), j)\right) - \operatorname{MvPolynomial.X}\left(((0: \operatorname{Fin}\left(d + 1\right)), j)\right)))\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.affineDet` (`✓ std3`).

*Citation.* Michel Rouleux (2019). *Multimode entanglement for fermions*. DOI: [10.48550/arXiv.1910.04790](https://doi.org/10.48550/arXiv.1910.04790). URL: <https://arxiv.org/abs/1910.04790v1>.

*Commentary.*

Definition 3, lines 251–253, takes the determinant of the d columns obtained by subtracting the first point from each remaining point. Here X(k.succ,j) is coordinate j of the point indexed by k.succ, and X(0,j) is coordinate j of the first point. The row index is j and the column index is k. At d equal to zero the empty determinant is one.

**Definition 1.3 (Non-degeneracy through affine dimension).**

$$\forall (d: \mathbb{N}), (\forall (\omega: ((\operatorname{Fin}\left(d + 1\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{C}))) \to (\mathbb{C})), ((\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.IsNondegenerate}\left(d, \omega\right)) \Leftrightarrow (\forall (x: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{C}))), ((\forall (x_{0}: (\operatorname{Fin}\left(d\right)) \to (\mathbb{C})), (\omega\left(\operatorname{Fin.cons}\left(x_{0}, x\right)\right) = (0: \mathbb{C}))) \Rightarrow (\operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{Subtype}\left(\operatorname{SetLike.coe}\left(\operatorname{AffineSubspace.direction}\left(\operatorname{affineSpan}\left(\mathbb{C}, \operatorname{Set.range}\left(x\right)\right)\right)\right)\right)\right) \le (d - 2: \mathbb{N}))))))$$

*Formalization.* `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.IsNondegenerate` (`✓ std3`).

*Citation.* Michel Rouleux (2019). *Multimode entanglement for fermions*. DOI: [10.48550/arXiv.1910.04790](https://doi.org/10.48550/arXiv.1910.04790). URL: <https://arxiv.org/abs/1910.04790v1>.

*Commentary.*

For every family x of d points in the coordinate space Fin d → ℂ, suppose that inserting any first point x₀ makes ω vanish. Non-degeneracy requires the direction of the affine span of those d points to have complex dimension at most d minus two. This expresses the source's condition in lines 262–263 using the smallest affine subspace containing the points. Subtype applied to SetLike.coe of the direction explicitly denotes its underlying vector-space type. The subtraction d minus two is natural-number subtraction; the non-degeneracy conclusion below assumes d at least two.

**Theorem 1.4 (Vanishing, classification and non-degeneracy).**

$$(\forall (d: \mathbb{N}), (\forall (r: \mathbb{N}), ((d + 2 \le r) \Rightarrow (\forall (f: \operatorname{MvPolynomial}\left((\operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.IsAlternating}\left(f\right)) \Rightarrow ((\operatorname{MvPolynomial.totalDegree}\left(f\right) \le d) \Rightarrow (f = (0: \operatorname{MvPolynomial}\left((\operatorname{Fin}\left(r\right)) \times (\operatorname{Fin}\left(d\right)), \mathbb{C}\right))))))))) \land ((\forall (d: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.IsAlternating}\left(\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.affineDet}\left(d\right)\right)) \land (\operatorname{MvPolynomial.totalDegree}\left(\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.affineDet}\left(d\right)\right) \le d))) \land ((\forall (d: \mathbb{N}), (\forall (f: \operatorname{MvPolynomial}\left((\operatorname{Fin}\left(d + 1\right)) \times (\operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.IsAlternating}\left(f\right)) \Rightarrow ((\operatorname{MvPolynomial.totalDegree}\left(f\right) \le d) \Rightarrow (\exists (c: \mathbb{C}), (f = (c) \cdot (\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.affineDet}\left(d\right)))))))) \land (\forall (d: \mathbb{N}), ((2 \le d) \Rightarrow (\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.IsNondegenerate}\left(d, \lambda (y: (\operatorname{Fin}\left(d + 1\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{C}))) \mapsto (\operatorname{DFunLike.coe}\left(\operatorname{MvPolynomial.eval}\left(\lambda (p: (\operatorname{Fin}\left(d + 1\right)) \times (\operatorname{Fin}\left(d\right))) \mapsto (y\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right)\right))\right)\right)\left(\operatorname{D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.affineDet}\left(d\right)\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.result` (`✓ std3`). ∎

*Resolves.* `Problems/rouleux-2019-affine-determinant-antisymmetric-forms` (proved) by `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rouleux-2019-affine-determinant-antisymmetric-forms","declaration_gid":"D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michel Rouleux (2019). *Multimode entanglement for fermions*. DOI: [10.48550/arXiv.1910.04790](https://doi.org/10.48550/arXiv.1910.04790). URL: <https://arxiv.org/abs/1910.04790v1>.

*Commentary.*

Represent a monomial by its exponent array m, with one row in ℕ^d for each vector variable. Alternation relates the coefficient at a permuted array to the original coefficient multiplied by the permutation sign. If two rows coincide, their transposition fixes the monomial and negates its coefficient. Over ℂ that coefficient is zero. Thus every monomial with nonzero coefficient has pairwise distinct exponent rows.

The total exponent sum is the sum of the row sums. Among distinct rows at most one is zero, and each remaining row contributes at least one. Consequently r distinct rows have total exponent sum at least r minus one. With d+1 rows and total exponent sum at most d, there must be one zero row and all other row sums must equal one. Those other rows are distinct coordinate unit vectors, so they comprise all d unit vectors. Every such monomial is therefore a permutation of the monomial with zero row at index zero and the kth unit row at index k.succ.

If r is at least d+2, the row-count bound contradicts total degree at most d for any monomial in the support. Every coefficient must vanish, proving the first conjunct.

To prove alternation of the affine determinant, adjoin a row of ones above the matrix of point coordinates. Transpose this bordered matrix and subtract its first row from every other row. These row operations preserve its determinant; expansion along the first column leaves the transpose of the matrix of differences. Thus the bordered determinant equals the affine determinant. Renaming the point variables permutes the columns of the bordered matrix, multiplying its determinant by the permutation sign. Expanding the determinant of differences gives a sum of products of d linear polynomials, so its total degree is at most d. This proves the second conjunct.

The coefficient of the distinguished monomial, the product of X(k.succ,k) over k in Fin d, is one in the affine determinant. To see this, retain only these d variables and set every other variable to zero. The matrix of differences becomes diagonal, and its determinant is their product; the coefficient is preserved by this restriction.

Let c be the coefficient of that monomial in f, and subtract c times the affine determinant. The difference is still alternating, has total degree at most d, and has zero coefficient at the distinguished monomial. Every monomial in its support would be a permutation of that monomial, and the coefficient relation would force its coefficient to be zero. Hence the difference vanishes, proving the third conjunct with this c.

For the fourth conjunct let d be at least two, and suppose the evaluated affine determinant vanishes for every first point x₀. The dimension bound for the direction of the affine span of d points is equivalent to their failure to be affinely independent. Assume instead that the d points are affinely independent. Their affine span is a proper affine subspace of the d-dimensional ambient affine space, so choose x₀ outside it. Inserting x₀ gives d+1 affinely independent points. Their d differences from x₀ are linearly independent, so the square matrix having these columns has nonzero determinant. Evaluation of the polynomial affine determinant is exactly this matrix determinant, contradicting the assumed vanishing. The direction dimension is therefore at most d minus two.

The four conjuncts give a scalar-polynomial reading of the two conjectures in lines 266–269. The total-degree bound includes homogeneous polynomials of degree d. The separate collapse conjecture in lines 271–272 is outside these statements.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.IsAlternating`
- Truth anchor: `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.IsNondegenerate`
- Truth anchor: `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.affineDet`
- Truth anchor: `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.result`
- Dependency: [D5/S3/Arith/Lattices/CofactorKernel](../../Arith/Lattices/CofactorKernel.md)
