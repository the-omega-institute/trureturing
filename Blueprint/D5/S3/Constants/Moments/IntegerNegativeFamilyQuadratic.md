# Simultaneous integerization of negative subspaces

## Abstract

Simultaneous integerization of negative subspaces

**Theorem 1.1 (One integer matrix preserves a uniform negative gap).**

Lean statement: `D5/S3/Constants/Moments/IntegerNegativeFamilyQuadratic.exists_integer_negative_family_quadratic_of_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/IntegerNegativeFamilyQuadratic.exists_integer_negative_family_quadratic_of_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k,d, real matrix M on Fin d by Fin d, real row matrix A on Fin k by Fin d, and positive real gamma, suppose that for every real vector t on Fin k the form sum_ab (sum_j t(j) A(j,a)) (sum_l t(l) A(l,b)) M(a,b) is at most minus gamma times sum_j t(j) squared. There exists one integer row matrix U such that the same form using U after real casts is strictly negative for every nonzero real t. No symmetry of M is assumed. Empty row and column index sets are included.

The pullback Gram entries are finite polynomials in the whole row matrix. With eta equal to gamma divided by 2(k+1), a finite open intersection constrains every Gram-entry perturbation by eta. Nested componentwise rational density selects one rational matrix. The absolute change of the form is at most eta times (sum_j abs(t(j))) squared, at most gamma/2 times sum_j t(j) squared by finite Cauchy-Schwarz. Matrix.den and Matrix.num clear one nonzero denominator for all entries, multiplying the form by its positive square. Rows are never integerized separately.

**Theorem 1.2 (Strict negativity on every direction can be integerized simultaneously).**

Lean statement: `D5/S3/Constants/Moments/IntegerNegativeFamilyQuadratic.exists_integer_negative_family_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/IntegerNegativeFamilyQuadratic.exists_integer_negative_family_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k,d, arbitrary real matrix M on Fin d by Fin d, and real row matrix A on Fin k by Fin d, assume the pullback form sum_ab (sum_j t(j) A(j,a)) (sum_l t(l) A(l,b)) M(a,b) is strictly negative for every nonzero real t on Fin k. There exists one integer matrix U with that same strict inequality for every nonzero real t. Neither symmetry nor a supplied quantitative gap is assumed; k=0 is included.

On the compact unit sphere in the finite real Pi space, minus the pullback form divided by sum_j t(j) squared is continuous and positive. Compactness supplies a positive lower bound even when the sphere is empty. Normalize a nonzero vector and use degree-two homogeneity to obtain a uniform gap on all vectors. The preceding entrywise perturbation and common-denominator theorem then constructs U. This is finite-dimensional approximation of a supplied real negative subspace, not a statement that a particular spectral matrix has one.

## References

- Truth anchor: `D5/S3/Constants/Moments/IntegerNegativeFamilyQuadratic.exists_integer_negative_family_quadratic`
- Truth anchor: `D5/S3/Constants/Moments/IntegerNegativeFamilyQuadratic.exists_integer_negative_family_quadratic_of_gap`
- Dependency: [D5/S3/Constants/Moments/CountableHankelNegativeWitness](CountableHankelNegativeWitness.md)
