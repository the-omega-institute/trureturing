# Squared-Catalan Hankel Growth

## Abstract

The literal squared-Catalan Hankel matrices are positive product Gram matrices with explicit Chebyshev upper bounds.

**Definition 1.1 (The scaled beta source measure).**

Lean statement: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanBetaMeasure`

*Formalization.* `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanBetaMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gwo Dong Lin (2018). *On Powers of the Catalan Number Sequence*. DOI: [10.1016/j.disc.2018.05.009](https://doi.org/10.1016/j.disc.2018.05.009). URL: <https://arxiv.org/abs/1711.01536v3>.

*Commentary.*

The beta distribution has parameters one half and three halves. Scaling its coordinate by four puts the Catalan law on the interval from zero to four. The proof evaluates the density integral literally; no moment identity is assumed as an axiom or imported theorem.

**Definition 1.2 (Literal Catalan moments).**

Lean statement: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanMoment`

*Formalization.* `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gwo Dong Lin (2018). *On Powers of the Catalan Number Sequence*. DOI: [10.1016/j.disc.2018.05.009](https://doi.org/10.1016/j.disc.2018.05.009). URL: <https://arxiv.org/abs/1711.01536v3>.

*Commentary.*

The m-th moment is the integral of (4*x)^m against the beta measure. The proof expands the beta density, evaluates the beta and gamma factors, and obtains exactly Catalan(m), including m=0.

**Definition 1.3 (Products give squared Catalan moments).**

Lean statement: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanProductMoment`

*Formalization.* `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanProductMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gwo Dong Lin (2018). *On Powers of the Catalan Number Sequence*. DOI: [10.1016/j.disc.2018.05.009](https://doi.org/10.1016/j.disc.2018.05.009). URL: <https://arxiv.org/abs/1711.01536v3>.

*Commentary.*

Two independent copies are combined with the product measure. Product integration separates the powers and turns the literal product moment into Catalan(m)^2. This is the measure actually used by the Hankel Gram matrices.

**Definition 1.4 (The exact shifted matrices).**

Lean statement: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanSquareHankelMatrix`

*Formalization.* `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanSquareHankelMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2016). *OEIS A277829 and A278770: squared-Catalan Hankel determinants*. URL: <https://oeis.org/A277829>.

*Commentary.*

At size n and shift r the Fin n matrix has entry Catalan(i+j+r)^2. Thus r=1 is OEIS A277829 and r=2 is A278770 after converting their one-based program indices to zero-based Fin indices.

**Definition 1.5 (The determinant convention).**

Lean statement: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanSquareHankelDet`

*Formalization.* `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanSquareHankelDet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2016). *OEIS A277829 and A278770: squared-Catalan Hankel determinants*. URL: <https://oeis.org/A277829>.

*Commentary.*

The determinant is taken over the exact shifted matrix. At n=0 this is the empty determinant and equals one, so the all-n positivity theorem has no exceptional base-case convention outside Lean.

**Theorem 1.6 (Both determinant sequences are strictly positive).**

Lean statement: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalan_square_hankel_det_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalan_square_hankel_det_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2016). *OEIS A277829 and A278770: squared-Catalan Hankel determinants*. URL: <https://oeis.org/A277829>.

*Acknowledgement.* Gwo Dong Lin (2018). *On Powers of the Catalan Number Sequence*. DOI: [10.1016/j.disc.2018.05.009](https://doi.org/10.1016/j.disc.2018.05.009). URL: <https://arxiv.org/abs/1711.01536v3>.

*Commentary.*

Clipped bounded coordinates agree with the literal product coordinate on the support. Weighted powers are linearly independent because a polynomial vanishing almost everywhere on the positive open support vanishes identically. Transport to L2 gives positive-definite Gram matrices for both shifts. The entry calculation uses the literal product moment, and the Hadamard product of the corresponding Catalan Gram matrix with itself has positive determinant. This proves both positivity conjuncts for every n, including zero.

**Theorem 1.7 (Monic Chebyshev-T upper bounds).**

Lean statement: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalan_square_hankel_det_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalan_square_hankel_det_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2016). *OEIS A277829 and A278770: squared-Catalan Hankel determinants*. URL: <https://oeis.org/A277829>.

*Acknowledgement.* Gwo Dong Lin (2018). *On Powers of the Catalan Number Sequence*. DOI: [10.1016/j.disc.2018.05.009](https://doi.org/10.1016/j.disc.2018.05.009). URL: <https://arxiv.org/abs/1711.01536v3>.

*Commentary.*

An affine map sends the product support [0,16] to [-1,1]. Properly scaled Chebyshev-T polynomials are monic and replace the power basis by a unit triangular change, so the Gram determinant is unchanged. Their uniform bound controls every changed Gram diagonal. The positive-definite Hadamard inequality then gives the exact factors 4^n and 16^n and the common factor 16^(n*(n-1)/2), without an extra n factorial.

## References

- Truth anchor: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanBetaMeasure`
- Truth anchor: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanMoment`
- Truth anchor: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanProductMoment`
- Truth anchor: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanSquareHankelDet`
- Truth anchor: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalanSquareHankelMatrix`
- Truth anchor: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalan_square_hankel_det_positive`
- Truth anchor: `D5/S3/Constants/Moments/CatalanSquareHankelGrowth.catalan_square_hankel_det_upper`
- Dependency: [D5/S3/Arith/GoldenResource/IntegerHadamard](../../Arith/GoldenResource/IntegerHadamard.md)
