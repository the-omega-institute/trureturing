# The minimum separation rank of a quadratic weighted Hankel kernel

## Abstract

Three nearby evaluation points exclude two-term separation of every nonzero continuous quadratic weighted Hankel kernel.

**Theorem 1.1 (A nonzero three-point evaluation minor).**

Lean statement: `D5/S3/Analytic/Entire/WeightedHankelLowerRank.weighted_hankel_three_point_minor`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/WeightedHankelLowerRank.weighted_hankel_three_point_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero continuous complex f has three complex points whose weighted Hankel evaluation matrix has nonzero determinant. Continuity near a point where f is nonzero supplies three distinct nearby points with every off-diagonal entry nonzero and diagonal zero. This minor is consumed both in the universal lower bound and in the independent-exponent block obstruction.

**Theorem 1.2 (A nonzero continuous kernel needs at least three terms).**

Lean statement: `D5/S3/Analytic/Entire/WeightedHankelLowerRank.not_separated_two_weighted_hankel`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/WeightedHankelLowerRank.not_separated_two_weighted_hankel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every continuous f from Complex to Complex that is not the zero function, the kernel (z-w)^2*f(z+w) has no representation by at most two entire separated terms. Choose a point a with f(a) nonzero and put x=a/2. Continuity supplies a nonzero small t such that f(2*x+t) and f(2*x-t) remain nonzero. At the three points x, x+t, x-t, the symmetric evaluation matrix has zero diagonal and all three off-diagonal entries nonzero. Its determinant is twice their product. Every sum of two separated terms has zero determinant on any such three-by-three evaluation matrix. No polynomial, finite support, finite separation, growth bound or Fock-vector premise on f is used.

**Theorem 1.3 (Three terms for an exponential).**

Lean statement: `D5/S3/Analytic/Entire/WeightedHankelLowerRank.separated_three_exponential`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/WeightedHankelLowerRank.separated_three_exponential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all complex c and alpha, including c=0, the weighted kernel of c*exp(alpha*z) has at most three entire separated terms. Expand the squared difference z^2-2*z*w+w^2 and split the exponential of the sum into a product.

**Theorem 1.4 (Three terms for a shifted square).**

Lean statement: `D5/S3/Analytic/Entire/WeightedHankelLowerRank.separated_three_exponential_square`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Entire/WeightedHankelLowerRank.separated_three_exponential_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all complex c, alpha and beta, the weighted kernel of c*exp(alpha*z)*(z-beta)^2 also has at most three entire separated terms. Set p(z)=z^2-beta*z. Then (z-w)*(z+w-beta)=p(z)-p(w), whose square is a sum of three separated terms. These two explicit constructions supply the sufficiency direction of the physical rank-three statement. Exhaustiveness of those profiles requires the separate polynomial-block classification.

## References

- Truth anchor: `D5/S3/Analytic/Entire/WeightedHankelLowerRank.not_separated_two_weighted_hankel`
- Truth anchor: `D5/S3/Analytic/Entire/WeightedHankelLowerRank.separated_three_exponential`
- Truth anchor: `D5/S3/Analytic/Entire/WeightedHankelLowerRank.separated_three_exponential_square`
- Truth anchor: `D5/S3/Analytic/Entire/WeightedHankelLowerRank.weighted_hankel_three_point_minor`
- Dependency: [D5/S3/Analytic/Entire/WeightedHankel](WeightedHankel.md)
