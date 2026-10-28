# Bilinear defect gaps

## Abstract

Fourth moments and uniform bilinear defect gaps.

**Definition 1.1 (A diagonal bilinear form).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.bilinearKernel`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.bilinearKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real coefficient vector q and coordinate vectors x,y, the kernel is the sum of q(i)x(i)y(i). It is symmetric in its two arguments. Neither the coefficients nor the coordinate vectors are required to be nonnegative.

**Definition 1.2 (Empirical sign and row defects).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.empiricalDefect`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.empiricalDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n coordinate vectors, average the squared sign residual (H(x(r),x(s))^2-1)^2 over ordered pairs, and add the average squared difference between each normalized kernel row sum and c. The first term is separately quartic in the two vectors. The second becomes quadratic in one vector when the empirical coordinate mean is fixed.

**Theorem 1.3 (A gap independent of sample size).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.bilinear_defect_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.bilinear_defect_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonsquare coordinate dimension k and every common entry bound M, there is a positive lower bound on the empirical defect at c=1/sqrt(k), uniform over every positive sample size, every real coefficient vector, and every family whose kernel values have absolute value at most M. Fourth-moment compression gives exactly choose(k+4,4)+1 weighted nodes from the family. Powers of the bilinear form expand as finite sums of products of monomials. The first and second defects, and the coordinate mean used in the second, are preserved exactly. The resulting bounded symmetric model is subject to the fixed-order positive defect gap.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.bilinearKernel`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.bilinear_defect_gap`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.empiricalDefect`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/Compactness](Compactness.md)
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression](MomentCompression.md)
