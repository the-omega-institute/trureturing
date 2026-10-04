# The Weighted Image Formula

## Abstract

Four integer-indexed Gaussian image families enumerate paths in a floor-reflected strip.

**Definition 1.1 (The displacement kernel).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuImages.imageKernel`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuImages.imageKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For nonnegative L and integer d, the kernel is G(L,(L+d)/2) with integer indices when L+d is even, and zero otherwise.

**Definition 1.2 (The four image families).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuImages.imagePolynomial`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuImages.imagePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

Put p = 2H + 3 and i = H + 1 - a. Sum over all integers t the weight q^(2pt^2+(2a+1)t) times the kernels at displacements b-a-2pt and b+a+1+2pt. Subtract the sums of q^((2t+1)(pt+i)) times the kernels at displacements b-p+1+a-2pt and b+p-a+2pt. Each exponent is truncated at zero before taking a power. These are finite-support sums for endpoints in the strip.

**Theorem 1.3 (Images enumerate bounded paths).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuImages.path_image_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuImages.path_image_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For every H at least one, every nonnegative length L, and integer endpoints a and b between zero and H, imagePolynomial(H,L,a,b) equals pathPolynomial(H,L,a,b).

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuImages.imageKernel`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuImages.imagePolynomial`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuImages.path_image_formula`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuPaths](LiUncuPaths.md)
