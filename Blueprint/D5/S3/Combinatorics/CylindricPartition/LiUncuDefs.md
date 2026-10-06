# The Finite Andrews-Gordon Companion Polynomials

## Abstract

Gaussian binomials with a primed boundary convention define the two polynomial sums in the finite Andrews-Gordon companion identity.

**Definition 1.1 (Gaussian polynomials).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gauss`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gauss` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For nonnegative integers a and b, G(a,0) = 1 and G(0,b+1) = 0. The recurrence G(a+1,b+1) = G(a,b+1) + q^(a-b) G(a,b) defines the Gaussian polynomial, with natural-number subtraction in the exponent.

**Definition 1.2 (Integer-indexed Gaussian polynomials).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gaussInt`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gaussInt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For integers a and b, the Gaussian polynomial is zero when either index is negative, and otherwise is G(a,b) with nonnegative indices. It also vanishes when b exceeds a.

**Definition 1.3 (The primed boundary convention).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gaussPrime`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gaussPrime` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

The primed Gaussian polynomial equals one whenever its lower index is zero, even if the upper index is negative. For every other lower index it equals the integer-indexed Gaussian polynomial.

**Definition 1.4 (The boundary shift).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.alpha`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For nonnegative integers i and j, alpha(i,j) is the maximum of j - i + 1 and zero, computed in the integers.

**Definition 1.5 (Tuple entries with zero extension).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.entry`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.entry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

A tuple has k - 1 entries between zero and n. Its jth entry is read with indices starting at one when 1 is at most j and j is at most k - 1; all other entries are zero.

**Definition 1.6 (A multiple-sum term).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.leftTerm`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.leftTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

Write n_j for the zero-extended tuple entries. The term is q raised to the sum of n_j squared for j from one to k - 1 plus the sum of n_j for j from i to k - 1, multiplied by the primed Gaussian factors with upper index 2n - 2 times the sum of n_l for 1 at most l and l less than j, minus n_j, n_(j+1), and 2 alpha(i,j), and lower index n_j - n_(j+1). The product runs from j = 1 through k - 1. Exponents are converted to nonnegative integers by truncation at zero.

**Definition 1.7 (The finite multiple sum).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.lhs`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.lhs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

The left polynomial is the sum of leftTerm over all weakly decreasing tuples of k - 1 entries between zero and n.

**Definition 1.8 (An alternating Gaussian term).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.rightTerm`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.rightTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For an integer r, put epsilon = 0 when r is even and epsilon = -1 when r is odd. The term is (-1)^abs(r) times q raised to r((2k+1)r + 2k - 2i + 1)/2, multiplied by the integer-indexed Gaussian polynomial with upper index 2n and lower index (2n - (2k+1)r + (2k-2i+1)epsilon)/2. Integer division is used and the exponent is truncated at zero before taking the power.

**Definition 1.9 (The finite alternating sum).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.rhs`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.rhs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

The right polynomial is the sum of rightTerm over all integers r from -(n+1) through n+1, inclusive.

**Definition 1.10 (The companion identity).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.claim`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For every nonnegative integer n, every integer k at least five, and every integer i with 1 at most i and i less than k, the finite multiple sum lhs(n,k,i) equals the finite alternating sum rhs(n,k,i) as polynomials with integer coefficients.

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.alpha`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.entry`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gauss`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gaussInt`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gaussPrime`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.leftTerm`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.lhs`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.rhs`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.rightTerm`
