# Dividing multinomial coefficients by six

## Abstract

The quotient coefficient is odd exactly at positive powers of two.

For a sequence b, H(b,k,s) is the k by k matrix with entry b(i+j+s), where 0 <= i,j < k; det of the empty matrix is one. Nat denotes the nonnegative integers, Z the integers, and all floor quotients are natural division.

**Definition 1.1 (An explicit integral quotient).**

$$\forall r \in Nat,\; q\left(r\right) = choose\left(NatSub\left(2 \cdot r, 1\right), NatSub\left(r, 1\right)\right) \cdot choose\left(NatSub\left(3 \cdot r, 1\right), NatSub\left(r, 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

NatSub is natural subtraction. The quotient relation is used only for positive r; the definition also fixes q(0).

**Theorem 1.2 (Exact divisibility by six).**

$$\forall r \in Nat,\; 0 < r \Rightarrow c\left(r\right) = 6 \cdot q\left(r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.c_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

Twice and three times the respective reduced binomial coefficients recover the two original binomial factors.

**Theorem 1.3 (Parity detects powers of two).**

$$\forall r \in Nat,\; 0 < r \Rightarrow \left(Odd\left(q\left(r\right)\right) \Leftrightarrow \left(\exists k \in Nat,\; r = 2^{k}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.q_odd_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

Kummer valuations express the central binomial valuation as the binary digit sum of r. Equality to one forces one binary digit; at a power of two the second binomial factor is odd.

**Definition 1.4 (Unshifted normalized determinant).**

$$\forall m \in Nat,\; d\left(m\right) = det\left(A\left(m\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.d` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

A(m) has size m+1. Its first row has entries c(j); every other row i has entries q(i+j).

**Definition 1.5 (Shifted normalized determinant).**

$$\forall m \in Nat,\; e\left(m\right) = det\left(H\left(q, m, 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.e` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

All m rows of the shifted determinant are divided by six.

**Theorem 1.6 (The unshifted exact factor).**

$$\forall m \in Nat,\; D\left(m + 1\right) = 6^{m} \cdot d\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.D_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

Each row except the first has a positive coefficient index and contributes one factor of six.

**Theorem 1.7 (The shifted exact factor).**

$$\forall m \in Nat,\; E\left(m\right) = 6^{m} \cdot e\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.E_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

Each shifted row contributes one factor of six, including the empty-size convention.

**Theorem 1.8 (Both integral quotients are odd).**

$$\forall m \in Nat,\; Odd\left(d\left(m\right)\right) \land Odd\left(e\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.normalized_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

Modulo two the shifted determinant is S(m). The unshifted first row reduces to (1,0,...,0), and its first cofactor is T(m). Both equal one.

## References

- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.D_normalization`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.E_normalization`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.c_six`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.d`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.e`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.normalized_odd`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.q`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Arithmetic.q_odd_iff`
- Dependency: [D5/S3/Combinatorics/Hankel/SunA006077Binary](SunA006077Binary.md)
