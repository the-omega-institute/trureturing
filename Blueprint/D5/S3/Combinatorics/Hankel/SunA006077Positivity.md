# Multinomial moment matrices

## Abstract

Beta integrals and the Schur product establish positive semidefiniteness.

For a sequence b, H(b,k,s) is the k by k matrix with entry b(i+j+s), where 0 <= i,j < k; det of the empty matrix is one. Nat denotes the nonnegative integers, Z the integers, and all floor quotients are natural division.

**Theorem 1.1 (Every nonnegative shift is positive semidefinite).**

$$\forall s \in Nat,\; \forall N \in Nat,\; PosSemidef\left(realCast\left(H\left(c, N, s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Positivity.multinomial_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

For 0<a<1 put mu(a,r)=(a)_r/r!. The normalized beta integral has these moments, and integrating t^s times a polynomial square gives a positive semidefinite matrix at every shift s. The identity c(r)=27^r mu(1/3,r) mu(2/3,r) follows from factorial recurrences. A Schur product, diagonal congruence by 27^i, and multiplication by 27^s give the stated matrix. Integrability follows from the beta integral with positive shifted shape. The positive-moment property of c is known, including Penson and Solomon, Example 9; the beta construction here uses the existing real beta integral declarations.

## References

- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Positivity.multinomial_posSemidef`
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../../Analytic/KummerRatio/BetaIntegral.md)
- Dependency: [D5/S3/Combinatorics/Hankel/SunA006077](SunA006077.md)
