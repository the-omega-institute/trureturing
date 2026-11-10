# Sun's complete determinant assertion

## Abstract

The literal finite sum satisfies every clause at every natural index.

Nat denotes the nonnegative integers and Z the integers. Matrix.of is displayed with Fin-sized row and column binders and explicit val projections; det of the empty matrix is one. All floor quotients are natural division.

**Definition 1.1 (All clauses of the assertion).**

$$claim \Leftrightarrow \left(\forall n \in Nat,\; \left(n \bmod 3 = 1 \Rightarrow W\left(n\right) = 0\right) \land \left(\left(\neg n \bmod 3 = 1\right) \Rightarrow \left(\exists z \in \mathbb{Z},\; 0 < z \land \left(Odd\left(z\right) \land \left(-1\right)^{\left\lfloor\frac{n + 1}{3}\right\rfloor} \cdot W\left(n\right) = 6^{n} \cdot z\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hankel/SunA006077Result.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

The zero branch and the positive odd integral normalized branch both quantify over every natural n, including n=0. No prime congruence from a later version is included.

**Theorem 1.2 (The full all-index statement).**

$$\forall n \in Nat,\; \left(n \bmod 3 = 1 \Rightarrow W\left(n\right) = 0\right) \land \left(\left(\neg n \bmod 3 = 1\right) \Rightarrow \left(\exists z \in \mathbb{Z},\; 0 < z \land \left(Odd\left(z\right) \land \left(-1\right)^{\left\lfloor\frac{n + 1}{3}\right\rfloor} \cdot W\left(n\right) = 6^{n} \cdot z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hankel/SunA006077Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/sun-a006077-hankel-determinants` (proved) by `D5/S3/Combinatorics/Hankel/SunA006077Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sun-a006077-hankel-determinants","declaration_gid":"D5/S3/Combinatorics/Hankel/SunA006077Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zhi-Wei Sun (2013). *On some determinants with Legendre symbol entries*. DOI: [10.48550/arXiv.1308.2900](https://doi.org/10.48550/arXiv.1308.2900). URL: <https://arxiv.org/abs/1308.2900v5>.

*Commentary.*

The odd integral quotients d(m) and e(m) are nonzero, so their positive semidefinite real Hankel matrices are positive definite. Their determinants and therefore d(m),e(m) are positive. At indices 3m and 3m+2 the signed quotients are respectively d(m)e(m)^2 and d(m)e(m+1)^2. Both are positive odd integers; the remaining residue class vanishes. The index zero and empty shifted determinants are included. This states the v5 conjecture for its original finite sum. The zero branch, Rueppel parity evaluations and positive moment ingredients are established prior mathematics; this statement makes no claim of priority for their combination.

## References

- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Result.claim`
- Truth anchor: `D5/S3/Combinatorics/Hankel/SunA006077Result.result`
- Dependency: [D5/S3/Combinatorics/Hankel/SunA006077Arithmetic](SunA006077Arithmetic.md)
- Dependency: [D5/S3/Combinatorics/Hankel/SunA006077Positivity](SunA006077Positivity.md)
