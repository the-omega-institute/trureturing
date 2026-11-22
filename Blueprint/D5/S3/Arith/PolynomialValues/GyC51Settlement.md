# Gy's coefficient log-concavity question

## Abstract

A common affine input family gives two symmetric triple-product differences whose coefficients fail log-concavity.

**Definition 1.1 (The first m inputs).**

$$\forall x \in \mathbb{N} \to \mathbb{R}[q],\; \forall m \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{inputPrefix}\left(x, m, i\right) = x\left(\operatorname{val}\left(i\right) + 1\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/GyC51Settlement.inputPrefix` (`✓ std3`).

*Citation.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

The prefix of size m is indexed by Fin m and begins at the sequence term x₁.

**Definition 1.2 (Coefficientwise order).**

$$\forall f \in \mathbb{R}[q],\; \forall g \in \mathbb{R}[q],\; \operatorname{qLe}\left(f, g\right) \Leftrightarrow \left(\forall k \in \mathbb{N},\; 0 \le \operatorname{coeff}\left(g - f, k\right)\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/GyC51Settlement.qLe` (`✓ std3`).

*Citation.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

The order compares every coefficient of the difference g − f.

**Definition 1.3 (Strong q-log-concavity).**

$$\forall x \in \mathbb{N} \to \mathbb{R}[q],\; \operatorname{StronglyQLogConcave}\left(x\right) \Leftrightarrow \left(\forall i \in \mathbb{N},\; \forall r \in \mathbb{N},\; i \le r \Rightarrow \operatorname{qLe}\left(x\left(i\right) \cdot x\left(r + 1\right), x\left(i + 1\right) \cdot x\left(r\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/GyC51Settlement.StronglyQLogConcave` (`✓ std3`).

*Citation.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

The source's left index is i + 1. Its predecessor is i, and r = i is the equality case.

**Definition 1.4 (The elementary symmetric sum).**

$$\forall x \in \mathbb{N} \to \mathbb{R}[q],\; \forall m \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{e}\left(x, m, d\right) = \operatorname{eval}\left(\operatorname{inputPrefix}\left(x, m\right), \operatorname{esymm}\left(\operatorname{Fin}\left(m\right), \mathbb{R}[q], d\right)\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/GyC51Settlement.e` (`✓ std3`).

*Citation.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

The sum is over subsets of size d of the first m input terms.

**Definition 1.5 (The complete homogeneous symmetric sum).**

$$\forall x \in \mathbb{N} \to \mathbb{R}[q],\; \forall m \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{h}\left(x, m, d\right) = \operatorname{eval}\left(\operatorname{inputPrefix}\left(x, m\right), \operatorname{hsymm}\left(\operatorname{Fin}\left(m\right), \mathbb{R}[q], d\right)\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/GyC51Settlement.h` (`✓ std3`).

*Citation.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

The sum is over multisets of size d of the first m input terms.

**Definition 1.6 (The elementary triple-product difference).**

$$\forall x \in \mathbb{N} \to \mathbb{R}[q],\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{E}\left(x, n, p, j\right) = \operatorname{e}\left(x, n, n - p\right) \cdot \operatorname{e}\left(x, p, p - j\right) \cdot \operatorname{e}\left(x, n - 1, n - j\right) - \operatorname{e}\left(x, n - 1, n - p\right) \cdot \operatorname{e}\left(x, p - 1, p - j\right) \cdot \operatorname{e}\left(x, n, n - j\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/GyC51Settlement.E` (`✓ std3`).

*Citation.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

Both products use elementary symmetric sums on the indicated prefixes.

**Definition 1.7 (The complete homogeneous triple-product difference).**

$$\forall x \in \mathbb{N} \to \mathbb{R}[q],\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{H}\left(x, n, p, j\right) = \operatorname{h}\left(x, p, n - p\right) \cdot \operatorname{h}\left(x, j, p - j\right) \cdot \operatorname{h}\left(x, j + 1, n - j\right) - \operatorname{h}\left(x, p + 1, n - p\right) \cdot \operatorname{h}\left(x, j + 1, p - j\right) \cdot \operatorname{h}\left(x, j, n - j\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/GyC51Settlement.H` (`✓ std3`).

*Citation.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

Both products use complete homogeneous symmetric sums on the indicated prefixes.

**Definition 1.8 (Log-concavity of the coefficients).**

$$\forall f \in \mathbb{R}[q],\; \operatorname{CoeffLogConcave}\left(f\right) \Leftrightarrow \left(\forall k \in \mathbb{N},\; 1 \le k \Rightarrow \left(k < \operatorname{natDegree}\left(f\right) \Rightarrow 0 \le \operatorname{coeff}\left(f, k\right)^{2} - \operatorname{coeff}\left(f, k + 1\right) \cdot \operatorname{coeff}\left(f, k - 1\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/GyC51Settlement.CoeffLogConcave` (`✓ std3`).

*Citation.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

Each determinant uses the coefficient at one interior index and the coefficients at its two neighbors.

**Definition 1.9 (Gy's affirmative assertion).**

$$claim \Leftrightarrow \left(\forall x \in \mathbb{N} \to \mathbb{R}[q],\; \operatorname{StronglyQLogConcave}\left(x\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall j \in \mathbb{N},\; 1 \le j \Rightarrow \left(j \le p \Rightarrow \left(p \le n \Rightarrow \left(\operatorname{CoeffLogConcave}\left(\operatorname{E}\left(x, n, p, j\right)\right) \land \operatorname{CoeffLogConcave}\left(\operatorname{H}\left(x, n, p, j\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/PolynomialValues/GyC51Settlement.claim` (`✓ std3`).

*Citation.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

Gy asks in Section 5, printed page 16, whether strong q-log-concavity of a sequence in R[q] forces log-concavity of the coefficients of both E and H at each allowed triple. Conjecture 5.1 on printed page 15 asks for coefficient nonnegativity of E and H.

**Theorem 1.10 (Both outputs can fail coefficient log-concavity).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PolynomialValues/GyC51Settlement.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* René Gy (2026). *On Certain Products of Three Stirling Numbers*. DOI: [10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106). URL: <https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16>.

*Commentary.*

Set gₜ = 1 + q + tq² and xₖ = (k + a)gₜ for every k ≥ 0. The strong q-log-concavity difference is (r − i)gₜ² for every i ≤ r, so the premise holds for t ≥ 0.

For n = j + 2 and p = j + 1, each output equals Cgₜ⁴, where C = j(j + 1)²(j + 2)(2a + j + 2)(4a + j + 3)/48 is positive for a > 0 and j ≥ 1. The first three coefficients are C, 4C and (6 + 4t)C. At t > 5/2, index one is interior and its determinant (10 − 4t)C² is negative.

The choice a = 1, t = 3 and j = 1 gives (n, p, j) = (3, 2, 1). Each output has first coefficients 10, 40 and 180 and determinant −200. Both polynomials have nonnegative coefficients.

## References

- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.CoeffLogConcave`
- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.E`
- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.H`
- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.StronglyQLogConcave`
- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.claim`
- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.e`
- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.h`
- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.inputPrefix`
- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.qLe`
- Truth anchor: `D5/S3/Arith/PolynomialValues/GyC51Settlement.result`
- Dependency: [D5/S0/Certificates/GiacomelliLogConcaveConeNonconvex](../../../S0/Certificates/GiacomelliLogConcaveConeNonconvex.md)
