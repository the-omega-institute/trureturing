# Karp's general-shift Hurwitz conjecture fails

## Abstract

Positive shifts need not preserve rising-factorial Toeplitz Hurwitz stability.

Local names belong to D5.S3.Analytic.SeriesInequalities.KarpRisingFactorialHurwitzRefutation. The rising factorial is ascPochhammer. The function f is real-valued and only its indices zero through n enter Q. Subtraction between natural indices, including n−k, k−1, k−10 and 10−k, is truncated subtraction.

**Definition 1.1 (The rising-factorial Toeplitz polynomial).**

$$\forall (n: \mathbb{N}), (\forall (f: \mathbb{N}\to \mathbb{R}), (\forall (\alpha: \mathbb{R}), (\forall (\beta: \mathbb{R}), (\operatorname{KarpRisingFactorialHurwitzRefutation.Q}\left(n, f, \alpha, \beta\right) = \sum_{k\in \operatorname{Finset.range}\left(n + 1\right)} \operatorname{Polynomial.C}\left((f\left(k\right): \mathbb{C}) \cdot (f\left(n - k\right): \mathbb{C}) \cdot (\operatorname{Nat.choose}\left(n, k\right): \mathbb{C})\right) \cdot (\operatorname{Polynomial.comp}\left(\operatorname{ascPochhammer}\left(\mathbb{C}, k\right), \operatorname{Polynomial.X} + \operatorname{Polynomial.C}\left((\alpha: \mathbb{C})\right)\right) \cdot \operatorname{Polynomial.comp}\left(\operatorname{ascPochhammer}\left(\mathbb{C}, n - k\right), \operatorname{Polynomial.X} + \operatorname{Polynomial.C}\left((\beta: \mathbb{C})\right)\right) - \operatorname{Polynomial.comp}\left(\operatorname{ascPochhammer}\left(\mathbb{C}, k\right), \operatorname{Polynomial.X} + \operatorname{Polynomial.C}\left(((\alpha + \beta: \mathbb{R}): \mathbb{C})\right)\right) \cdot \operatorname{ascPochhammer}\left(\mathbb{C}, n - k\right))))))$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.Q` (`✓ std3`).

*Citation.* D. Karp (2012). *Positivity of Toeplitz determinants formed by rising factorial series and properties of related polynomials*. DOI: [10.48550/arXiv.1203.1482](https://doi.org/10.48550/arXiv.1203.1482). URL: <https://arxiv.org/abs/1203.1482v1>.

*Commentary.*

Equation (3), p. 2 defines the finite sum displayed above.

Real coefficients and shifts are embedded into the complex numbers by the displayed casts. Polynomial composition substitutes X plus the shift into each rising factorial. The term with index k has the factor f(k)f(n−k) times Nat.choose n k.

**Definition 1.2 (Conjecture 2 with its standing assumptions).**

$$\operatorname{KarpRisingFactorialHurwitzRefutation.claim} = (\forall (n: \mathbb{N}), (\forall (\alpha: \mathbb{R}), (\forall (\beta: \mathbb{R}), (\forall (f: \mathbb{N}\to \mathbb{R}), ((3 \le n) \Rightarrow ((0 < \alpha) \Rightarrow ((0 < \beta) \Rightarrow ((\forall (k: \mathbb{N}), ((k \le n) \Rightarrow (0 \le f\left(k\right)))) \Rightarrow ((\exists (k: \mathbb{N}), ((k \le n) \land (f\left(k\right) \ne 0))) \Rightarrow ((\forall (N: \mathbb{N}), ((0 < N) \Rightarrow ((N \le n) \Rightarrow ((f\left(N\right) = 0) \Rightarrow (\forall (k: \mathbb{N}), ((N \le k) \Rightarrow ((k \le n) \Rightarrow (f\left(k\right) = 0)))))))) \Rightarrow ((\forall (k: \mathbb{N}), ((1 \le k) \Rightarrow ((k < n) \Rightarrow (f\left(k - 1\right) \cdot f\left(k + 1\right) < f\left(k\right)^{2})))) \Rightarrow (\forall (z: \mathbb{C}), ((\operatorname{Polynomial.eval}\left(z, \operatorname{KarpRisingFactorialHurwitzRefutation.Q}\left(n, f, \alpha, \beta\right)\right) = 0) \Rightarrow (\operatorname{Complex.re}\left(z\right) < 0))))))))))))))$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.claim` (`✓ std3`).

*Citation.* D. Karp (2012). *Positivity of Toeplitz determinants formed by rising factorial series and properties of related polynomials*. DOI: [10.48550/arXiv.1203.1482](https://doi.org/10.48550/arXiv.1203.1482). URL: <https://arxiv.org/abs/1203.1482v1>.

*Commentary.*

Conjecture 2, p. 2: “If $f_{k}^{2}>f_{k - 1} f_{k + 1}$, k=1,2,…,n−1, n≥3, then $Q^{\alpha,\beta}_{n}(x)$ is Hurwitz stable.”

“Recall that a polynomial is called Hurwitz stable if all its zeros have negative real part.” The positive shifts are α and β. The input is nonnegative and nonzero, and the source's zero condition applies only at N>0: a zero there forces all subsequent entries through n to vanish. Strict log-concavity is imposed for 1≤k<n. No total-positivity or unit-shift hypothesis is added.

**Theorem 1.3 (Refutation of general-shift Hurwitz stability).**

$$\neg (\forall (n: \mathbb{N}), (\forall (\alpha: \mathbb{R}), (\forall (\beta: \mathbb{R}), (\forall (f: \mathbb{N}\to \mathbb{R}), ((3 \le n) \Rightarrow ((0 < \alpha) \Rightarrow ((0 < \beta) \Rightarrow ((\forall (k: \mathbb{N}), ((k \le n) \Rightarrow (0 \le f\left(k\right)))) \Rightarrow ((\exists (k: \mathbb{N}), ((k \le n) \land (f\left(k\right) \ne 0))) \Rightarrow ((\forall (N: \mathbb{N}), ((0 < N) \Rightarrow ((N \le n) \Rightarrow ((f\left(N\right) = 0) \Rightarrow (\forall (k: \mathbb{N}), ((N \le k) \Rightarrow ((k \le n) \Rightarrow (f\left(k\right) = 0)))))))) \Rightarrow ((\forall (k: \mathbb{N}), ((1 \le k) \Rightarrow ((k < n) \Rightarrow (f\left(k - 1\right) \cdot f\left(k + 1\right) < f\left(k\right)^{2})))) \Rightarrow (\forall (z: \mathbb{C}), ((\operatorname{Polynomial.eval}\left(z, \operatorname{KarpRisingFactorialHurwitzRefutation.Q}\left(n, f, \alpha, \beta\right)\right) = 0) \Rightarrow (\operatorname{Complex.re}\left(z\right) < 0))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. Karp (2012). *Positivity of Toeplitz determinants formed by rising factorial series and properties of related polynomials*. DOI: [10.48550/arXiv.1203.1482](https://doi.org/10.48550/arXiv.1203.1482). URL: <https://arxiv.org/abs/1203.1482v1>.

*Commentary.*

Take n=20, α=β=1/t and f(k)=t^((k−10)²+(10−k)²), where 0<t<1. Every input is strictly positive, and the adjacent exponent sum exceeds twice the central exponent by two. Thus the inputs are strictly log-concave.

Multiplying Q evaluated at z/t by t²⁰ gives a polynomial whose value and derivative depend continuously on t. At t=0 it is 184756 times ((z+1)²⁰−(z(z+2))¹⁰). At z=1/50+(3/4)I the real part of its derivative times the conjugate of its value is strictly negative, by exact rational arithmetic.

If every root of a complex polynomial has nonpositive real part, its logarithmic derivative has nonnegative real part at every point with positive real part. The root-sum identity proves this sign condition term by term. The strict negative sign persists for some positive t<1, giving a root with positive real part and contradicting the claim. This argument proves existence at n=20; it supplies no explicit finite shift threshold or theorem for every larger degree.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.Q`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.claim`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.result`
