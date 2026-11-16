# Dimitrov and Lazarova Part 4, Conjecture 3

## Abstract

The third conjecture in Dimitrov and Lazarova Part 4 holds throughout its full natural-number range.

**Definition 1.1 (The complete third conjecture).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{2 \cdot ((n: \mathbb{R}))^{3 \cdot k} + ((n: \mathbb{R}) + 1)^{3 \cdot k}}{((n: \mathbb{R}))^{2 \cdot k} \cdot ((n: \mathbb{R}) + 1)^{k}}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovPartIVC3.claim` (`✓ std3`).

*Citation.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

The statement is Conjecture 3 in Section 4 of the source. Nat.totient is Euler's totient, psi is the existing Dedekind psi function, and ArithmeticFunction.sigma 1 is the sum of positive divisors. The identity OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of p^(e−1)(p+1) over the exact prime-power factors of n. ArithmeticFunction.sigma_one_apply identifies the divisor sum. Every pair sum is powered as a whole, and every quotient in the displayed inequality is real. Both natural-number quantifiers are unrestricted apart from n ≥ 2 and k ≥ 1.

**Theorem 1.2 (The full powered pair-sum inequality).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{2 \cdot ((n: \mathbb{R}))^{3 \cdot k} + ((n: \mathbb{R}) + 1)^{3 \cdot k}}{((n: \mathbb{R}))^{2 \cdot k} \cdot ((n: \mathbb{R}) + 1)^{k}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovPartIVC3.result` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-lazarova-part4-conjecture-3` (proved) by `D5/S3/Arith/Divisors/DimitrovPartIVC3.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-lazarova-part4-conjecture-3","declaration_gid":"D5/S3/Arith/Divisors/DimitrovPartIVC3.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

Put a=φ(n), b=ψ(n), c=σ(n) and q=(n+1)/n. The imported arithmetic bounds give 0<a≤n−1, n+1≤b≤c and q(a+b)≤2b. The pair-gap inequality gives q²(a+b)(a+c)≤(b+c)²; raising it to k yields the corresponding powered gap. For x=(a+b)^k, y=(a+c)^k, z=(b+c)^k and Q=q^k≥1, put u=√(xy). The inequalities x³+y³≥2u³ and z/u≥Q, followed by the monotonicity of t²+2/t for t≥1, imply (x³+y³+z³)/(xyz)≥Q²+2/Q. Exact field normalization identifies Q²+2/Q with the source right side. This proves the complete natural-number family, extending the source's Theorem 3 at k=1. No analytic priority or equality classification is asserted. The imported arithmetic development retains its existing supplier attribution and license.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartIVC3.claim`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartIVC3.result`
- Dependency: [D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5](DimitrovLowerBoundsC4C5.md)
