# Dimitrov and Lazarova Part 4, Conjecture 4

## Abstract

The fourth conjecture in Dimitrov and Lazarova Part 4 holds throughout its full natural-number range.

**Definition 1.1 (The complete fourth conjecture).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{2 \cdot ((n: \mathbb{R}))^{3 \cdot k} + ((n: \mathbb{R}) - 1)^{3 \cdot k}}{((n: \mathbb{R}))^{2 \cdot k} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovPartFourC4.claim` (`✓ std3`).

*Citation.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

The statement is Conjecture 4 in Section 4, page 13, MathML mm202–204 of the source (DOI 10.3390/math14213935, Mathematics 14(21), 3935; CC BY 4.0). Definitions are in Section 1, pages 1–2. Nat.totient is Euler's totient, psi is the existing Dedekind psi function, and ArithmeticFunction.sigma 1 is the sum of positive divisors. The identity OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of p^(e−1)(p+1) over the exact prime-power factors of n. ArithmeticFunction.sigma_one_apply identifies the divisor sum. Every pair sum is powered as a whole, and every quotient and n−1 in the displayed inequality are real. Both natural-number quantifiers are unrestricted apart from n ≥ 2 and k ≥ 1.

**Theorem 1.2 (The full powered mixed-product quotient).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{2 \cdot ((n: \mathbb{R}))^{3 \cdot k} + ((n: \mathbb{R}) - 1)^{3 \cdot k}}{((n: \mathbb{R}))^{2 \cdot k} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovPartFourC4.result` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-lazarova-part4-conjecture-4` (proved) by `D5/S3/Arith/Divisors/DimitrovPartFourC4.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-lazarova-part4-conjecture-4","declaration_gid":"D5/S3/Arith/Divisors/DimitrovPartFourC4.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

Put a=φ(n), b=ψ(n), c=σ(n), A=a(b+c), B=b(a+c), C=c(a+b) and r=n/(n−1). The imported arithmetic bounds and mixed_bound at m=1 give 0<A, r≤B/A≤C/A and 1≤r. For x=(B/A)^k, y=(C/A)^k and R=r^k, the consumed cubic_ratio_bound proves (1+x³+y³)/(xy)≥(1+2R³)/R². Its proof expands the cleared difference as R(R³−1)((x−R)+(y−R))+3R³((x−R)−(y−R))² +(4R³−1)(x−R)(y−R)+R²((x−R)³+(y−R)³), whose terms are nonnegative. Exact field normalization recovers every factor and ordinary power of the original quotient. This is the complete natural-number family; source Theorem 4 supplies only k=1. No analytic novelty, equality classification or worldwide priority is claimed. The imported arithmetic development retains its existing supplier attribution and license.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartFourC4.claim`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartFourC4.result`
- Dependency: [D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5](DimitrovLowerBoundsC4C5.md)
