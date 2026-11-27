# Dimitrov and Lazarova Part 4, Conjecture 1

## Abstract

The first conjecture in Dimitrov and Lazarova Part 4 holds throughout its full natural-number range.

**Definition 1.1 (The complete first conjecture).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{2 \cdot ((n: \mathbb{R}) + 1)^{3 \cdot k} + ((n: \mathbb{R}) - 1)^{3 \cdot k}}{((n: \mathbb{R}) + 1)^{2 \cdot k} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovPartIVC1.claim` (`✓ std3`).

*Citation.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

The statement is Conjecture 1 in Section 4, page 13 of the source. Nat.totient is Euler's totient, psi is the existing Dedekind psi function, and ArithmeticFunction.sigma 1 is the sum of positive divisors. The identity OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of p^(e−1)(p+1) over the exact prime-power factors of n. ArithmeticFunction.sigma_one_apply identifies the divisor sum. All powers are ordinary natural powers. Every quotient and the subtraction n−1 are real. Both natural-number quantifiers are unrestricted apart from n ≥ 2 and k ≥ 1.

**Theorem 1.2 (The full powered cubic quotient).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{2 \cdot ((n: \mathbb{R}) + 1)^{3 \cdot k} + ((n: \mathbb{R}) - 1)^{3 \cdot k}}{((n: \mathbb{R}) + 1)^{2 \cdot k} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovPartIVC1.result` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-lazarova-part4-conjecture-1` (proved) by `D5/S3/Arith/Divisors/DimitrovPartIVC1.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-lazarova-part4-conjecture-1","declaration_gid":"D5/S3/Arith/Divisors/DimitrovPartIVC1.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

Put a=φ(n), b=ψ(n), c=σ(n), u=n−1 and v=n+1. The imported arithmetic bounds give 0<a≤u and 0<v≤b≤c. For x=(b/a)^k, y=(c/a)^k and r=(v/u)^k, these bounds give 1≤r≤x≤y. The original cubic_ratio_bound in DimitrovPartFourC4 gives (1+2r³)/r²≤(1+x³+y³)/(xy). Clearing positive denominators identifies the left side here with the publisher's right side and the right side here with the publisher's left side. This proves the full power family of Conjecture 1. The source's Theorem 1 gives k=1.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartIVC1.claim`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartIVC1.result`
- Dependency: [D5/S3/Arith/Divisors/DimitrovPartFourC4](DimitrovPartFourC4.md)
