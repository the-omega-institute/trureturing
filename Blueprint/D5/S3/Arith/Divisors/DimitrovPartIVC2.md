# Dimitrov and Lazarova Part 4, Conjecture 2

## Abstract

The second conjecture in Dimitrov and Lazarova Part 4 holds throughout its full natural-number range.

**Definition 1.1 (The complete second conjecture).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{2 \cdot k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{2 \cdot k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{2 \cdot k}} \ge \frac{2 \cdot (((n: \mathbb{R}))^{2} - 1)^{3 \cdot k} + ((n: \mathbb{R}) + 1)^{6 \cdot k}}{((n: \mathbb{R}) - 1)^{2 \cdot k} \cdot ((n: \mathbb{R}) + 1)^{4 \cdot k}}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovPartIVC2.claim` (`✓ std3`).

*Citation.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

The statement is Conjecture 2 in Section 4 of the source. Nat.totient is Euler's totient, psi is the existing Dedekind psi function, and ArithmeticFunction.sigma 1 is the sum of positive divisors. The identity OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of p^(e−1)(p+1) over the exact prime-power factors of n. ArithmeticFunction.sigma_one_apply identifies the divisor sum. Every exponent is applied to a function value, and every quotient and subtraction in the displayed inequality is real. Both natural-number quantifiers are unrestricted apart from n ≥ 2 and k ≥ 1.

**Theorem 1.2 (The full power-family inequality).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{2 \cdot k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{2 \cdot k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{2 \cdot k}} \ge \frac{2 \cdot (((n: \mathbb{R}))^{2} - 1)^{3 \cdot k} + ((n: \mathbb{R}) + 1)^{6 \cdot k}}{((n: \mathbb{R}) - 1)^{2 \cdot k} \cdot ((n: \mathbb{R}) + 1)^{4 \cdot k}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovPartIVC2.result` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-lazarova-part4-conjecture-2` (proved) by `D5/S3/Arith/Divisors/DimitrovPartIVC2.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-lazarova-part4-conjecture-2","declaration_gid":"D5/S3/Arith/Divisors/DimitrovPartIVC2.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

Put A=φ(n)^k, B=ψ(n)^k, C=σ(n)^k, U=(n−1)^k and V=(n+1)^k. The existing bounds psi_ge and sigma_ge_psi, together with positivity and the totient upper bound, give 1 ≤ V/U ≤ B/A ≤ C/A. For real 1 ≤ r ≤ x ≤ y, put F=xy+x/y²+y/x². The identity F−(x²+2/x)=(y−x)((x³−1)y²+(y−x)(2y+x))/(x²y²) is nonnegative. Also x²+2/x−(r²+2/r)=(x−r)((x+r)xr−2)/(xr) is nonnegative. Apply these identities at r=V/U, x=B/A and y=C/A. Exact field normalization converts the left side to F and the right side to r²+2/r, including all three pairwise numerator terms and the denominator exponents 2k and 4k. This covers every prime and composite n and every allowed k. The argument uses no new arithmetic-function definition and claims no priority for the analytic inequality. The imported arithmetic development retains its existing supplier attribution and license.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartIVC2.claim`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartIVC2.result`
- Dependency: [D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5](DimitrovLowerBoundsC4C5.md)
