# Dimitrov's full Conjecture 6

## Abstract

Dimitrov's Conjecture 6 holds for every n ≥ 2 and k ≥ 1, with pointwise function-value powers.

**Definition 1.1 (The complete original sixth conjecture).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k}}{((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k}\right)} + \frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}}{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right)} + \frac{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right)} \ge \frac{4 \cdot ((n: \mathbb{R}) - 1)^{2 \cdot k} + (((n: \mathbb{R}))^{2} - 1)^{k} + ((n: \mathbb{R}) + 1)^{2 \cdot k}}{2 \cdot \left(((n: \mathbb{R}) - 1)^{2 \cdot k} + (((n: \mathbb{R}))^{2} - 1)^{k}\right)}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovLowerBoundC6.claim` (`✓ std3`).

*Citation.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

The source is arXiv:2606.12484v1, Conjecture 6. Nat.totient is Euler's totient, psi is Dedekind's function and ArithmeticFunction.sigma 1 is the positive-divisor sum. All powers are powers of function values, all arithmetic in the inequality is real, and the natural-number ranges n ≥ 2 and k ≥ 1 are unrestricted.

**Theorem 1.2 (The full sixth conjecture inequality).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k}}{((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k}\right)} + \frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}}{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right)} + \frac{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right)} \ge \frac{4 \cdot ((n: \mathbb{R}) - 1)^{2 \cdot k} + (((n: \mathbb{R}))^{2} - 1)^{k} + ((n: \mathbb{R}) + 1)^{2 \cdot k}}{2 \cdot \left(((n: \mathbb{R}) - 1)^{2 \cdot k} + (((n: \mathbb{R}))^{2} - 1)^{k}\right)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovLowerBoundC6.result` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-2606-12484-conjecture-6` (proved) by `D5/S3/Arith/Divisors/DimitrovLowerBoundC6.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-2606-12484-conjecture-6","declaration_gid":"D5/S3/Arith/Divisors/DimitrovLowerBoundC6.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

Put a=φ(n)^k, b=ψ(n)^k and c=σ(n)^k, and write F for the three-term expression in the statement. For A=a(b+c), B=b(a+c) and C=c(a+b), exact field normalization gives (A+B+C)(1/A+1/B+1/C)=6+2F. The Conjecture 5 numerator is six times its denominator plus the Conjecture 6 numerator, while the Conjecture 6 denominator is twice the Conjecture 5 denominator. Applying DimitrovLowerBoundsC4C5.result5 and canceling this positive affine transformation proves the displayed bound. The nonzero denominator facts follow from n ≥ 2 and positivity of the three arithmetic functions. No new analytic inequality or additional hypothesis is needed. The imported fifth-conjecture proof retains its existing Apache-2.0 supplier attribution and license.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovLowerBoundC6.claim`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovLowerBoundC6.result`
- Dependency: [D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5](DimitrovLowerBoundsC4C5.md)
