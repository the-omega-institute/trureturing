# Dimitrov–Lazarova Part 4 Conjecture 1

## Abstract

The complete positive-power quotient in Dimitrov–Lazarova Part 4 Conjecture 1.

**Definition 1.1 (The complete first conjecture).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{2 \cdot ((n: \mathbb{R}) + 1)^{3 \cdot k} + ((n: \mathbb{R}) - 1)^{3 \cdot k}}{((n: \mathbb{R}) + 1)^{2 \cdot k} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovPartFourC1.claim` (`✓ std3`).

*Citation.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

Dimitrov and Lazarova state Conjecture 1 in Section 4, page 13 of Mathematics 14(21), 3935 (DOI 10.3390/math14213935, CC BY 4.0). Nat.totient is Euler's totient. OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of p^(e−1)(p+1) over the exact prime powers in n. ArithmeticFunction.sigma_one_apply identifies ArithmeticFunction.sigma 1 with the sum of positive divisors. All quotients and n−1 are real, and all powers are ordinary powers of function values. The natural-number ranges n ≥ 2 and k ≥ 1 are complete.

**Theorem 1.2 (The full positive-power cubic quotient).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{3 \cdot k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{3 \cdot k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{2 \cdot ((n: \mathbb{R}) + 1)^{3 \cdot k} + ((n: \mathbb{R}) - 1)^{3 \cdot k}}{((n: \mathbb{R}) + 1)^{2 \cdot k} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovPartFourC1.result` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-lazarova-part4-conjecture-1` (proved) by `D5/S3/Arith/Divisors/DimitrovPartFourC1.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-lazarova-part4-conjecture-1","declaration_gid":"D5/S3/Arith/Divisors/DimitrovPartFourC1.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stoyan Dimitrov and Meglena Lazarova (2026). *Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4*. DOI: [10.3390/math14213935](https://doi.org/10.3390/math14213935). URL: <https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf>.

*Commentary.*

Set A=φ(n)^k, B=ψ(n)^k, C=σ(n)^k, U=(n−1)^k and V=(n+1)^k. Positivity, Nat.totient_lt, psi_ge and sigma_ge_psi give 0<A≤U≤V≤B≤C. Apply DimitrovPartFourC4.cubic_ratio_bound at r=V/U, x=B/A and y=C/A, where x,y≥r≥1. The supplier proves the cleared cubic difference is nonnegative by expanding it as r(r³−1)((x−r)+(y−r))+3r³((x−r)−(y−r))² +(4r³−1)(x−r)(y−r)+r²((x−r)³+(y−r)³). Exact field normalization recovers the displayed source quotients. At k=1 the result recovers source Theorem 1. The last term in the expansion forces x=y=r at equality. In the arithmetic application this forces A=U and hence n prime. Conversely every prime has A=U and B=C=V and attains the bound for every allowed k. The original cubic lemma is owned by the Part IV C4 module, where it was private. The imported C4/C5 arithmetic bounds retain their existing supplier attribution and license.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartFourC1.claim`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPartFourC1.result`
- Dependency: [D5/S3/Arith/Divisors/DimitrovPartFourC4](DimitrovPartFourC4.md)
