# Dimitrov's full reciprocal-product lower bounds

## Abstract

Dimitrov's reciprocal-product Conjectures 4 and 5 hold for every n ≥ 2 and k ≥ 1.

**Definition 1.1 (Dimitrov Conjecture 4).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)\right) \cdot \left(\frac{1}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)} + \frac{1}{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)} + \frac{1}{((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)}\right) \ge \frac{5 \cdot (n: \mathbb{R}) \cdot ((n: \mathbb{R}) + 1)^{k - 1} \cdot ((n: \mathbb{R}) - 1)^{k} + 2 \cdot ((n: \mathbb{R}) - 1)^{2 \cdot k} + 2 \cdot ((n: \mathbb{R}))^{2} \cdot ((n: \mathbb{R}) + 1)^{2 \cdot k - 2}}{(n: \mathbb{R}) \cdot ((n: \mathbb{R}) + 1)^{k - 1} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.claim4` (`✓ std3`).

*Citation.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

The source is arXiv:2606.12484v1, §2, PDF page 4. The variables are integers n ≥ 2 and k ≥ 1. Nat.totient is Euler's φ, psi is the local Dedekind ψ definition, and ArithmeticFunction.sigma 1 is the positive-divisor sum. Every exponent k is a pointwise power of a function value, and all three displayed reciprocal denominators are retained.

**Definition 1.2 (Dimitrov Conjecture 5).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right) + ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right) + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k}\right)\right) \cdot \left(\frac{1}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right)} + \frac{1}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right)} + \frac{1}{((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k}\right)}\right) \ge \frac{10 \cdot ((n: \mathbb{R}) - 1)^{2 \cdot k} + 7 \cdot (((n: \mathbb{R}))^{2} - 1)^{k} + ((n: \mathbb{R}) + 1)^{2 \cdot k}}{((n: \mathbb{R}) - 1)^{2 \cdot k} + (((n: \mathbb{R}))^{2} - 1)^{k}}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.claim5` (`✓ std3`).

*Citation.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

The source's fifth conjecture uses the pointwise k-th powers in every mixed sum and denominator. Its quantifiers and native function meanings are unchanged from Conjecture 4.

**Theorem 1.3 (The complete Conjecture 4 inequality).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)\right) \cdot \left(\frac{1}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)} + \frac{1}{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)} + \frac{1}{((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)}\right) \ge \frac{5 \cdot (n: \mathbb{R}) \cdot ((n: \mathbb{R}) + 1)^{k - 1} \cdot ((n: \mathbb{R}) - 1)^{k} + 2 \cdot ((n: \mathbb{R}) - 1)^{2 \cdot k} + 2 \cdot ((n: \mathbb{R}))^{2} \cdot ((n: \mathbb{R}) + 1)^{2 \cdot k - 2}}{(n: \mathbb{R}) \cdot ((n: \mathbb{R}) + 1)^{k - 1} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result4` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-2606-12484-conjecture-4` (proved) by `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result4`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-2606-12484-conjecture-4","declaration_gid":"D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result4","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

The native ordering 0 < φ(n) ≤ n−1 < n+1 ≤ ψ(n) ≤ σ(n) and the ordered reciprocal-product ratio lemma give the exact ratio n(n+1)^(k−1)/(n−1)^k. Mixed-power ordering supplies the required lower ratio, and exact field normalization produces every source numerator and denominator term.

**Theorem 1.4 (The complete Conjecture 5 inequality).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right) + ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right) + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k}\right)\right) \cdot \left(\frac{1}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right)} + \frac{1}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}\right)} + \frac{1}{((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left(((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k}\right)}\right) \ge \frac{10 \cdot ((n: \mathbb{R}) - 1)^{2 \cdot k} + 7 \cdot (((n: \mathbb{R}))^{2} - 1)^{k} + ((n: \mathbb{R}) + 1)^{2 \cdot k}}{((n: \mathbb{R}) - 1)^{2 \cdot k} + (((n: \mathbb{R}))^{2} - 1)^{k}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result5` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-2606-12484-conjecture-5` (proved) by `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result5`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-2606-12484-conjecture-5","declaration_gid":"D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result5","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

Apply the same ordered bound to φ(n)^k, ψ(n)^k and σ(n)^k. With q=((n+1)/(n−1))^k, the bound becomes (q²+7q+10)/(q+1); clearing the positive denominator and using (n²−1)^k is exactly the displayed source right-hand side.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.claim4`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.claim5`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result4`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.result5`
- Dependency: [D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes](OeisA344695GcdSigmaPsiPrimes.md)
