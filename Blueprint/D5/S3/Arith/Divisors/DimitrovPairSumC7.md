# Dimitrov's seventh pair-sum inequality

## Abstract

The full powered pair-sum inequality for Euler totient, Dedekind psi and the divisor sum.

**Definition 1.1 (The complete original seventh conjecture).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} + \frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} + \frac{((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{4 \cdot ((n: \mathbb{R}))^{2 \cdot k} + ((n: \mathbb{R}) + 1)^{2 \cdot k} + ((n: \mathbb{R}))^{k} \cdot ((n: \mathbb{R}) + 1)^{k}}{2 \cdot \left(((n: \mathbb{R}))^{2 \cdot k} + ((n: \mathbb{R}))^{k} \cdot ((n: \mathbb{R}) + 1)^{k}\right)}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovPairSumC7.claim` (`✓ std3`).

*Citation.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

Conjecture 7 of arXiv:2606.12484v1 quantifies all natural n at least two and k at least one. Nat.totient is Euler's function, psi is the product of p^(e-1)(p+1) over exact prime powers, and ArithmeticFunction.sigma 1 is the positive-divisor sum. Each entire pair sum is raised to k, and every quotient is real.

**Theorem 1.2 (The full seventh inequality).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} + \frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} + \frac{((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R}))^{k} + ((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k}} \ge \frac{4 \cdot ((n: \mathbb{R}))^{2 \cdot k} + ((n: \mathbb{R}) + 1)^{2 \cdot k} + ((n: \mathbb{R}))^{k} \cdot ((n: \mathbb{R}) + 1)^{k}}{2 \cdot \left(((n: \mathbb{R}))^{2 \cdot k} + ((n: \mathbb{R}))^{k} \cdot ((n: \mathbb{R}) + 1)^{k}\right)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovPairSumC7.result` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-2606-12484-conjecture-7` (proved) by `D5/S3/Arith/Divisors/DimitrovPairSumC7.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-2606-12484-conjecture-7","declaration_gid":"D5/S3/Arith/Divisors/DimitrovPairSumC7.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

Let x=φ(n)+ψ(n), y=φ(n)+σ(n), z=ψ(n)+σ(n) and q=(n+1)/n. Totient positivity and DimitrovLowerBoundsC4C5.psi_ge and sigma_ge_psi give 0<x≤y. The first projection of DimitrovPsiSigmaSeparation.separation gives q≤z/y, hence qy≤z. Since q≥1, raising the inequalities to k gives 0<x^k≤y^k≤z^k and 1≤q^k≤z^k/y^k. The first projection of DimitrovNesbittOppositeGap.opposite_gap at X=x^k, Y=y^k, Z=z^k and s=q^k gives the lower bound q^k/2+2/(1+q^k). Exact field normalization gives the displayed right side. The Library note cites both suppliers and the attribution for the imported C4/C5 development. In the bounded source screen, Part III Theorem 5 treats k=1. Part IV and the public Lean donor at 95809b59deefd8dfad81e398250aedd7e1aea3b3 leave the full C7 assertion uncovered.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPairSumC7.claim`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovPairSumC7.result`
- Dependency: [D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5](DimitrovLowerBoundsC4C5.md)
- Dependency: [D5/S3/Arith/Divisors/DimitrovNesbittOppositeGap](DimitrovNesbittOppositeGap.md)
- Dependency: [D5/S3/Arith/Divisors/DimitrovPsiSigmaSeparation](DimitrovPsiSigmaSeparation.md)
