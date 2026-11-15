# Dimitrov's complete Conjecture 8

## Abstract

The mixed-power Nesbitt lower bound holds for every n ≥ 2 and k ≥ 1.

**Definition 1.1 (Dimitrov Conjecture 8).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)}{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)} + \frac{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)} + \frac{((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)} \ge \frac{(n: \mathbb{R}) \cdot ((n: \mathbb{R}) + 1)^{k - 1} \cdot ((n: \mathbb{R}) - 1)^{k} + ((n: \mathbb{R}) - 1)^{2 \cdot k} + 4 \cdot ((n: \mathbb{R}))^{2} \cdot ((n: \mathbb{R}) + 1)^{2 \cdot k - 2}}{2 \cdot ((n: \mathbb{R}))^{2} \cdot ((n: \mathbb{R}) + 1)^{2 \cdot k - 2} + 2 \cdot (n: \mathbb{R}) \cdot ((n: \mathbb{R}) + 1)^{k - 1} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Formalization.* `D5/S3/Arith/Divisors/DimitrovNesbittC8.claim` (`✓ std3`).

*Citation.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

The source states: For every integers k ≥ 1 and n ≥ 2, we have the displayed inequality. Nat.totient is Euler's totient, psi is Dedekind's function from OeisA344695GcdSigmaPsiPrimes, and ArithmeticFunction.sigma 1 is the sum of positive divisors. Function values are raised to pointwise powers; the inner sums in all three mixed terms remain unpowered. The natural exponent 2k−2 agrees with the source because k ≥ 1.

**Theorem 1.2 (The full Conjecture 8 inequality).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\frac{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)}{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)} + \frac{((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)} + \frac{((\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{psi}\left(n\right): \mathbb{R})\right)}{((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{psi}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right) + ((\operatorname{psi}\left(n\right): \mathbb{R}))^{k} \cdot \left((\operatorname{Nat}.\operatorname{totient}\left(n\right): \mathbb{R}) + (\operatorname{ArithmeticFunction}.\operatorname{sigma}\left(1, n\right): \mathbb{R})\right)} \ge \frac{(n: \mathbb{R}) \cdot ((n: \mathbb{R}) + 1)^{k - 1} \cdot ((n: \mathbb{R}) - 1)^{k} + ((n: \mathbb{R}) - 1)^{2 \cdot k} + 4 \cdot ((n: \mathbb{R}))^{2} \cdot ((n: \mathbb{R}) + 1)^{2 \cdot k - 2}}{2 \cdot ((n: \mathbb{R}))^{2} \cdot ((n: \mathbb{R}) + 1)^{2 \cdot k - 2} + 2 \cdot (n: \mathbb{R}) \cdot ((n: \mathbb{R}) + 1)^{k - 1} \cdot ((n: \mathbb{R}) - 1)^{k}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/DimitrovNesbittC8.result` (`✓ std3`). ∎

*Resolves.* `Problems/dimitrov-2606-12484-conjecture-8` (proved) by `D5/S3/Arith/Divisors/DimitrovNesbittC8.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dimitrov-2606-12484-conjecture-8","declaration_gid":"D5/S3/Arith/Divisors/DimitrovNesbittC8.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. I. Dimitrov (2026). *Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*. URL: <https://arxiv.org/abs/2606.12484v1>.

*Commentary.*

The original arithmetic bounds and mixed_bound in DimitrovLowerBoundsC4C5 give 0 < A ≤ B ≤ C and 1 ≤ R ≤ B/A ≤ C/A, where R=n(n+1)^(k−1)/(n−1)^k. The ratio-constrained Nesbitt inequality at x=B/A, y=C/A and r=R yields (4R²+R+1)/(2(R²+R)). Exact field normalization gives the displayed source bound. The analytic step is a modified Apache-2.0 source port: balanced_pair_fraction_le and nesbitt_envelope_mono are consumed by normalized_nesbitt_ratio_inequality from pro20541/dimitrov-conjectures-lean at 95809b59deefd8dfad81e398250aedd7e1aea3b3, FrontierMathLean/NesbittRatioInequality.lean. Michael Mazur is the upstream author/maintainer, with substantive OpenAI Codex generation disclosed under his direction. Namespace and private visibility are adapted; the source note supplies the immutable URL, hash, license and receiver-pin retirement condition. This application includes k=1 and every composite or prime n ≥ 2.

## References

- Truth anchor: `D5/S3/Arith/Divisors/DimitrovNesbittC8.claim`
- Truth anchor: `D5/S3/Arith/Divisors/DimitrovNesbittC8.result`
- Dependency: [D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5](DimitrovLowerBoundsC4C5.md)
