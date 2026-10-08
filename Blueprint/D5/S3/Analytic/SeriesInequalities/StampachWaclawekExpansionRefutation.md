# Štampach–Waclawek Expansion Refutation

## Abstract

The Birman weight expansion conjecture fails at order two and p = 11/10.

**Definition 1.1 (The alternative parameter sequence).**

$$\forall \ell: \mathbb{N}, \forall p: \mathbb{R}, \forall n: \mathbb{Z}, \operatorname{gT}\left(\ell, p, n\right) = \begin{cases}(n: \mathbb{R})^{1 - \frac{1}{p}} \cdot \prod_{j\in \operatorname{Finset}.\operatorname{Icc}\left(1, \ell - 1\right)} ((n: \mathbb{R}) - (j: \mathbb{R}))&\text{if} 0 \le n\\0&\text{otherwise}\end{cases}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.gT` (`✓ std3`).

*Citation.* František Štampach; Jakub Waclawek (2026). *Optimal discrete p-Hardy–Rellich–Birman inequalities*. URL: <https://arxiv.org/abs/2605.25238v1>.

*Commentary.*

Equation (2.16), p. 9, defines gT by n^(1−1/p) times the product of n−j for j=1,…,ℓ−1 on non-negative integers, with zero extension on negative integers. The product is over Finset.Icc on natural indices; ℓ−1 there is natural subtraction. All explicitly displayed casts to ℝ are the Lean coercions. Real powers use Real.rpow.

**Definition 1.2 (The discrete gradient).**

$$\forall u: \mathbb{Z}\to \mathbb{R}, \forall n: \mathbb{Z}, \operatorname{grad}\left(u, n\right) = u\left(n\right) - u\left(n - 1\right)$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.grad` (`✓ std3`).

*Citation.* František Štampach; Jakub Waclawek (2026). *Optimal discrete p-Hardy–Rellich–Birman inequalities*. URL: <https://arxiv.org/abs/2605.25238v1>.

*Commentary.*

Equation (2.2), p. 3: “We introduce the discrete gradient and discrete divergence operators acting on C(ℤ) as” (∇u)ₙ := uₙ − uₙ₋₁ and (div u)ₙ := uₙ₊₁ − uₙ. Here the sequences take real values, a subdomain of the source's complex sequences.

**Definition 1.3 (The discrete divergence).**

$$\forall u: \mathbb{Z}\to \mathbb{R}, \forall n: \mathbb{Z}, \operatorname{dv}\left(u, n\right) = u\left(n + 1\right) - u\left(n\right)$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.dv` (`✓ std3`).

*Citation.* František Štampach; Jakub Waclawek (2026). *Optimal discrete p-Hardy–Rellich–Birman inequalities*. URL: <https://arxiv.org/abs/2605.25238v1>.

*Commentary.*

Equation (2.2), p. 3, defines the forward difference u(n+1)−u(n). The indices are integers, so the successor does not truncate.

**Definition 1.4 (The signed-power convention).**

$$\forall a: \mathbb{R}, \forall \nu: \mathbb{R}, \operatorname{spow}\left(a, \nu\right) = \begin{cases}0&\text{if} \nu = 0\\\nu \cdot \left|\nu\right|^{a - 1}&\text{otherwise}\end{cases}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.spow` (`✓ std3`).

*Citation.* František Štampach; Jakub Waclawek (2026). *Optimal discrete p-Hardy–Rellich–Birman inequalities*. URL: <https://arxiv.org/abs/2605.25238v1>.

*Commentary.*

After (2.3), p. 4: “where ν^{⟨a⟩}:=ν|ν|^{a−1} for any a>0 and ν∈ℂ, with the convention 0^{⟨a⟩}:=0.” The real restriction is represented by spow; its definition includes the zero branch for every real exponent.

**Definition 1.5 (The alternative weight).**

$$\forall \ell: \mathbb{N}, \forall p: \mathbb{R}, \forall n: \mathbb{Z}, \operatorname{rhoT}\left(\ell, p, n\right) = \frac{(-1)^{\ell} \cdot \operatorname{dv}^{[\ell]}\left((m: \mathbb{Z} \mapsto \operatorname{spow}\left(p - 1, \operatorname{grad}^{[\ell]}\left(\operatorname{gT}\left(\ell, p\right), m\right)\right)), n\right)}{\operatorname{gT}\left(\ell, p, n\right)^{p - 1}}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.rhoT` (`✓ std3`).

*Citation.* František Štampach; Jakub Waclawek (2026). *Optimal discrete p-Hardy–Rellich–Birman inequalities*. URL: <https://arxiv.org/abs/2605.25238v1>.

*Commentary.*

Equation (2.17), p. 9, divides −Δₚ^(ℓ)gT by gT^(p−1). Equation (2.3), p. 4, gives −Δₚ^(ℓ)u = (−1)^ℓ div^ℓ(∇^ℓu)^{⟨p−1⟩}. The bracketed exponent [ℓ] means Function.iterate, including zero iterations; it is not a scalar power. The displayed expression retains the sign factor, order of the iterates, signed power and denominator.

**Definition 1.6 (The non-negative expansion claim).**

$$claim \Leftrightarrow (\forall \ell: \mathbb{N}, (1 \le \ell) \Rightarrow (\forall p: \mathbb{R}, (1 < p) \Rightarrow (\exists c: \mathbb{N}\to \mathbb{R}, (\forall k: \mathbb{N}, 0 \le c\left(k\right)) \land (\forall n: \mathbb{N}, (\ell \le n) \Rightarrow (\operatorname{HasSum}\left((k: \mathbb{N} \mapsto \frac{c\left(k\right)}{(n: \mathbb{R})^{k}}), (n: \mathbb{R})^{(\ell: \mathbb{R}) \cdot p} \cdot \operatorname{rhoT}\left(\ell, p, (n: \mathbb{Z})\right)\right))))))$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.claim` (`✓ std3`).

*Citation.* František Štampach; Jakub Waclawek (2026). *Optimal discrete p-Hardy–Rellich–Birman inequalities*. URL: <https://arxiv.org/abs/2605.25238v1>.

*Commentary.*

Conjecture 5.6, p. 28: “Let $\ell \in \mathbb{N}$ and $p> 1$, and let $\widetilde{\rho}^{(\ell,p)}$ be defined by (2.17) and (2.16).”

Part (iii), verbatim: “For all $n\ge \ell$, the terms $\left(\widetilde{\rho}^{(\ell,p)}\right)_{n}$ admit a power series expansion in negative powers of $n$ with entirely non-negative coefficients; cf. (2.15).”

The source's ℕ denotes positive integers; Lean uses ℓ : ℕ with 1 ≤ ℓ. HasSum expresses convergence of one coefficient sequence at every n ≥ ℓ. The constant coefficient is allowed to be any non-negative number. The source's (2.15) form implies this claim: take c₀=((1/q) rising-factorial ℓ)^p and cₖ=c₀Aₖ for k≥1. The rising factorial is positive for ℓ≥1 and p>1. Negating this weaker claim therefore refutes (iii) as stated.

**Theorem 1.7 (The expansion conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/stampach-waclawek-2026-birman-weight-expansion` (refuted) by `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"stampach-waclawek-2026-birman-weight-expansion","declaration_gid":"D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* František Štampach; Jakub Waclawek (2026). *Optimal discrete p-Hardy–Rellich–Birman inequalities*. URL: <https://arxiv.org/abs/2605.25238v1>.

*Commentary.*

Take ℓ=2 and p=11/10. Rational enclosures of n^(2p)rhoT(2,p,n) at n=100,200,400 give 200G(100)−600G(200)+400G(400) ≤ −32183/312500000 < 0. Here G(n) denotes that normalized weight. This is the difference between the upper and lower adjacent secant slopes at x=1/n. Non-negative power-series coefficients force the opposite inequality. The proof excludes an expansion directly; it does not identify individual asymptotic coefficients. Only part (iii) is refuted. Parts (i) and (ii), and the source's original-weight conjecture in Remark 2.12, are separate questions.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.claim`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.dv`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.gT`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.grad`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.result`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.rhoT`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.spow`
