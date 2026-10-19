# A counterexample to the general Potts moment lower bound

## Abstract

A mixture of two uniform densities has a unique positive Potts criticality zero below the proposed general moment lower bound.

All integrals are Lebesgue integrals on the real line. The parameter q is real, and the proposed inequality concerns q > 2. The functions F0 and K are the size-biased order parameter and criticality function of Section 1, equations (1) and (6), in Janssen's analysis of the annealed Potts model. The claim below is the general moment lower inequality in equation (84), with the standing curvature assumption and unique-positive-zero condition explicit.

**Definition 1.1 (Moments of a density).**

$$\forall (f: \mathbb{R} \to \mathbb{R}), (\forall (n: \mathbb{N}), (\operatorname{moment}\left(f, n\right) = \int_{\mathbb{R}} ((w)^{n} \cdot f\left(w\right)) \mathrm{d}w))$$

*Formalization.* `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are the standard moments μₙ of a real-valued density f, with n a natural number. The definition uses the Lebesgue integral on the whole real line; for densities supported on positive weights it agrees with the integral over positive weights. The definition is total, and the proposed inequality supplies integrability conditions.

**Definition 1.2 (The size-biased order parameter).**

$$\forall (f: \mathbb{R} \to \mathbb{R}), (\forall (q: \mathbb{R}), (\forall (t: \mathbb{R}), (\left(\mathcal{F}_{0}\right)\left(f, q, t\right) = \frac{\int_{\mathbb{R}} (w \cdot \frac{\exp\left(t \cdot w\right) - 1}{\exp\left(t \cdot w\right) + q - 1} \cdot f\left(w\right)) \mathrm{d}w}{\operatorname{moment}\left(f, 1\right)})))$$

*Formalization.* `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.F0` (`✓ std3`).

*Citation.* A. J. E. M. Janssen (2025). *Analysis of quantities determining the critical inverse temperature in the annealed Potts model with Pareto vertex weights*. URL: <https://arxiv.org/abs/2508.21409v3>.

*Commentary.*

Equation (1) defines 𝓕₀ by the size-biased expectation, normalized by the first moment. The definition takes arbitrary real q and t; the proposed inequality uses q > 2 and positive zeros t.

**Definition 1.3 (The criticality function).**

$$\forall (f: \mathbb{R} \to \mathbb{R}), (\forall (q: \mathbb{R}), (\forall (t: \mathbb{R}), (\mathcal{K}\left(f, q, t\right) = \frac{\int_{\mathbb{R}} (\log\left(\frac{\exp\left(t \cdot w\right) + q - 1}{q}\right) \cdot f\left(w\right)) \mathrm{d}w}{\operatorname{moment}\left(f, 1\right)} - \frac{q - 1}{2 \cdot q} \cdot t \cdot \left(\mathcal{F}_{0}\right)\left(f, q, t\right) - \frac{t}{q})))$$

*Formalization.* `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.K` (`✓ std3`).

*Citation.* A. J. E. M. Janssen (2025). *Analysis of quantities determining the critical inverse temperature in the annealed Potts model with Pareto vertex weights*. URL: <https://arxiv.org/abs/2508.21409v3>.

*Commentary.*

Equation (6) defines 𝒦 as the logarithmic expectation divided by the first moment, minus the two displayed correction terms, after eliminating the stationarity parameter.

**Definition 1.4 (The proposed universal lower inequality).**

$$\operatorname{claim} \Leftrightarrow (\forall (q: \mathbb{R}), ((2 < q) \Rightarrow (\forall (f: \mathbb{R} \to \mathbb{R}), ((\operatorname{Integrable}\left(f\right)) \Rightarrow ((\forall (w: \mathbb{R}), (0 \le f\left(w\right))) \Rightarrow ((\forall (w: \mathbb{R}), ((w \le 0) \Rightarrow (f\left(w\right) = 0))) \Rightarrow ((\int_{\mathbb{R}} (f\left(w\right)) \mathrm{d}w = 1) \Rightarrow ((\operatorname{Integrable}\left(\lambda (w: \mathbb{R}) \mapsto ((w)^{4} \cdot f\left(w\right))\right)) \Rightarrow ((\exists (s: \mathbb{R}), ((0 < s) \land ((\forall (t: \mathbb{R}), ((0 < t) \Rightarrow ((t < s) \Rightarrow (0 < \operatorname{iteratedDeriv}\left(2, \left(\mathcal{F}_{0}\right)\left(f, q\right), t\right))))) \land (\forall (t: \mathbb{R}), ((s < t) \Rightarrow (\operatorname{iteratedDeriv}\left(2, \left(\mathcal{F}_{0}\right)\left(f, q\right), t\right) < 0)))))) \Rightarrow ((\exists (u: \mathbb{R}), (((0 < u) \land (\mathcal{K}\left(f, q, u\right) = 0)) \land (\forall (s: \mathbb{R}), (((0 < s) \land (\mathcal{K}\left(f, q, s\right) = 0)) \Rightarrow (s = u))))) \Rightarrow (\forall (t: \mathbb{R}), ((0 < t) \Rightarrow ((\mathcal{K}\left(f, q, t\right) = 0) \Rightarrow (2 \cdot \frac{\operatorname{moment}\left(f, 3\right)}{\operatorname{moment}\left(f, 4\right)} \cdot \log\left(q - 1\right) < t))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.claim` (`✓ std3`).

*Citation.* A. J. E. M. Janssen (2025). *Analysis of quantities determining the critical inverse temperature in the annealed Potts model with Pareto vertex weights*. URL: <https://arxiv.org/abs/2508.21409v3>.

*Commentary.*

The lower inequality proposed in equation (84) asserts 2(μ₃/μ₄) ln(q − 1) < t at every positive zero t of 𝒦, for every real q > 2. The hypotheses require an integrable nonnegative density, zero for w ≤ 0, of total mass one, and with integrable fourth-moment integrand. The standing assumption requires a positive s such that 𝓕₀''(t) > 0 for 0 < t < s and 𝓕₀''(t) < 0 for t > s. They also require exactly one positive zero of 𝒦. The existential clause below includes the universal equality condition expressing uniqueness.

**Definition 1.5 (Two narrow uniform blocks).**

$$\forall (w: \mathbb{R}), (\operatorname{density}\left(w\right) = \frac{1331}{1340} \cdot (500 \cdot \left(\mathbf{1}_{[\frac{999}{1000}, \frac{1001}{1000}]}\right)\left(w\right)) + \frac{9}{1340} \cdot (500 \cdot \left(\mathbf{1}_{[\frac{10999}{1000}, \frac{11001}{1000}]}\right)\left(w\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.density` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. J. E. M. Janssen (2025). *Analysis of quantities determining the critical inverse temperature in the annealed Potts model with Pareto vertex weights*. URL: <https://arxiv.org/abs/2508.21409v3>.

*Commentary.*

Each indicator is one on the displayed closed interval and zero elsewhere. Multiplication by 500 makes each block have mass one. The mixture weights are 1331/1340 and 9/1340, and the block centers are 1 and 11. This density is nonnegative, has mass one, vanishes on nonpositive weights, and has finite moments of every natural order.

**Theorem 1.6 (The universal inequality fails).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/janssen-2025-annealed-potts-moment-lower-bound-refutation` (refuted) by `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"janssen-2025-annealed-potts-moment-lower-bound-refutation","declaration_gid":"D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. J. E. M. Janssen (2025). *Analysis of quantities determining the critical inverse temperature in the annealed Potts model with Pareto vertex weights*. URL: <https://arxiv.org/abs/2508.21409v3>.

*Commentary.*

Take q = 3 and the displayed two-block density f. Its first, third, and fourth moments are μ₁ = 143/134, μ₃ = 1331000143/134000000, and μ₄ = 33275001210000067/335000000000000. Set T = 6931/50000 = 0.13862. These exact moments and a lower bound for ln 2 give T < 2(μ₃/μ₄) ln 2.

The second derivative of x ↦ (eˣ − 1)/(eˣ + 2) is 3eˣ(2 − eˣ)/(eˣ + 2)³, positive for x < ln 2 and negative for x > ln 2. The second derivative 𝓕₀''(t) is its expectation at tW, weighted by W³/μ₁. This weighted expectation strictly decreases on [0, 9/50] and is positive at zero. On [9/50, 7/10], certified rational exponential enclosures on 26 subintervals make it negative; for t ≥ 7/10 both density intervals have tW > ln 2. Continuity therefore gives a positive s with 𝓕₀'' positive on (0, s) and negative on (s, ∞), as the standing assumption requires.

Differentiating the criticality function gives 𝒦'(t) = ((q − 1)/(2q))(𝓕₀(t) − t𝓕₀'(t)); at q = 3 this yields 𝒦''(t) = −t𝓕₀''(t)/3. Since 𝒦(0) = 𝒦'(0) = 0 and 𝓕₀'' has exactly one positive zero, Rolle's theorem gives at most one positive zero of 𝒦. Near zero 𝒦 is negative. Rational exponential and logarithm bounds, with a symmetric integral error estimate for the two density intervals, give 𝒦(T) > 0. The intermediate value theorem supplies a positive zero at or below T, so the zero is unique and lies strictly below 2(μ₃/μ₄) ln 2. All the hypotheses hold while the proposed strict lower inequality fails.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.F0`
- Truth anchor: `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.K`
- Truth anchor: `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.density`
- Truth anchor: `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.moment`
- Truth anchor: `D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.result`
- Dependency: [D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay](../FluidDynamics/Fourier/PeriodicAllenCahnDecay.md)
