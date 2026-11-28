# Farih’s exact fourth-moment maximum

## Abstract

At one prescribed moment vector, a feasible three-moment law has mean efficiency 37/60, above the attained four-moment maximum 11/18. No two-point law satisfies all four moments.

**Definition 1.1 (Raw moment).**

$$\operatorname{rawMoment}(\mu,k)=\int_{\mathbb{R}} x^{k}\,\mathrm{d}\mu(x)$$

*Formalization.* `D5/S3/Analytic/Stieltjes/FarihFourthMoment.rawMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Badr Farih (2026). *Sharp Bounds on the Mean Efficiency of a Fluctuating Machine*. DOI: [10.48550/arXiv.2609.15443](https://doi.org/10.48550/arXiv.2609.15443). URL: <https://arxiv.org/abs/2609.15443v3>.

*Commentary.*

The variable μ ranges over Borel measures on the real line and k over natural numbers. The integral is the real Bochner integral.

**Definition 1.2 (Prescribed integrable moment).**

$$\operatorname{HasRawMoment}(\mu,k,m)\iff \operatorname{Integrable}(x\mapsto x^{k},\mu) \land \operatorname{rawMoment}(\mu,k)=m$$

*Formalization.* `D5/S3/Analytic/Stieltjes/FarihFourthMoment.HasRawMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Badr Farih (2026). *Sharp Bounds on the Mean Efficiency of a Fluctuating Machine*. DOI: [10.48550/arXiv.2609.15443](https://doi.org/10.48550/arXiv.2609.15443). URL: <https://arxiv.org/abs/2609.15443v3>.

*Commentary.*

The function x ↦ xᵏ must be integrable against μ, and its raw moment must equal the real number m. The integrability hypothesis gives the moment its usual interpretation throughout the proof.

**Definition 1.3 (First-three-moment class).**

$$M_{3}(\mu)\iff \operatorname{IsProbabilityMeasure}(\mu) \land \forall^{\mathrm{ae}}_{x\sim\mu} (0\le x) \land \operatorname{HasRawMoment}(\mu,1,1) \land \operatorname{HasRawMoment}(\mu,2,\frac{5}{3}) \land \operatorname{HasRawMoment}(\mu,3,3)$$

*Formalization.* `D5/S3/Analytic/Stieltjes/FarihFourthMoment.FirstThreeMoments` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Badr Farih (2026). *Sharp Bounds on the Mean Efficiency of a Fluctuating Machine*. DOI: [10.48550/arXiv.2609.15443](https://doi.org/10.48550/arXiv.2609.15443). URL: <https://arxiv.org/abs/2609.15443v3>.

*Commentary.*

Here M₃(μ) denotes FirstThreeMoments μ. The structure requires probability, nonnegative x almost everywhere with respect to μ, and integrable raw moments 1, 5/3 and 3 in orders one, two and three.

**Definition 1.4 (First-four-moment class).**

$$M_{4}(\mu)\iff M_{3}(\mu) \land \operatorname{HasRawMoment}(\mu,4,\frac{17}{3})$$

*Formalization.* `D5/S3/Analytic/Stieltjes/FarihFourthMoment.FirstFourMoments` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Badr Farih (2026). *Sharp Bounds on the Mean Efficiency of a Fluctuating Machine*. DOI: [10.48550/arXiv.2609.15443](https://doi.org/10.48550/arXiv.2609.15443). URL: <https://arxiv.org/abs/2609.15443v3>.

*Commentary.*

Here M₄(μ) denotes FirstFourMoments μ. It retains all five fields of FirstThreeMoments and prescribes the integrable fourth raw moment 17/3.

**Definition 1.5 (Efficiency at α = 1).**

$$\operatorname{efficiency}(x)=\frac{1}{1+x}$$

*Formalization.* `D5/S3/Analytic/Stieltjes/FarihFourthMoment.efficiency` (`✓ std3`).

*Citation.* Badr Farih (2026). *Sharp Bounds on the Mean Efficiency of a Fluctuating Machine*. DOI: [10.48550/arXiv.2609.15443](https://doi.org/10.48550/arXiv.2609.15443). URL: <https://arxiv.org/abs/2609.15443v3>.

*Commentary.*

The real function uses the inverse of 1+x. Farih’s law is supported almost everywhere on x ≥ 0, where the denominator is positive.

**Definition 1.6 (Mean efficiency).**

$$\operatorname{meanEfficiency}(\mu)=\int_{\mathbb{R}} \operatorname{efficiency}(x)\,\mathrm{d}\mu(x)$$

*Formalization.* `D5/S3/Analytic/Stieltjes/FarihFourthMoment.meanEfficiency` (`✓ std3`).

*Citation.* Badr Farih (2026). *Sharp Bounds on the Mean Efficiency of a Fluctuating Machine*. DOI: [10.48550/arXiv.2609.15443](https://doi.org/10.48550/arXiv.2609.15443). URL: <https://arxiv.org/abs/2609.15443v3>.

*Commentary.*

Mean efficiency is the Bochner integral against μ. The proof establishes integrability on every feasible law using the bound by one on the nonnegative half-line.

**Definition 1.7 (The attaining four-moment law).**

$$\mu_{4}=\frac{1}{3}\delta_{0}+\frac{1}{3}\delta_{1}+\frac{1}{3}\delta_{2}$$

*Formalization.* `D5/S3/Analytic/Stieltjes/FarihFourthMoment.uniform012` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Badr Farih (2026). *Sharp Bounds on the Mean Efficiency of a Fluctuating Machine*. DOI: [10.48550/arXiv.2609.15443](https://doi.org/10.48550/arXiv.2609.15443). URL: <https://arxiv.org/abs/2609.15443v3>.

*Commentary.*

μ₄ is uniform012. Each δ denotes a Dirac measure at its subscript. The nonnegative weights act as scalars in the extended nonnegative reals.

**Definition 1.8 (The first-three-moment witness).**

$$\mu_{3}=\frac{10}{27}\delta_{0}+\frac{16}{27}\delta_{\frac{3}{2}}+\frac{1}{27}\delta_{3}$$

*Formalization.* `D5/S3/Analytic/Stieltjes/FarihFourthMoment.threeMomentWitness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Badr Farih (2026). *Sharp Bounds on the Mean Efficiency of a Fluctuating Machine*. DOI: [10.48550/arXiv.2609.15443](https://doi.org/10.48550/arXiv.2609.15443). URL: <https://arxiv.org/abs/2609.15443v3>.

*Commentary.*

μ₃ is threeMomentWitness. Its exact weights and atoms give the first three prescribed moments.

**Theorem 1.9 (Attainment, two-point infeasibility, and strict improvement).**

$$\begin{aligned}&M_{4}(\mu_{4}) \land \operatorname{meanEfficiency}(\mu_{4})=\frac{11}{18}\\&\land (\forall \mu:\mathcal{M}(\mathbb{R}), M_{4}(\mu)\implies\operatorname{meanEfficiency}(\mu)\le\frac{11}{18})\\&\land (\forall \mu:\mathcal{M}(\mathbb{R}), M_{4}(\mu)\implies\forall a,b:\mathbb{R}, \neg(\forall^{\mathrm{ae}}_{x\sim\mu} (x=a\lor x=b)))\\&\land M_{3}(\mu_{3}) \land \operatorname{meanEfficiency}(\mu_{3})=\frac{37}{60}\\&\land (\forall \nu:\mathcal{M}(\mathbb{R}), M_{4}(\nu)\implies\operatorname{meanEfficiency}(\nu)<\operatorname{meanEfficiency}(\mu_{3}))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Stieltjes/FarihFourthMoment.result` (`✓ std3`). ∎

*Resolves.* `Problems/farih-fourth-moment-mean-efficiency` (proved) by `D5/S3/Analytic/Stieltjes/FarihFourthMoment.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"farih-fourth-moment-mean-efficiency","declaration_gid":"D5/S3/Analytic/Stieltjes/FarihFourthMoment.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Badr Farih (2026). *Sharp Bounds on the Mean Efficiency of a Fluctuating Machine*. DOI: [10.48550/arXiv.2609.15443](https://doi.org/10.48550/arXiv.2609.15443). URL: <https://arxiv.org/abs/2609.15443v3>.

*Commentary.*

Write ℳ(ℝ) for all Borel measures on ℝ. The superscript ae and subscript x ∼ μ bind x almost everywhere with respect to μ. The upper bound holds for every feasible μ, and μ₄ attains it. Two-point concentration is impossible for any pair of real points, including a repeated point. Every four-moment feasible law ν lies strictly below the specific relaxed witness μ₃.

The quartic Q(x) = (x⁴ − 7x³ + 20x² − 32x + 36)/36 has gap Q(x) − (1+x)⁻¹ = x(x−1)²(x−2)²/[36(1+x)]. This identity gives a pointwise majorant on x ≥ 0. All its monomials are integrable on a feasible law. Integrating Q gives 11/18, and the gap vanishes at the three atoms of μ₄.

Concentration on a pair a,b forces the raw-moment recurrence mₙ₊₂ = (a+b)mₙ₊₁ − ab mₙ. Normalization and the first three moments force a+b = 2 and ab = 1/3, hence m₄ = 49/9. This conflicts with 17/3 for every such pair.

Direct integration on μ₃ gives 37/60, exceeding 11/18 by 1/180. In the paper’s earlier bracket, variance 5/3 − 1 = 2/3 gives the upper endpoint U(1,2/3) = 5/8 by Eqs. (13) and (30), a gap of 1/72 from the four-moment maximum. The Lean result carries the strict witness comparison. The general fourth-moment hierarchy, the exact three-moment optimum and its attainment, and optimizer uniqueness lie outside its statement.

## References

- Truth anchor: `D5/S3/Analytic/Stieltjes/FarihFourthMoment.FirstFourMoments`
- Truth anchor: `D5/S3/Analytic/Stieltjes/FarihFourthMoment.FirstThreeMoments`
- Truth anchor: `D5/S3/Analytic/Stieltjes/FarihFourthMoment.HasRawMoment`
- Truth anchor: `D5/S3/Analytic/Stieltjes/FarihFourthMoment.efficiency`
- Truth anchor: `D5/S3/Analytic/Stieltjes/FarihFourthMoment.meanEfficiency`
- Truth anchor: `D5/S3/Analytic/Stieltjes/FarihFourthMoment.rawMoment`
- Truth anchor: `D5/S3/Analytic/Stieltjes/FarihFourthMoment.result`
- Truth anchor: `D5/S3/Analytic/Stieltjes/FarihFourthMoment.threeMomentWitness`
- Truth anchor: `D5/S3/Analytic/Stieltjes/FarihFourthMoment.uniform012`
