# A positive logarithmic representation of bosonic Renyi entropy

## Abstract

The bosonic Gaussian Renyi function is a positive logarithmic Stieltjes mixture for orders between zero and two, excluding one.

**Definition 1.1 (The single-mode entropy).**

$$\forall (\alpha: \mathbb{R}), (\forall (\nu: \mathbb{R}), ((\operatorname{renyiFunction}\left(\alpha, \nu\right): \mathbb{R}) = \frac{\operatorname{Real.log}\left(((\frac{(\nu) + (1)}{2})^{\alpha}) - ((\frac{(\nu) - (1)}{2})^{\alpha})\right)}{(\alpha) - (1)}))$$

*Formalization.* `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.renyiFunction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The function is the logarithm of the difference of the two real powers, divided by α−1. For ν at least one and positive α different from one, this is the single-mode term in Eq. renyi_bosonic_1 of Camilo, Landi and Eliëns (RenyiGaussian_v2.tex, lines 216–220). The real logarithm and real powers give a total real-valued function also outside this entropy range.

**Definition 1.2 (The additive constant).**

$$\forall (\alpha: \mathbb{R}), ((\operatorname{renyiConstant}\left(\alpha\right): \mathbb{R}) = (\frac{\operatorname{Real.log}\left(\alpha\right)}{(\alpha) - (1)}) - (\operatorname{Real.log}\left(2\right)))$$

*Formalization.* `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.renyiConstant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The constant log(α)/(α−1)−log(2) fixes the asymptotic normalization of the logarithmic representation.

**Definition 1.3 (The logarithmic density).**

$$\forall (\alpha: \mathbb{R}), (\forall (x: \mathbb{R}), ((\operatorname{renyiWeight}\left(\alpha, x\right): \mathbb{R}) = \frac{(((-(2)) \cdot (\alpha)) \cdot (\operatorname{Real.sin}\left((\operatorname{Real.pi}) \cdot (\alpha)\right))) \cdot (((1) - ((x)^{2}))^{(\alpha) - (1)})}{((\operatorname{Real.pi}) \cdot ((\alpha) - (1))) \cdot (((((1) + (x))^{(2) \cdot (\alpha)}) + (((1) - (x))^{(2) \cdot (\alpha)})) - (((2) \cdot (((1) - ((x)^{2}))^{\alpha})) \cdot (\operatorname{Real.cos}\left((\operatorname{Real.pi}) \cdot (\alpha)\right))))}))$$

*Formalization.* `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.renyiWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The real density combines a signed sine factor with a power of 1−x² and a power Poisson denominator. Its positivity and integrability are asserted only for the order and interval ranges specified below.

**Theorem 1.4 (Strict positivity of the density).**

$$\forall (\alpha: \mathbb{R}), (\forall (x: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow ((\alpha \ne 1) \Rightarrow ((0 \le x) \Rightarrow ((x < 1) \Rightarrow (0 < \operatorname{renyiWeight}\left(\alpha, x\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.weight_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For 0<α<2 with α different from one, the signed sine factor is positive. Factoring the denominator into a positive power and a Poisson quadratic proves strict positivity for every 0≤x<1.

**Theorem 1.5 (Integrability at the endpoints).**

$$\forall (\alpha: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow ((\alpha \ne 1) \Rightarrow (\operatorname{MeasureTheory.IntegrableOn}\left(\operatorname{renyiWeight}\left(\alpha\right), \operatorname{Set.Ioo}\left((0: \mathbb{R}), 1\right), \operatorname{MeasureTheory.volume}\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.weight_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The substitutions q=(1−x)/(1+x) and p=q^α give an arctangent primitive. It is continuous at the endpoints, and its derivative on the open interval is the nonnegative density. The fundamental theorem of calculus for a nonnegative derivative proves integrability.

**Theorem 1.6 (Mass one half).**

$$\forall (\alpha: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow ((\alpha \ne 1) \Rightarrow (\int_{(x: \mathbb{R}) \in \operatorname{Set.Ioo}\left((0: \mathbb{R}), 1\right)} (\operatorname{renyiWeight}\left(\alpha, x\right))\,dx = \frac{1}{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.weight_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The same arctangent primitive evaluates the integral as the difference of its values at one and zero. The sine and cosine identities on each side of α=1 make this difference one half.

**Theorem 1.7 (The positive logarithmic representation).**

$$\forall (\alpha: \mathbb{R}), (\forall (\nu: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow ((\alpha \ne 1) \Rightarrow ((1 \le \nu) \Rightarrow ((\operatorname{MeasureTheory.IntegrableOn}\left(\lambda (x: \mathbb{R}) \mapsto ((\operatorname{renyiWeight}\left(\alpha, x\right)) \cdot (\operatorname{Real.log}\left(((\nu)^{2}) - ((x)^{2})\right))), \operatorname{Set.Ioo}\left((0: \mathbb{R}), 1\right), \operatorname{MeasureTheory.volume}\right)) \land (\operatorname{renyiFunction}\left(\alpha, \nu\right) = (\operatorname{renyiConstant}\left(\alpha\right)) + (\int_{(x: \mathbb{R}) \in \operatorname{Set.Ioo}\left((0: \mathbb{R}), 1\right)} ((\operatorname{renyiWeight}\left(\alpha, x\right)) \cdot (\operatorname{Real.log}\left(((\nu)^{2}) - ((x)^{2})\right)))\,dx))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.stieltjes_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For ν>1, the positive-axis Stieltjes transform of the power Poisson density identifies the derivative of the logarithmic integral with the derivative of the single-mode entropy. Their difference is constant; its limit at infinity is renyiConstant, using the density mass one half. Near ν=1, a logarithmic endpoint majorant is integrable. Dominated convergence therefore extends both the integrability and the identity to the pure-mode endpoint ν=1.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.renyiConstant`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.renyiFunction`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.renyiWeight`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.stieltjes_representation`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.weight_integrable`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.weight_mass`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.weight_pos`
- Dependency: [D5/S3/Arith/Robin/LogarithmicMellinReserve](../../Arith/Robin/LogarithmicMellinReserve.md)
- Dependency: [D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight](BosonicRenyiStieltjes/PoissonWeight.md)
