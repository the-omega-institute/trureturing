# A positive logarithmic representation of fermionic Renyi entropy

## Abstract

The fermionic Gaussian Renyi function has a positive logarithmic Stieltjes representation for every real order strictly between zero and one.

**Definition 1.1 (The single-mode fermionic entropy).**

$$\forall (\alpha: \mathbb{R}), (\forall (\sigma: \mathbb{R}), ((\operatorname{fermionicRenyiFunction}\left(\alpha, \sigma\right): \mathbb{R}) = \operatorname{D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining.hRenyi}\left(\alpha, \frac{(1) + (\sigma)}{2}\right)))$$

*Formalization.* `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.fermionicRenyiFunction` (`✓ std3`).

*Citation.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

Evaluate the binary Renyi function hRenyi at the probability (1+σ)/2. For |σ|≤1 and positive order different from one, this is the logarithm of the sum of the two powers ((1+σ)/2)^α and ((1−σ)/2)^α, divided by 1−α. It is the single-mode function in Eq. renyi_fermionic_1 of Camilo, Landi and Eliëns (RenyiGaussian_v2.tex, lines 297–301). The total real-valued definition uses Real.rpow and Real.log; it does not insert the Shannon limit at order one.

**Definition 1.2 (The logarithmic density).**

$$\forall (\alpha: \mathbb{R}), (\forall (u: \mathbb{R}), ((\operatorname{fermionicWeight}\left(\alpha, u\right): \mathbb{R}) = \frac{(((2) \cdot (\alpha)) \cdot (\operatorname{Real.sin}\left((\operatorname{Real.pi}) \cdot (\alpha)\right))) \cdot (((1) - ((u)^{2}))^{(\alpha) - (1)})}{((\operatorname{Real.pi}) \cdot ((1) - (\alpha))) \cdot (((((1) + (u))^{(2) \cdot (\alpha)}) + (((1) - (u))^{(2) \cdot (\alpha)})) + (((2) \cdot (((1) - ((u)^{2}))^{\alpha})) \cdot (\operatorname{Real.cos}\left((\operatorname{Real.pi}) \cdot (\alpha)\right))))}))$$

*Formalization.* `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.fermionicWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The density has the positive sine factor for orders between zero and one, a power of 1−u², and a denominator with a plus cosine term. The formula defines a total real function; the positivity and integrability assertions below specify its entropy range.

**Theorem 1.3 (Strict positivity of the density).**

$$\forall (\alpha: \mathbb{R}), (\forall (u: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 1) \Rightarrow ((0 \le u) \Rightarrow ((u < 1) \Rightarrow (0 < \operatorname{fermionicWeight}\left(\alpha, u\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.weight_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For 0<α<1 and 0≤u<1, the sine and the power of 1−u² are positive. Rescaling the denominator gives a positive multiple of the Poisson quadratic at a negative real argument. All numerator and denominator factors therefore have the signs needed for strict positivity.

**Theorem 1.4 (Integrability on the open unit interval).**

$$\forall (\alpha: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 1) \Rightarrow (\operatorname{MeasureTheory.IntegrableOn}\left(\operatorname{fermionicWeight}\left(\alpha\right), \operatorname{Set.Ioo}\left((0: \mathbb{R}), 1\right), \operatorname{MeasureTheory.volume}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.weight_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

Multiply the bosonic density of order β by β−1. The fermionic density is the difference of these scaled densities at orders 2α and α, divided by 1−α. Each scaled density is integrable for 0<β<2; at β=1 it is identically zero. The difference formula proves integrability even when 2α=1.

**Theorem 1.5 (The positive logarithmic representation).**

$$\forall (\alpha: \mathbb{R}), (\forall (\sigma: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 1) \Rightarrow ((\left|\sigma\right| \le 1) \Rightarrow ((\operatorname{MeasureTheory.IntegrableOn}\left(\lambda (u: \mathbb{R}) \mapsto ((\operatorname{fermionicWeight}\left(\alpha, u\right)) \cdot (\operatorname{Real.log}\left((1) - (((u)^{2}) \cdot ((\sigma)^{2}))\right))), \operatorname{Set.Ioo}\left((0: \mathbb{R}), 1\right), \operatorname{MeasureTheory.volume}\right)) \land (\operatorname{fermionicRenyiFunction}\left(\alpha, \sigma\right) = (\operatorname{Real.log}\left(2\right)) + (\int_{(u: \mathbb{R}) \in \operatorname{Set.Ioo}\left((0: \mathbb{R}), 1\right)} ((\operatorname{fermionicWeight}\left(\alpha, u\right)) \cdot (\operatorname{Real.log}\left((1) - (((u)^{2}) \cdot ((\sigma)^{2}))\right)))\,du)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.stieltjes_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For a positive spectral argument at most one, apply the bosonic logarithmic representation to its reciprocal at orders α and 2α. Scaling each identity by its order minus one removes the exceptional order one, where the identity reduces directly to elementary logarithms. Factoring the difference of squares into the difference and sum of powers and subtracting the two logarithmic identities gives the fermionic formula with constant log 2. The same density difference gives integrability of the logarithmic integrand, including the pure-mode endpoint. At spectral argument zero the integrand vanishes and h_half evaluates the entropy as log 2. Evenness of the entropy and the squared spectral argument then gives the formula for negative arguments, including minus one.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.fermionicRenyiFunction`
- Truth anchor: `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.fermionicWeight`
- Truth anchor: `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.stieltjes_representation`
- Truth anchor: `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.weight_integrable`
- Truth anchor: `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes.weight_pos`
- Dependency: [D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity](../../Entropy/RenyiCombining/HircheCachinCombiningConcavity.md)
- Dependency: [D5/S3/Quantum/Analysis/BosonicRenyiStieltjes](BosonicRenyiStieltjes.md)
