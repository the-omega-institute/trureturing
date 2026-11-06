# The power Poisson density and its Stieltjes transform

## Abstract

The power Poisson density has reciprocal reflection symmetry and an explicit positive-axis Stieltjes transform.

**Theorem 1.1 (Strict positivity of the power Poisson denominator).**

$$\forall (\alpha: \mathbb{R}), (\forall (r: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow ((\alpha \ne 1) \Rightarrow (0 < ((1) - (((2) \cdot (r)) \cdot (\operatorname{Real.cos}\left((\operatorname{Real.pi}) \cdot (\alpha)\right)))) + ((r)^{2}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.power_poisson_denominator_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

For every real r, the Poisson quadratic is strictly positive when 0<α<2 and α is different from one. Below one, sin(πα)>0; above one, reflecting the angle makes its sine positive without changing its cosine. The sum-of-squares identity for the Poisson denominator proves the assertion in both cases.

**Theorem 1.2 (The signed sine factor).**

$$\forall (\alpha: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow ((\alpha \ne 1) \Rightarrow (0 < \frac{-(\operatorname{Real.sin}\left((\operatorname{Real.pi}) \cdot (\alpha)\right))}{(\alpha) - (1)}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.sine_factor_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

Below one, sin(πα) is positive and α−1 is negative. Above one, the sine is negative and α−1 is positive. Thus −sin(πα)/(α−1) is strictly positive throughout the stated range.

**Theorem 1.3 (A nondegenerate Poisson angle).**

$$\forall (\alpha: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow ((\alpha \ne 1) \Rightarrow (\operatorname{Real.cos}\left((\operatorname{Real.pi}) \cdot (\alpha)\right) < 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.cosine_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

Positivity of the signed sine factor implies that sin(πα) is nonzero. Equality in the universal bound cos(πα)≤1 would force that sine to vanish, so the bound is strict.

**Definition 1.4 (The power Poisson density).**

$$\forall (\alpha: \mathbb{R}), (\forall (q: \mathbb{R}), ((\operatorname{density}\left(\alpha, q\right): \mathbb{R}) = \frac{((\alpha) \cdot ((q)^{(\alpha) - (1)})) \cdot (-(\operatorname{Real.sin}\left((\operatorname{Real.pi}) \cdot (\alpha)\right)))}{((\operatorname{Real.pi}) \cdot ((\alpha) - (1))) \cdot (((1) - (((2) \cdot ((q)^{\alpha})) \cdot (\operatorname{Real.cos}\left((\operatorname{Real.pi}) \cdot (\alpha)\right)))) + (((q)^{\alpha})^{2}))}))$$

*Formalization.* `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.density` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The density is obtained from the Poisson quadratic by the substitution p=q^α. Its numerator includes the derivative factor α q^(α−1) and the signed angular factor. Real powers and division make this a total real function; positivity is used only with the stated restrictions on α and q.

**Theorem 1.5 (Reciprocal reflection of the density).**

$$\forall (\alpha: \mathbb{R}), (\forall (q: \mathbb{R}), ((0 < q) \Rightarrow ((\alpha \ne 1) \Rightarrow ((\operatorname{Real.cos}\left((\operatorname{Real.pi}) \cdot (\alpha)\right) < 1) \Rightarrow (\frac{\operatorname{density}\left(\alpha, \operatorname{Inv.inv}\left(q\right)\right)}{(q)^{2}} = \operatorname{density}\left(\alpha, q\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.density_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

Replacing q by its reciprocal multiplies the density by q². Real-power inversion and the Poisson denominator identity prove this equality for positive q whenever α differs from one and cos(πα)<1.

**Theorem 1.6 (Reciprocal reflection with a resolvent).**

$$\forall (\alpha: \mathbb{R}), (\forall (r: \mathbb{R}), (\forall (q: \mathbb{R}), ((0 < r) \Rightarrow ((0 < q) \Rightarrow ((\alpha \ne 1) \Rightarrow ((\operatorname{Real.cos}\left((\operatorname{Real.pi}) \cdot (\alpha)\right) < 1) \Rightarrow ((\left|-(\operatorname{Inv.inv}\left((q)^{2}\right))\right|) \cdot (\frac{\operatorname{density}\left(\alpha, \operatorname{Inv.inv}\left(q\right)\right)}{(r) + (\operatorname{Inv.inv}\left(q\right))}) = \frac{(\operatorname{density}\left(\alpha, q\right)) \cdot (q)}{(1) + ((r) \cdot (q))})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.density_resolvent_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The absolute Jacobian of q↦q⁻¹ is |−(q²)⁻¹|. Combining it with the reciprocal density identity transforms the resolvent at q⁻¹ into density(α,q) q/(1+r q). Positivity of r and q keeps the denominators nonzero.

**Theorem 1.7 (The explicit Stieltjes transform).**

$$\forall (\alpha: \mathbb{R}), (\forall (r: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha < 2) \Rightarrow ((\alpha \ne 1) \Rightarrow ((0 < r) \Rightarrow ((r < 1) \Rightarrow ((\operatorname{MeasureTheory.IntegrableOn}\left(\lambda (q: \mathbb{R}) \mapsto (\frac{\operatorname{density}\left(\alpha, q\right)}{(r) + (q)}), \operatorname{Set.Ioi}\left((0: \mathbb{R})\right), \operatorname{MeasureTheory.volume}\right)) \land (\int_{(q: \mathbb{R}) \in \operatorname{Set.Ioi}\left((0: \mathbb{R})\right)} (\frac{\operatorname{density}\left(\alpha, q\right)}{(r) + (q)})\,dq = (\frac{1}{((\alpha) - (1)) \cdot ((1) - (r))}) - (\frac{(\alpha) \cdot ((r)^{(\alpha) - (1)})}{((\alpha) - (1)) \cdot ((1) - ((r)^{\alpha}))})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.stieltjes_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giancarlo Camilo, Gabriel T. Landi, Sebas Eliëns (2019). *Strong subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*. DOI: [10.1103/PhysRevB.99.045155](https://doi.org/10.1103/PhysRevB.99.045155). URL: <https://arxiv.org/abs/1810.07070v2>.

*Commentary.*

The transform is integrable at zero and infinity by power bounds and reciprocal reflection. Work on a logarithmic strip of height 2π, using the removable extension of the transform at one and the regularized kernel at log r. The regularized kernel has zero boundary integral on each rectangle. The two horizontal edges give the jump across the negative real axis, equal to the density times the Poisson normalization. With the vertical integrals taken with respect to the increasing imaginary coordinate, the left limit is zero and the right limit is (2π) • (−complexTransform α r). The real part of the left limit minus the right limit is therefore 2π times the real part of the transform. Substituting q=exp(x) then gives the stated positive-axis integral for 0<r<1.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.cosine_lt_one`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.density`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.density_reflection`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.density_resolvent_reflection`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.power_poisson_denominator_pos`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.sine_factor_pos`
- Truth anchor: `D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.stieltjes_integral`
- Dependency: [D5/S3/TotalVariation/IndependentConvolutionL1Minimum](../../../TotalVariation/IndependentConvolutionL1Minimum.md)
