# Density

## Abstract

Density for the strong-absorption cumulant expansion.

Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.

**Definition 1.1 (crossProduct).**

$$\forall (M : \mathbb{N}) , \forall (\varepsilon : \mathbb{R}) , \forall (x : Fin M \to \mathbb{R}) , \forall (y : Fin M \to \mathbb{R}) , crossProduct M \varepsilon x y = (\prod i , \prod j , (1 + \varepsilon \cdot (x i - y j)))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.2 (tailSet).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , tailSet M \gamma = (\{p | \exists j , \gamma < p . 2 j\})$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Density.tailSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.3 (linearDensityPoly).**

$$\forall (M : \mathbb{N}) , linearDensityPoly M = (C (M : \mathbb{R}) \cdot ((\sum i : Fin M , X (\operatorname{Sum}.\operatorname{inl} i)) - (\sum j : Fin M , X (\operatorname{Sum}.\operatorname{inr} j))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Theorem 1.4 (measurableSet_tailSet).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , MeasurableSet (tailSet M \gamma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.measurableSet_tailSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.5 (linearDensityPoly_eval).**

$$\forall (M : \mathbb{N}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) (linearDensityPoly M) = (M : \mathbb{R}) \cdot ((\sum i , p . 1 i) - (\sum j , p . 2 j))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityPoly_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.6 (FirstOrder.affine).**

$$\forall (a : \mathbb{R}) , \forall (b : \mathbb{R}) , FirstOrder (fun \gamma \mapsto a + b \cdot \gamma^{-1}) a b$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Definition 1.7 (baseWeight).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , baseWeight M a p = (laguerreWeight M a p . 1 \cdot laguerreWeight M a p . 2)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Theorem 1.8 (baseWeight_mass).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , (\int p , baseWeight M a p) =  (partition M a)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.9 (linearDensityIntegral_zero).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , (\int p , baseWeight M a p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) (linearDensityPoly M)) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityIntegral_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.10 (basePolynomial_integrable).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , \forall (P : MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R}) , (0 < a) \to Integrable (fun p \mapsto baseWeight M a p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.basePolynomial_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.11 (weight_scaled_cutoff).**

$$\forall (M : \mathbb{N}) , \forall (\gamma : \mathbb{R}) , \forall (p : (Fin M \to \mathbb{R}) \times (Fin M \to \mathbb{R})) , (0 < \gamma) \to weight M \gamma p =  \gamma^{M^{2}} \cdot (tailSet M \gamma) ^{c} . indicator (fun p \mapsto baseWeight M M p \cdot crossProduct M \gamma^{-1} p . 1 p . 2) p$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.weight_scaled_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.12 (crossIntegrand_integrable).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , \forall (\varepsilon : \mathbb{R}) , \forall (P : MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R}) , (0 < a) \to Integrable (fun p \mapsto baseWeight M a p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P \cdot crossProduct M \varepsilon p . 1 p . 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossIntegrand_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.13 (law_polynomial_firstOrder).**

$$\forall (M : \mathbb{N}) , \forall (P : MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R}) , (1 \le M) \to FirstOrder (fun \gamma \mapsto \int p , eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P d law M \gamma) ((\int p , baseWeight M M p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P) /  (partition M M)^{2}) ((\int p , baseWeight M M p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) (P \cdot linearDensityPoly M)) /  (partition M M)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.law_polynomial_firstOrder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

## References

- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.affine`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.basePolynomial_integrable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_mass`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossIntegrand_integrable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.law_polynomial_firstOrder`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityIntegral_zero`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityPoly`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityPoly_eval`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.measurableSet_tailSet`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.tailSet`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.weight_scaled_cutoff`
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments](LaguerreMoments.md)
