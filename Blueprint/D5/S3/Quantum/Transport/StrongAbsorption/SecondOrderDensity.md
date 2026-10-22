# SecondOrderDensity

## Abstract

SecondOrderDensity for strong-absorption moments.

Real arithmetic is used in all coefficients. Integrals without an explicit measure use volume. M is the channel count; n is the moment order.

**Definition 1.1 (quadraticDensityPoly).**

$$\forall (M : (\mathbb{N})) , ((quadraticDensityPoly M = (C (1 / 2 : (\mathbb{R})) \cdot (((linearDensityPoly M))^{2} - C (M : (\mathbb{R})) \cdot ((\sum i : Fin M , ((X (\operatorname{Sum}.\operatorname{inl} i)))^{2}) + (\sum j : Fin M , ((X (\operatorname{Sum}.\operatorname{inr} j)))^{2})) + C 2 \cdot (\sum i : Fin M , X (\operatorname{Sum}.\operatorname{inl} i)) \cdot (\sum j : Fin M , X (\operatorname{Sum}.\operatorname{inr} j))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity.quadraticDensityPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used to evaluate the strong-absorption coefficients.

**Theorem 1.2 (law_polynomial_secondOrder).**

$$\forall (M : (\mathbb{N})) , ((((1 \le M)) \to (((((\int p , baseWeight M (M : (\mathbb{R})) p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) (quadraticDensityPoly M)) = 0)) \to ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , (((fun \gamma \mapsto ((\int p , eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P \,d law M \gamma) - (\int p , baseWeight M (M : (\mathbb{R})) p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P) / ((partition M (M : (\mathbb{R}))))^{2} - (\gamma)^{-1} \cdot ((\int p , baseWeight M (M : (\mathbb{R})) p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) (P \cdot linearDensityPoly M)) / ((partition M (M : (\mathbb{R}))))^{2}) - ((\gamma)^{-1})^{2} \cdot ((\int p , baseWeight M (M : (\mathbb{R})) p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) (P \cdot quadraticDensityPoly M)) / ((partition M (M : (\mathbb{R}))))^{2}))) =^{O} [ atTop ] (fun \gamma : (\mathbb{R}) \mapsto (((\gamma)^{-1})^{3}))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity.law_polynomial_secondOrder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used to evaluate the strong-absorption coefficients.

## References

- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity.law_polynomial_secondOrder`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity.quadraticDensityPoly`
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Density](Density.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Foundations](Foundations.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments](LaguerreMoments.md)
