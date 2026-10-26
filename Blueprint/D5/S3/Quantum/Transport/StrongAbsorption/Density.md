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

**Theorem 1.14 (crossProduct_firstOrder).**

$$\forall (M : (\mathbb{N})) , ((\forall (x : ((Fin M) \to (\mathbb{R}))) , ((\forall (y : ((Fin M) \to (\mathbb{R}))) , (((\sum p : Fin M \times Fin M , (x p . 1 - y p . 2)) = (M : (\mathbb{R})) \cdot ((\sum i , x i) - (\sum j , y j))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct_firstOrder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Definition 1.15 (jointSum).**

$$\forall (M : (\mathbb{N})) , ((\forall (p : (((Fin M) \to (\mathbb{R})) \times ((Fin M) \to (\mathbb{R})))) , ((jointSum M p = ((\sum i , p . 1 i) + (\sum j , p . 2 j))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Density.jointSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.16 (crossProduct_abs_bound).**

$$\forall (M : (\mathbb{N})) , ((\forall (\varepsilon : (\mathbb{R})) , ((((0 \le \varepsilon)) \to ((((\varepsilon \le 1)) \to ((\forall (x : ((Fin M) \to (\mathbb{R}))) , ((\forall (y : ((Fin M) \to (\mathbb{R}))) , ((((\forall i , (0 \le x i))) \to ((((\forall j , (0 \le y j))) \to ((| crossProduct M \varepsilon x y | \le ((1 + (\sum i , x i) + (\sum j , y j)))^{(M)^{2}}))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct_abs_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Definition 1.17 (budgetPoly).**

$$\forall (M : (\mathbb{N})) , ((budgetPoly M = (((1 + (\operatorname{MvPolynomial}.\operatorname{psum} (Sum (Fin M) (Fin M)) \mathbb{R} 1)))^{(M)^{2}})))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Density.budgetPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.18 (budgetPoly_eval).**

$$\forall (M : (\mathbb{N})) , ((\forall (p : (((Fin M) \to (\mathbb{R})) \times ((Fin M) \to (\mathbb{R})))) , ((eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) (budgetPoly M) = ((1 + jointSum M p))^{(M)^{2}}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.budgetPoly_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.19 (baseWeight_nonneg).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((\forall (p : (((Fin M) \to (\mathbb{R})) \times ((Fin M) \to (\mathbb{R})))) , ((0 \le baseWeight M a p))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.20 (budgetPoly_nonneg).**

$$\forall (M : (\mathbb{N})) , ((\forall (p : (((Fin M) \to (\mathbb{R})) \times ((Fin M) \to (\mathbb{R})))) , ((((p \in (\operatorname{Set}.\operatorname{Ici} (0 : (((Fin M) \to (\mathbb{R})) \times ((Fin M) \to (\mathbb{R}))))))) \to ((0 \le eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) (budgetPoly M)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.budgetPoly_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Definition 1.21 (crossIntegral).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((\forall (\varepsilon : (\mathbb{R})) , ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , ((crossIntegral M a \varepsilon P = (\int p , baseWeight M a p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P \cdot crossProduct M \varepsilon p . 1 p . 2)))))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Definition 1.22 (cutoffIntegral).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((\forall (\gamma : (\mathbb{R})) , ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , ((cutoffIntegral M a \gamma P = (\int p , ((tailSet M \gamma))^{c} . indicator (fun p \mapsto (baseWeight M a p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P \cdot crossProduct M (\gamma)^{-1} p . 1 p . 2)) p)))))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/Density.cutoffIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.23 (baseWeight_eq_zero_off_orthant).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((\forall (p : (((Fin M) \to (\mathbb{R})) \times ((Fin M) \to (\mathbb{R})))) , ((((p \neg \in (\operatorname{Set}.\operatorname{Ici} (0 : (((Fin M) \to (\mathbb{R})) \times ((Fin M) \to (\mathbb{R}))))))) \to ((baseWeight M a p = 0))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_eq_zero_off_orthant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.24 (tail_family_exponential_bound).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((((0 < a)) \to ((\forall (\gamma : (\mathbb{R})) , ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , ((\forall (f : ((((Fin M) \to (\mathbb{R})) \times ((Fin M) \to (\mathbb{R}))) \to (\mathbb{R}))) , ((((\forall p , (| f p | \le baseWeight M a p \cdot | eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P |))) \to ((| \int p in tailSet M \gamma , f p | \le \operatorname{Real}.\operatorname{exp} (- (a \cdot \gamma) / 2) \cdot \int p , baseWeight M (a / 2) p \cdot | eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P |))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.tail_family_exponential_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.25 (law_polynomial_ratio).**

$$\forall (M : (\mathbb{N})) , ((((1 \le M)) \to ((\forall (\gamma : (\mathbb{R})) , ((((0 < \gamma)) \to ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , (((\int p , eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P \,d law M \gamma) = cutoffIntegral M (M : (\mathbb{R})) \gamma P / cutoffIntegral M (M : (\mathbb{R})) \gamma 1))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.law_polynomial_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.26 (cutoffIntegral_eq_sub).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((((0 < a)) \to ((\forall (\gamma : (\mathbb{R})) , ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , ((cutoffIntegral M a \gamma P = crossIntegral M a (\gamma)^{-1} P - \int p in tailSet M \gamma , baseWeight M a p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P \cdot crossProduct M (\gamma)^{-1} p . 1 p . 2))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.cutoffIntegral_eq_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.27 (cutoffIntegral_firstOrder).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((((0 < a)) \to ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , ((FirstOrder (fun \gamma \mapsto (cutoffIntegral M a \gamma P)) (\int p , baseWeight M a p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P) (\int p , baseWeight M a p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) (P \cdot linearDensityPoly M))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/Density.cutoffIntegral_firstOrder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

## References

- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.affine`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.basePolynomial_integrable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_eq_zero_off_orthant`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_mass`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.baseWeight_nonneg`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.budgetPoly`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.budgetPoly_eval`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.budgetPoly_nonneg`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossIntegral`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossIntegrand_integrable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct_abs_bound`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.crossProduct_firstOrder`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.cutoffIntegral`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.cutoffIntegral_eq_sub`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.cutoffIntegral_firstOrder`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.jointSum`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.law_polynomial_firstOrder`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.law_polynomial_ratio`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityIntegral_zero`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityPoly`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.linearDensityPoly_eval`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.measurableSet_tailSet`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.tailSet`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.tail_family_exponential_bound`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/Density.weight_scaled_cutoff`
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Foundations](Foundations.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments](LaguerreMoments.md)
