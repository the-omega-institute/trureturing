# StrongAbsorptionCumulants

## Abstract

StrongAbsorptionCumulants for the strong-absorption cumulant expansion.

Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.

**Definition 1.1 (claim).**

$$claim = (\forall M : \mathbb{N} , 1 \le M \to \forall n : \mathbb{N} , 2 \le n \to \exists C \gamma_{0} : \mathbb{R} , 0 < \gamma_{0} \land \forall \gamma : \mathbb{R} , \gamma_{0} \le \gamma \to |  (- 1 : \mathbb{R})^{n} \cdot kappa M n \gamma - ((n - 1) . factorial / ((M : \mathbb{R})^{2 \cdot n - 2} \cdot  \gamma^{2 \cdot n}) - (2 \cdot n - 1) \cdot n \cdot (n - 1) . factorial / ((M : \mathbb{R})^{2 \cdot n - 2} \cdot  \gamma^{2 \cdot n + 1})) | \le C /  \gamma^{2 \cdot n + 2})$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.claim` (`✓ std3`).

*Citation.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

Novaes, Section 5, p. 7: “we conjecture that, for n > 1,” followed by Eq. (58). Natural n ≥ 2 expresses n > 1. The two coefficients and the absolute remainder bound refer to every M ≥ 1. The constants may depend on M and n.

**Theorem 1.2 (result).**

$$\forall M : \mathbb{N} , 1 \le M \to \forall n : \mathbb{N} , 2 \le n \to \exists C \gamma_{0} : \mathbb{R} , 0 < \gamma_{0} \land \forall \gamma : \mathbb{R} , \gamma_{0} \le \gamma \to |  (- 1 : \mathbb{R})^{n} \cdot kappa M n \gamma - ((n - 1) . factorial / ((M : \mathbb{R})^{2 \cdot n - 2} \cdot  \gamma^{2 \cdot n}) - (2 \cdot n - 1) \cdot n \cdot (n - 1) . factorial / ((M : \mathbb{R})^{2 \cdot n - 2} \cdot  \gamma^{2 \cdot n + 1})) | \le C /  \gamma^{2 \cdot n + 2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result` (`✓ std3`). ∎

*Resolves.* `Problems/novaes-2023-strong-absorption-cumulants` (proved) by `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"novaes-2023-strong-absorption-cumulants","declaration_gid":"D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Novaes (2023). *Time delay statistics for chaotic cavities with absorption*. DOI: [10.1007/s10955-023-03183-7](https://doi.org/10.1007/s10955-023-03183-7). URL: <https://arxiv.org/abs/2305.18235v1>.

*Commentary.*

For every positive channel number and every cumulant order at least two, the normalized law has the two strong-absorption coefficients of Novaes, Eq. (58).

**Definition 1.3 (baseExpectation).**

$$\forall (M : (\mathbb{N})) , ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , ((baseExpectation M P = ((\int p , baseWeight M (M : (\mathbb{R})) p \cdot eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P) / ((partition M (M : (\mathbb{R}))))^{2})))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.baseExpectation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Definition 1.4 (singleWMoment).**

$$\forall (M : (\mathbb{N})) , ((\forall (r : (\mathbb{N})) , ((singleWMoment M r = ((\int x , laguerreWeight M (M : (\mathbb{R})) x \cdot (\operatorname{Finset}.\operatorname{univ}.\operatorname{expect} (fun i \mapsto ((x i)^{2}))) \cdot ((\operatorname{Finset}.\operatorname{univ}.\operatorname{expect} x))^{r}) / partition M (M : (\mathbb{R})))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.singleWMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.5 (baseExpectation_add).**

$$\forall (M : (\mathbb{N})) , ((((1 \le M)) \to ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , ((\forall (Q : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , ((baseExpectation M (P + Q) = baseExpectation M P + baseExpectation M Q))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.baseExpectation_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.6 (law_polynomial_integrable).**

$$\forall (M : (\mathbb{N})) , ((((1 \le M)) \to ((\forall (\gamma : (\mathbb{R})) , ((((0 < \gamma)) \to ((\forall (P : (MvPolynomial (Sum (Fin M) (Fin M)) \mathbb{R})) , ((Integrable (fun p \mapsto (eval (\operatorname{Sum}.\operatorname{elim} p . 1 p . 2) P)) (law M \gamma)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.law_polynomial_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.7 (rescaled_pow_integrable).**

$$\forall (M : (\mathbb{N})) , ((((1 \le M)) \to ((\forall (\gamma : (\mathbb{R})) , ((((0 < \gamma)) \to ((\forall (r : (\mathbb{N})) , ((Integrable (fun p \mapsto ((rescaledObservable M \gamma p)^{r})) (law M \gamma)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.rescaled_pow_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.8 (singleWMoment_derivative).**

$$\forall (M : (\mathbb{N})) , ((((1 \le M)) \to ((\forall (r : (\mathbb{N})) , ((singleWMoment M r = iteratedDeriv r (laguerreHw M) 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.singleWMoment_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.9 (rescaledMomentExpansion).**

$$\forall M : (\mathbb{N}) , ((1 \le M) \to (\forall r : (\mathbb{N}) , (FirstOrder ((fun \gamma \mapsto (\operatorname{ProbabilityTheory}.\operatorname{moment} (rescaledObservable M \gamma) r (law M \gamma)))) (expJet (gammaCGF (((M : (\mathbb{R})))^{2})) r) (correctionJet (gammaCGF (((M : (\mathbb{R})))^{2})) (correctionCGF (((M : (\mathbb{R})))^{2})) r))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.rescaledMomentExpansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

## References

- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.baseExpectation`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.baseExpectation_add`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.claim`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.law_polynomial_integrable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.rescaledMomentExpansion`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.rescaled_pow_integrable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.result`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.singleWMoment`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorptionCumulants.singleWMoment_derivative`
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Density](StrongAbsorption/Density.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Foundations](StrongAbsorption/Foundations.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments](StrongAbsorption/LaguerreMoments.md)
