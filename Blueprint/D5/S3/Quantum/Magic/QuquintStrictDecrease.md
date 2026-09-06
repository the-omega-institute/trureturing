# Ququint Strict Directional Decrease

## Abstract

Exact normalized variation and strict mana decrease on the constrained tangent family.

**Definition 1.1 (Normalized perturbation).**

$$\forall v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangent},\forall e:\mathbb{R},\mathrm{normalizedPerturbation}(v,e)=\mathrm{Norm}.\mathrm{norm}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi}+e\cdot(v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))^{-1}\cdot(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi}+e\cdot(v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintStrictDecrease.normalizedPerturbation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The inverse norm is real scalar multiplication on the complex Euclidean state space.

**Theorem 1.2 (The normalization denominator).**

$$\forall v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangent},\forall e:\mathbb{R},\mathrm{Norm}.\mathrm{norm}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi}+e\cdot(v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))^{2}=1+e^{2}\cdot\mathrm{Norm}.\mathrm{norm}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintStrictDecrease.perturbation_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

The orthogonality field of tangent removes the cross term. The exact norm of psi is one; the denominator is positive for every real parameter.

**Theorem 1.3 (Every normalized Wigner entry).**

$$\forall v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangent},\forall e:\mathbb{R},\forall q p:\mathrm{Fin} 5,\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}(\mathrm{normalizedPerturbation}(v,e),q,p)=\frac{\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi},q,p)+e\cdot(2\cdot\mathrm{Complex}.\mathrm{re}(\mathrm{dotProduct}(\mathrm{star}(\mathrm{WithLp}.\mathrm{ofLp}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi})),\mathrm{Matrix}.\mathrm{mulVec}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{phasePoint}(q,p),\mathrm{WithLp}.\mathrm{ofLp}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State})))))/5)+e^{2}\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{wigner}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}),q,p)}{1+e^{2}\cdot\mathrm{Norm}.\mathrm{norm}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintStrictDecrease.normalized_wigner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

wigner_expand supplies the exact quadratic numerator. Real homogeneity and perturbation_norm_sq supply the denominator.

**Theorem 1.4 (The exact local change).**

$$\forall v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangent},\mathrm{Filter}.\mathrm{Eventually}(((e:\mathbb{R})\mapsto\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{normalizedPerturbation}(v,e))-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi})=\frac{e^{2}\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintFiniteMaximum}.\mathrm{secondVariation}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))}{1+e^{2}\cdot\mathrm{Norm}.\mathrm{norm}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))^{2}}),\mathrm{nhds}((0:\mathbb{R})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintStrictDecrease.exact_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

Continuity keeps the sign fixed at each nonzero Wigner entry near zero. At zeroPoints the tangent constraint leaves a squared parameter times the absolute quadratic coefficient. first_coefficient_zero consumes gradient_psi to cancel the summed linear term. The remaining coefficient is exactly secondVariation.

**Theorem 1.5 (Strict decrease of the norm sum and mana).**

$$\forall v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{tangent},v\neq0\implies\exists delta:\mathbb{R},0<delta \land (\forall e:\mathbb{R},0<\mathrm{abs}(e)\implies\mathrm{abs}(e)<delta\implies(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{normalizedPerturbation}(v,e))-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi})=\frac{e^{2}\cdot\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintFiniteMaximum}.\mathrm{secondVariation}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))}{1+e^{2}\cdot\mathrm{Norm}.\mathrm{norm}((v:\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{State}))^{2}} \land \mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{normalizedPerturbation}(v,e))<\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi}) \land \mathrm{Real}.\mathrm{log}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{normalizedPerturbation}(v,e)))<\mathrm{Real}.\mathrm{log}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{lOne}(\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintWignerCriticalGeometry}.\mathrm{psi}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintStrictDecrease.directional_decrease` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Muhammad Erew and Moshe Goldstein (2025). *Extremizing Measures of Magic on Pure States by Clifford-stabilizer States*. DOI: [10.48550/arXiv.2512.19657](https://doi.org/10.48550/arXiv.2512.19657).

*Commentary.*

second_variation_negative consumes negativity_iff, the finite sign maximum identity, and all thirty-two LDL certificates. A nonzero real parameter has positive square. Positivity near zero allows Real.log_lt_log to give strict mana decrease.

This result concerns only the specified dimension-five state and nonzero directions in tangent. It does not classify other directions, dimensions or critical points, solve general mana extremisation, identify Claim C as an author-verbatim conjecture, or assert global novelty beyond the recorded search.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QuquintStrictDecrease.directional_decrease`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintStrictDecrease.exact_change`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintStrictDecrease.normalizedPerturbation`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintStrictDecrease.normalized_wigner`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintStrictDecrease.perturbation_norm_sq`
- Dependency: [D5/S3/Quantum/Magic/QuquintFiniteMaximum](QuquintFiniteMaximum.md)
