# Global focusing and generalized entropy

## Abstract

Global Raychaudhuri evolution constrains the total Ricci integral. The generalized entropy derivative gives stationary-cut quantum focusing, an entropy monotonicity theorem, and an integrated energy inequality.

The focusing identity allows continuous integrable Ricci curvature of either sign. The quantum results use a scalar entropy and positive area along an affine generator, with the Raychaudhuri equation and quantum focusing or energy inequalities stated as mathematical hypotheses. The references concern null-local modular flow and the corresponding null-cone gravitational setting.

**Theorem 1.1 (Two-ended decay of global expansion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.raychaudhuri_global_tendsto_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.raychaudhuri_global_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For a global Raychaudhuri solution with continuous integrable Ricci term of arbitrary sign, its Ricci primitive is bounded by the integral of its absolute value. Adding the primitive to the expansion gives a decreasing function. The existing finite-affine focusing bound applied to a shifted expansion and to its time reversal bounds this function on both sides. The nonnegative optical loss is consequently integrable, as are the squared expansion and the expansion derivative. Both endpoint limits exist and must vanish because the squared expansion is integrable.

**Theorem 1.2 (Global integrated focusing identity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.raychaudhuri_global_anec_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.raychaudhuri_global_anec_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The focusing density θ²/2 + σ² is nonnegative. Integrating its derivative relation with the compensated expansion on increasing compact intervals and taking both infinite endpoints proves integrability and identifies its total integral with minus the Ricci integral.

**Theorem 1.3 (Global rigidity under averaged null energy).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.anec_global_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.anec_global_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Nonnegative total Ricci curvature forces zero total focusing density. Nonnegative squares and continuity of the expansion imply pointwise vanishing of the expansion. The derivative equation then gives an almost-everywhere zero Ricci term, which vanishes everywhere by its continuity. The same equation gives pointwise zero shear, and the Ricci integral is zero.

**Theorem 1.4 (Obstruction to global regular expansion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.strict_anec_forces_caustic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.strict_anec_forces_caustic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Strictly positive total Ricci curvature contradicts the nonnegative integral of the focusing density. Hence a regular expansion solving the equation cannot be defined on the entire affine line.

**Theorem 1.5 (Pointwise null energy rigidity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.nec_and_global_forces_zero_ricci`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.nec_and_global_forces_zero_ricci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Nonnegative Ricci curvature implies the averaged hypothesis. The expansion and shear vanish, and the Raychaudhuri equation yields zero Ricci curvature pointwise.

**Definition 1.6 (Generalized entropy).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.generalizedEntropy`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.generalizedEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At each affine parameter, divide the area by 4Gℏ and add the exterior matter entropy.

**Definition 1.7 (Quantum expansion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.quantumExpansion`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.quantumExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Multiply the affine derivative of generalized entropy by 4Gℏ divided by the area.

**Theorem 1.8 (Generalized entropy and quantum expansion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.quantum_expansion_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.quantum_expansion_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The area derivative equals expansion times area. Differentiating generalized entropy and multiplying by four times Newton's constant times Planck's constant divided by area yields the classical expansion plus the rescaled entropy derivative.

**Theorem 1.9 (Derivative of quantum expansion).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.quantum_expansion_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.quantum_expansion_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The reciprocal-area derivative contributes the correction proportional to minus the expansion times the entropy derivative. Combining this with the Raychaudhuri equation gives the full quantum expansion derivative.

**Theorem 1.10 (Stationary-cut equivalence).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.qfc_iff_qnec_at_stationary_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.qfc_iff_qnec_at_stationary_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

At a cut with vanishing expansion and shear the quantum focusing inequality reduces to the quantum null energy inequality. Dividing by the positive factor 8πG cancels Newton's constant exactly, leaving the entropy second derivative times ℏ/(2πA).

**Theorem 1.11 (Generalized second law on a future horizon).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.qfc_implies_gsl`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.qfc_implies_gsl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Under quantum focusing the quantum expansion is antitone. If there are arbitrarily late cuts where it is at least minus any positive tolerance, every earlier value is nonnegative. Positivity of the area and constants transfers this sign to the generalized entropy derivative, proving entropy monotonicity on the future ray.

**Theorem 1.12 (Integrated quantum null energy inequality).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.qnec_implies_anec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.qnec_implies_anec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

With positive constant area and Planck's constant, integrate the pointwise QNEC inequality on finite intervals. The fundamental theorem of calculus rewrites the entropy second derivative integral as the difference of entropy first derivatives. Both endpoint derivatives tend to zero, and the integrable stress tensor has a finite total integral, which is nonnegative.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.anec_global_rigidity`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.generalizedEntropy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.nec_and_global_forces_zero_ricci`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.qfc_iff_qnec_at_stationary_cut`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.qfc_implies_gsl`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.qnec_implies_anec`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.quantumExpansion`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.quantum_expansion_deriv`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.quantum_expansion_eq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.raychaudhuri_global_anec_identity`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.raychaudhuri_global_tendsto_zero`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.strict_anec_forces_caustic`
- Dependency: [D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D](../../../Geometry/Lorentz/SachsJacobsonEinstein4D.md)
