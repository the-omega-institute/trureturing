# FaithfulPerronRegularization

## Abstract

FaithfulPerronRegularization for the spectral bound of conditionally two-positive maps.

**Definition 1.1 (Regularized).**

$$\forall (\operatorname{d} : \mathbb{N}) (\operatorname{T} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) (\operatorname{epsilon} : \mathbb{R}) (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) , \operatorname{Regularized} \operatorname{T} \operatorname{epsilon} \operatorname{X} = \operatorname{T} \operatorname{X} + (\operatorname{epsilon} : \mathbb{C}) \cdot (\operatorname{Matrix} . \operatorname{trace} \operatorname{X} \cdot (1 : \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.Regularized` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for Regularized. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Definition 1.2 (PerronCertificate).**

$$\forall (\operatorname{d} : \mathbb{N}) (\operatorname{T} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) (\operatorname{p} : \operatorname{PerronCertificate} \operatorname{T}) , \operatorname{p} . \operatorname{rho} . \operatorname{PosDef} \land \operatorname{Matrix} . \operatorname{trace} \operatorname{p} . \operatorname{rho} = 1 \land \operatorname{T} \operatorname{p} . \operatorname{rho} = (\operatorname{p} . \operatorname{c} : \mathbb{C}) \cdot \operatorname{p} . \operatorname{rho} \land 0 < \operatorname{p} . \operatorname{c} \land \operatorname{p} . \operatorname{c} = \operatorname{maxReSpectrum} \operatorname{T} \land \operatorname{spectralRadius} \mathbb{C} \operatorname{T} . \operatorname{toContinuousLinearMap} = \operatorname{ENNReal} . \operatorname{ofReal} \operatorname{p} . \operatorname{c}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.PerronCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The carrier contains rho and c with all six displayed constraints: positive definiteness, normalized matrix trace, the eigenmatrix equation, positivity of c, maximal real part, and the spectral radius. The displayed fields rho : Matrix (Fin d) (Fin d) ℂ and c : ℝ have these types.

**Definition 1.3 (RegularizedPerronGoal).**

$$\operatorname{RegularizedPerronGoal} \Leftrightarrow \forall (\operatorname{d} : \mathbb{N}) , 0 < \operatorname{d} \to \forall (\operatorname{T} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) (\varepsilon : \mathbb{R}) , 0 < \varepsilon \to (\operatorname{KPositive} 2 \operatorname{d} \operatorname{T}) \to \operatorname{Nonempty} (\operatorname{PerronCertificate} (\operatorname{Regularized} \operatorname{T} \varepsilon))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.RegularizedPerronGoal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for RegularizedPerronGoal. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.4 (strict positive perron eigenmatrix).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{NeZero} \operatorname{d}] , \forall (\operatorname{T} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , (\forall \operatorname{X} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) , \operatorname{X} . \operatorname{PosSemidef} \to (\operatorname{T} \operatorname{X}) . \operatorname{PosSemidef}) \to (\forall \operatorname{X} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) , \operatorname{X} . \operatorname{PosSemidef} \to \operatorname{X} \neq 0 \to (\operatorname{T} \operatorname{X}) . \operatorname{PosDef}) \to \exists (\rho : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) (\operatorname{c} : \mathbb{R}) , \rho . \operatorname{PosDef} \land \operatorname{Matrix} . \operatorname{trace} \rho = 1 \land 0 < \operatorname{c} \land \operatorname{T} \rho = (\operatorname{c} : \mathbb{C}) \cdot \rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.strict_positive_perron_eigenmatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

Compactness of the normalized positive cone gives a minimum Collatz parameter. Strict positivity makes its minimizing matrix faithful. A nonzero residual can be lowered, contradicting minimality, so the minimizer is an eigenmatrix with a positive eigenvalue.

**Theorem 1.5 (regularized perron certificate).**

$$\operatorname{RegularizedPerronGoal}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.regularized_perron_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The trace-to-identity perturbation is strictly positivity improving. Its faithful Perron eigenmatrix controls every eigenvalue modulus; the Perron eigenvalue is both the maximal real part and the spectral radius.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.PerronCertificate`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.Regularized`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.RegularizedPerronGoal`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.regularized_perron_certificate`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization.strict_positive_perron_eigenmatrix`
- Dependency: [D5/S3/Quantum/Fibers/PhysicalFiber](../Fibers/PhysicalFiber.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace](TwoPositiveTransitionTrace.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
