# TracePreservingEigenvalueBound

## Abstract

TracePreservingEigenvalueBound for the spectral bound of conditionally two-positive maps.

**Definition 1.1 (Source Theorem 1 Bound).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{SourceTheorem1Bound} \phi \Leftrightarrow ((\operatorname{LinearMap} . \operatorname{trace} \mathbb{C} (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) \phi)) . \operatorname{re} \leq (\operatorname{d} : \mathbb{R}) * \operatorname{minReSpectrum} \phi + ((\operatorname{d} : \mathbb{R})^{2} - \operatorname{d})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.SourceTheorem1Bound` (`✓ std3`).

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for SourceTheorem1Bound. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Definition 1.2 (Source Theorem 1 Goal).**

$$\operatorname{SourceTheorem1Goal} \Leftrightarrow \forall (\operatorname{d} : \mathbb{N}) , 0 < \operatorname{d} \to \forall \phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) , (\operatorname{KPositive} 2 \operatorname{d} \phi) \to (\forall \operatorname{X} , \operatorname{Matrix} . \operatorname{trace} (\phi \operatorname{X}) = \operatorname{Matrix} . \operatorname{trace} \operatorname{X}) \to \operatorname{SourceTheorem1Bound} \phi$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.SourceTheorem1Goal` (`✓ std3`).

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

Theorem 1, page 4, arXiv:2506.02145v1: "Let Φ ∈ L(ℂ^{d×d}) be a 2-positive and trace-preserving linear map. Then" tr(Φ) ≤ d min ℜ(σ(Φ)) + (d² − d). Trace preservation is equality of Matrix.trace before and after Φ for every matrix.

**Definition 1.3 (congrEquiv).**

$$\forall (\operatorname{d} : \mathbb{N}) (\operatorname{R} \operatorname{S} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) (\operatorname{hRS} : \operatorname{R} * \operatorname{S} = 1) (\operatorname{hSR} : \operatorname{S} * \operatorname{R} = 1) , (\operatorname{congrEquiv} \operatorname{R} \operatorname{S} \operatorname{hRS} \operatorname{hSR}) . \operatorname{toLinearMap} = \operatorname{LinearMap} . \operatorname{mulLeftRight} \mathbb{C} (\operatorname{R} , \operatorname{R} . \operatorname{conjTranspose}) \land (\operatorname{congrEquiv} \operatorname{R} \operatorname{S} \operatorname{hRS} \operatorname{hSR}) . \operatorname{symm} . \operatorname{toLinearMap} = \operatorname{LinearMap} . \operatorname{mulLeftRight} \mathbb{C} (\operatorname{S} , \operatorname{S} . \operatorname{conjTranspose})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.congrEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for congrEquiv. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.4 (hsAdjoint trace).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{hsInner}] , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{LinearMap} . \operatorname{trace} \mathbb{C} ((\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) (\operatorname{LinearMap} . \operatorname{adjoint} \operatorname{Phi}) = \operatorname{star} (\operatorname{LinearMap} . \operatorname{trace} \mathbb{C} ((\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) \operatorname{Phi})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.hsAdjoint_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for hsAdjoint_trace. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.5 (extrema hsAdjoint).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{hsInner}] , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{minReSpectrum} (\operatorname{LinearMap} . \operatorname{adjoint} \operatorname{Phi}) = \operatorname{minReSpectrum} \operatorname{Phi} \land \operatorname{maxReSpectrum} (\operatorname{LinearMap} . \operatorname{adjoint} \operatorname{Phi}) = \operatorname{maxReSpectrum} \operatorname{Phi}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.extrema_hsAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for extrema_hsAdjoint. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.6 (extrema conj).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{e} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) \equiv_{l[\mathbb{C}]} (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{minReSpectrum} (\operatorname{e} . \operatorname{conj} \operatorname{Phi}) = \operatorname{minReSpectrum} \operatorname{Phi} \land \operatorname{maxReSpectrum} (\operatorname{e} . \operatorname{conj} \operatorname{Phi}) = \operatorname{maxReSpectrum} \operatorname{Phi}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.extrema_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for extrema_conj. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.7 (faithful fourth roots).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{rho} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , (\operatorname{rho} . \operatorname{PosDef}) \to \exists \operatorname{R} \operatorname{S} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) , \operatorname{R} . \operatorname{IsHermitian} \land \operatorname{S} . \operatorname{IsHermitian} \land \operatorname{R} * \operatorname{S} = 1 \land \operatorname{S} * \operatorname{R} = 1 \land (\operatorname{S} * \operatorname{S}) * (\operatorname{S} * \operatorname{S}) = \operatorname{rho}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.faithful_fourth_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for faithful_fourth_roots. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.8 (real limit preserves bound).**

$$\forall (\operatorname{f} \operatorname{g} : \mathbb{R} \to \mathbb{R}) , \forall (\operatorname{a} \operatorname{b} : \mathbb{R}) , (\forall \operatorname{t} , 0 < \operatorname{t} \to \operatorname{f} \operatorname{t} \leq \operatorname{g} \operatorname{t}) \to (\operatorname{Tendsto} \operatorname{f} \operatorname{atTop} (\operatorname{nhds} \operatorname{a})) \to (\operatorname{Tendsto} \operatorname{g} \operatorname{atTop} (\operatorname{nhds} \operatorname{b})) \to \operatorname{a} \leq \operatorname{b}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.real_limit_preserves_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for real_limit_preserves_bound. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.9 (real limit preserves bound within).**

$$\forall (\operatorname{f} \operatorname{g} : \mathbb{R} \to \mathbb{R}) (\operatorname{a} \operatorname{b} : \mathbb{R}) , \operatorname{Filter} . \operatorname{Eventually} (\lambda (\operatorname{t} : \mathbb{R}) \mapsto \operatorname{f} \operatorname{t} \leq \operatorname{g} \operatorname{t}) (\operatorname{nhdsWithin} 0 (\operatorname{Ioi} 0)) \to \operatorname{Tendsto} \operatorname{f} (\operatorname{nhdsWithin} 0 (\operatorname{Ioi} 0)) (\operatorname{nhds} \operatorname{a}) \to \operatorname{Tendsto} \operatorname{g} (\operatorname{nhdsWithin} 0 (\operatorname{Ioi} 0)) (\operatorname{nhds} \operatorname{b}) \to \operatorname{a} \leq \operatorname{b}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.real_limit_preserves_bound_within` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for real_limit_preserves_bound_within. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.10 (theorem1 general).**

$$\operatorname{SourceTheorem1Goal}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.theorem1_general` (`✓ std3`). ∎

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

Theorem 1, page 4, arXiv:2506.02145v1: "Let Φ ∈ L(ℂ^{d×d}) be a 2-positive and trace-preserving linear map. Then" tr(Φ) ≤ d min ℜ(σ(Φ)) + (d² − d). SourceTheorem1Goal states this for every positive dimension. The weighted Hilbert–Schmidt symmetric part supplies a real eigenvalue no larger than the real part of any original eigenvalue. Diagonalization then gives the transition estimate; depolarizing approximation removes faithfulness of the invariant state.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.SourceTheorem1Bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.SourceTheorem1Goal`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.congrEquiv`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.extrema_conj`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.extrema_hsAdjoint`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.faithful_fourth_roots`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.hsAdjoint_trace`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.real_limit_preserves_bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.real_limit_preserves_bound_within`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.theorem1_general`
- Dependency: [D5/S3/Quantum/ChannelFixedState](../ChannelFixedState.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace](TwoPositiveTransitionTrace.md)
