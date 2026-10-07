# ConditionalTwoPositiveSpectralBound

## Abstract

ConditionalTwoPositiveSpectralBound for the spectral bound of conditionally two-positive maps.

**Definition 1.1 (expEnd).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{L} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \forall (\operatorname{t} : \mathbb{R}) , \operatorname{expEnd} \operatorname{L} \operatorname{t} = (\operatorname{NormedSpace} . \operatorname{exp} (\operatorname{t} \cdot \operatorname{L} . \operatorname{toContinuousLinearMap})) . \operatorname{toLinearMap}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.expEnd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The operator exponential of t times the continuous-linear realization of L, returned as a complex-linear endomorphism. Finite dimensionality gives the continuous-linear realization without an additional hypothesis.

**Definition 1.2 (ConditionallyTwoPositive).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{L} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{ConditionallyTwoPositive} \operatorname{L} \Leftrightarrow \forall \operatorname{t} : \mathbb{R} , 0 \leq \operatorname{t} \to (\operatorname{KPositive} 2 \operatorname{d} (\operatorname{expEnd} \operatorname{L} \operatorname{t}))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.ConditionallyTwoPositive` (`✓ std3`).

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

Page 11, arXiv:2506.02145v1: "A map L is called conditionally 2-positive if e^{tL} is 2-positive for all t ≥ 0." KPositive 2 is positivity of MatrixMap.kron LinearMap.id with the map, on matrices indexed by Fin 2 × Fin d; expEnd is the operator exponential of the same endomorphism.

**Definition 1.3 (claim).**

$$\operatorname{claim} \Leftrightarrow \forall (\operatorname{d} : \mathbb{N}) , 0 < \operatorname{d} \to \forall \operatorname{L} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) , \operatorname{ConditionallyTwoPositive} \operatorname{L} \to ((\operatorname{LinearMap} . \operatorname{trace} \mathbb{C} (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) \operatorname{L})) . \operatorname{im} = 0 \land \operatorname{spectralBound} \operatorname{L}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

Page 11, arXiv:2506.02145v1: "Hence one may wonder whether all (generators of) completely positive maps, resp. 2-positive maps satisfy" tr(Φ) ≤ d min ℜ(σ(Φ)) + (d² − d) max ℜ(σ(Φ)) ? "With this, (10) becomes really a conjecture about the spectrum of arbitrary conditionally 2-positive maps." The encoding quantifies over every positive matrix dimension and every complex-linear endomorphism, uses the literal operator exponential, and takes the real extrema over the roots of its characteristic polynomial. It also asserts that the endomorphism trace is real.

**Theorem 1.4 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/vom-ende-chruscinski-kimura-muratore-ginanneschi-2025-conditional-two-positive-bound` (proved) by `D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"vom-ende-chruscinski-kimura-muratore-ginanneschi-2025-conditional-two-positive-bound","declaration_gid":"D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

Every conditionally 2-positive endomorphism satisfies (10). Adding epsilon times the trace-to-identity map produces a faithful Perron eigenmatrix. Congruence by its square root and division by the Perron eigenvalue give a unital map whose Hilbert–Schmidt adjoint is trace preserving. Theorem 1 transports through this similarity. Letting epsilon tend to zero gives the bound for every 2-positive map; applying it to exp(tL) and passing through the difference quotient at t = 0 gives the asserted bound for L, together with reality of its trace.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.ConditionallyTwoPositive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.expEnd`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ConditionalTwoPositiveSpectralBound.result`
- Dependency: [D5/S3/Quantum/QuantumChannels/FaithfulPerronRegularization](FaithfulPerronRegularization.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound](TracePreservingEigenvalueBound.md)
