# TwoPositiveTransitionTrace

## Abstract

TwoPositiveTransitionTrace for the spectral bound of conditionally two-positive maps.

**Definition 1.1 (minReSpectrum).**

$$\forall (\operatorname{d} : \mathbb{N}) (\operatorname{L} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{minReSpectrum} \operatorname{L} = \operatorname{sInf} (\operatorname{Set} . \operatorname{image} \operatorname{Complex} . \operatorname{re} (\{\operatorname{z} : \mathbb{C} | \operatorname{z} \in \operatorname{L} . \operatorname{charpoly} . \operatorname{roots}\}))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.minReSpectrum` (`✓ std3`).

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for minReSpectrum. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Definition 1.2 (maxReSpectrum).**

$$\forall (\operatorname{d} : \mathbb{N}) (\operatorname{L} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{maxReSpectrum} \operatorname{L} = \operatorname{sSup} (\operatorname{Set} . \operatorname{image} \operatorname{Complex} . \operatorname{re} (\{\operatorname{z} : \mathbb{C} | \operatorname{z} \in \operatorname{L} . \operatorname{charpoly} . \operatorname{roots}\}))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.maxReSpectrum` (`✓ std3`).

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for maxReSpectrum. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Definition 1.3 (spectralBound).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{L} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{spectralBound} \operatorname{L} \Leftrightarrow ((\operatorname{LinearMap} . \operatorname{trace} \mathbb{C} (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) \operatorname{L})) . \operatorname{re} \leq (\operatorname{d} : \mathbb{R}) * \operatorname{minReSpectrum} \operatorname{L} + ((\operatorname{d} : \mathbb{R})^{2} - \operatorname{d}) * \operatorname{maxReSpectrum} \operatorname{L}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.spectralBound` (`✓ std3`).

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for spectralBound. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.4 (pair extraction).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \phi)) \to \forall (\operatorname{j} \operatorname{k} : \operatorname{Fin} \operatorname{d}) , (\phi (\operatorname{Matrix} . \operatorname{single} \operatorname{k} \operatorname{j} 1) \operatorname{k} \operatorname{j}) . \operatorname{re} + (\phi (\operatorname{Matrix} . \operatorname{single} \operatorname{j} \operatorname{k} 1) \operatorname{j} \operatorname{k}) . \operatorname{re} \leq (\phi (\operatorname{Matrix} . \operatorname{single} \operatorname{k} \operatorname{k} 1) \operatorname{k} \operatorname{k}) . \operatorname{re} + (\phi (\operatorname{Matrix} . \operatorname{single} \operatorname{j} \operatorname{j} 1) \operatorname{j} \operatorname{j}) . \operatorname{re}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.pair_extraction` (`✓ std3`). ∎

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The pair estimate in the proof of Lemma 1, page 7, arXiv:2506.02145v1. Testing the amplified map on the entangled rank-one matrix formed from two matrix units and using the opposite-sign vector bounds the two crossed diagonal coefficients by the two uncrossed coefficients.

**Theorem 1.5 (transition trace bound).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \phi)) \to (\operatorname{LinearMap} . \operatorname{trace} \mathbb{C} ((\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) \phi) . \operatorname{re} \leq (\operatorname{d} : \mathbb{R}) * \sum \operatorname{i} : \operatorname{Fin} \operatorname{d} , (\phi (\operatorname{Matrix} . \operatorname{single} \operatorname{i} \operatorname{i} 1) \operatorname{i} \operatorname{i}) . \operatorname{re}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.transition_trace_bound` (`✓ std3`). ∎

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

Lemma 1, page 6, arXiv:2506.02145v1, equation (8), specialized to the standard orthonormal basis. Summing the pair estimates over every ordered pair yields the dimension-wide superoperator trace estimate. LinearMap.trace is the trace on the matrix space, rather than Matrix.trace of an output matrix.

**Theorem 1.6 (twoPositive star preserving).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \phi)) \to \forall (\operatorname{Y} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \phi \operatorname{Y} . \operatorname{conjTranspose} = (\phi \operatorname{Y}) . \operatorname{conjTranspose}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_star_preserving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for twoPositive_star_preserving. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.7 (twoPositive add).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\phi \psi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \phi)) \to ((\operatorname{KPositive} 2 \operatorname{d} \psi)) \to (\operatorname{KPositive} 2 \operatorname{d} (\phi + \psi))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for twoPositive_add. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.8 (twoPositive smul).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \phi)) \to \forall (\operatorname{c} : \mathbb{R}) , (0 \leq \operatorname{c}) \to (\operatorname{KPositive} 2 \operatorname{d} ((\operatorname{c} : \mathbb{C}) \cdot \phi))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for twoPositive_smul. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.9 (traceIdentity twoPositive).**

$$\forall (\operatorname{d} : \mathbb{N}) , (\operatorname{KPositive} 2 \operatorname{d} (((\operatorname{Matrix} . \operatorname{traceLinearMap} (\operatorname{Fin} \operatorname{d}) \mathbb{C} \mathbb{C}) . \operatorname{smulRight} (1 : \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.traceIdentity_twoPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for traceIdentity_twoPositive. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.10 (regularization twoPositive).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{T} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \operatorname{T})) \to \forall (\varepsilon : \mathbb{R}) , (0 \leq \varepsilon) \to (\operatorname{KPositive} 2 \operatorname{d} (\operatorname{T} + (\varepsilon : \mathbb{C}) \cdot ((\operatorname{Matrix} . \operatorname{traceLinearMap} (\operatorname{Fin} \operatorname{d}) \mathbb{C} \mathbb{C}) . \operatorname{smulRight} (1 : \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.regularization_twoPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for regularization_twoPositive. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.11 (twoPositive positive).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{T} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \operatorname{T})) \to \forall (\operatorname{X} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , (\operatorname{X} . \operatorname{PosSemidef}) \to (\operatorname{T} \operatorname{X}) . \operatorname{PosSemidef}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for twoPositive_positive. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.12 (regularization strictly improving).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{T} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \operatorname{T})) \to \forall (\varepsilon : \mathbb{R}) , (0 < \varepsilon) \to \forall (\operatorname{X} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , (\operatorname{X} . \operatorname{PosSemidef}) \to (\operatorname{X} \neq 0) \to (((\operatorname{T} + (\varepsilon : \mathbb{C}) \cdot ((\operatorname{Matrix} . \operatorname{traceLinearMap} (\operatorname{Fin} \operatorname{d}) \mathbb{C} \mathbb{C}) . \operatorname{smulRight} (1 : \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}))) : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) \operatorname{X}) . \operatorname{PosDef}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.regularization_strictly_improving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for regularization_strictly_improving. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.13 (positive diag of two).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \phi)) \to \forall (\operatorname{i} \operatorname{j} : \operatorname{Fin} \operatorname{d}) , 0 \leq (\phi (\operatorname{Matrix} . \operatorname{single} \operatorname{j} \operatorname{j} 1) \operatorname{i} \operatorname{i}) . \operatorname{re}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.positive_diag_of_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for positive_diag_of_two. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Definition 1.14 (transition).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{transition} \phi = \lambda \operatorname{i} \operatorname{j} \mapsto (\phi (\operatorname{Matrix} . \operatorname{single} \operatorname{j} \operatorname{j} 1) \operatorname{i} \operatorname{i})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.transition` (`✓ std3`).

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

Page 6, arXiv:2506.02145v1: "given Φ ∈ L(Cd×d) and any orthonormal basis G := {gj}dj=1 of Cd define TG(Φ) ∈ Cd×d (or TG, for short) via (TG)jk := ⟨gj|Φ(|gk⟩⟨gk|)|gj⟩." In the standard basis the entry is Phi (Matrix.single j j 1) i i, with its full complex value. Fin d indexes all d basis vectors.

**Theorem 1.15 (transition colStochastic).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{NeZero} \operatorname{d}] , \forall (\phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , (\forall \operatorname{i} \operatorname{j} : \operatorname{Fin} \operatorname{d} , 0 \leq (\phi (\operatorname{Matrix} . \operatorname{single} \operatorname{j} \operatorname{j} 1) \operatorname{i} \operatorname{i}) . \operatorname{re}) \to ((\forall \operatorname{X} , \operatorname{Matrix} . \operatorname{trace} (\phi \operatorname{X}) = \operatorname{Matrix} . \operatorname{trace} \operatorname{X})) \to (\operatorname{transition} \phi).\operatorname{map} \operatorname{Complex}.\operatorname{re} \in \operatorname{Matrix} . \operatorname{colStochastic} \mathbb{R} (\operatorname{Fin} \operatorname{d})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.transition_colStochastic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for transition_colStochastic. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Definition 1.16 (hsInner).**

$$\forall (\operatorname{d} : \mathbb{N}) , \operatorname{hsInner} . \operatorname{toNormedSpace} = \operatorname{Matrix} . \operatorname{frobeniusNormedSpace} \land \forall (\operatorname{X} \operatorname{Y} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) , \operatorname{hsInner} . \operatorname{inner} \operatorname{X} \operatorname{Y} = (\operatorname{X} . \operatorname{conjTranspose} * \operatorname{Y}) . \operatorname{trace}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.hsInner` (`✓ std3`).

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The Hilbert–Schmidt structure uses the Frobenius norm already supplied by Mathlib. Its inner product is exactly the trace of conjTranspose X times Y; the normed-space field is Matrix.frobeniusNormedSpace. The equality specifies the data fields; the remaining structure fields certify the inner-product laws.

**Definition 1.17 (weightedAdjoint).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{hsInner}] , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \forall (\operatorname{W} \operatorname{V} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{weightedAdjoint} \operatorname{Phi} \operatorname{W} \operatorname{V} = ((\operatorname{LinearMap} . \operatorname{mulLeftRight} \mathbb{C} (\operatorname{W} , \operatorname{W} . \operatorname{conjTranspose}))) . \operatorname{comp} ((\operatorname{LinearMap} . \operatorname{adjoint} \operatorname{Phi}) . \operatorname{comp} ((\operatorname{LinearMap} . \operatorname{mulLeftRight} \mathbb{C} (\operatorname{V} , \operatorname{V} . \operatorname{conjTranspose}))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.weightedAdjoint` (`✓ std3`).

*Citation.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for weightedAdjoint. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.18 (hsAdjoint inner left).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{hsInner}] , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \forall (\operatorname{X} \operatorname{Y} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{inner} \mathbb{C} (\operatorname{LinearMap} . \operatorname{adjoint} \operatorname{Phi} \operatorname{Y}) \operatorname{X} = \operatorname{inner} \mathbb{C} \operatorname{Y} (\operatorname{Phi} \operatorname{X})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.hsAdjoint_inner_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for hsAdjoint_inner_left. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.19 (hsAdjoint entry).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{hsInner}] , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \forall (\operatorname{Y} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \forall (\operatorname{a} \operatorname{b} : \operatorname{Fin} \operatorname{d}) , \operatorname{LinearMap} . \operatorname{adjoint} \operatorname{Phi} \operatorname{Y} \operatorname{a} \operatorname{b} = \sum \operatorname{i} : \operatorname{Fin} \operatorname{d} , \sum \operatorname{j} : \operatorname{Fin} \operatorname{d} , \operatorname{star} (\operatorname{Phi} (\operatorname{Matrix} . \operatorname{single} \operatorname{a} \operatorname{b} 1) \operatorname{i} \operatorname{j}) * \operatorname{Y} \operatorname{i} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.hsAdjoint_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for hsAdjoint_entry. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.20 (unital iff adjoint tracePreserving).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{hsInner}] , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \operatorname{Phi} 1 = 1 \Leftrightarrow (\forall \operatorname{X} , \operatorname{Matrix} . \operatorname{trace} ((\operatorname{LinearMap} . \operatorname{adjoint} \operatorname{Phi}) \operatorname{X}) = \operatorname{Matrix} . \operatorname{trace} \operatorname{X})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.unital_iff_adjoint_tracePreserving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for unital_iff_adjoint_tracePreserving. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.21 (adjoint twoPositive).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{hsInner}] , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \operatorname{Phi})) \to (\operatorname{KPositive} 2 \operatorname{d} (\operatorname{LinearMap} . \operatorname{adjoint} \operatorname{Phi}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.adjoint_twoPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for adjoint_twoPositive. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.22 (congrMap twoPositive).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{A} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , (\operatorname{KPositive} 2 \operatorname{d} ((\operatorname{LinearMap} . \operatorname{mulLeftRight} \mathbb{C} (\operatorname{A} , \operatorname{A} . \operatorname{conjTranspose}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.congrMap_twoPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for congrMap_twoPositive. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.23 (twoPositive comp).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{T} \operatorname{S} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \operatorname{T})) \to ((\operatorname{KPositive} 2 \operatorname{d} \operatorname{S})) \to (\operatorname{KPositive} 2 \operatorname{d} (\operatorname{T} . \operatorname{comp} \operatorname{S}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for twoPositive_comp. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.24 (superoperator trace real twoPositive).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\phi : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , ((\operatorname{KPositive} 2 \operatorname{d} \phi)) \to (\operatorname{LinearMap} . \operatorname{trace} \mathbb{C} ((\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) \phi) . \operatorname{im} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.superoperator_trace_real_twoPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for superoperator_trace_real_twoPositive. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.25 (faithful fixed eigenvalue norm le one).**

$$\forall (\operatorname{A} : \operatorname{Type} *) , [\operatorname{CStarAlgebra} \operatorname{A}] , [\operatorname{PartialOrder} \operatorname{A}] , [\operatorname{StarOrderedRing} \operatorname{A}] , [\operatorname{NonnegSpectrumClass} \mathbb{R} \operatorname{A}] , [\operatorname{Nontrivial} \operatorname{A}] , [\operatorname{NormOneClass} \operatorname{A}] , \forall (\operatorname{U} : (\operatorname{A} \to_{l[\mathbb{C}]} \operatorname{A})) , (\forall \operatorname{X} , 0 \leq \operatorname{X} \to 0 \leq \operatorname{U} \operatorname{X}) \to \forall (\rho : \operatorname{A}) , (\operatorname{IsStrictlyPositive} \rho) \to (\operatorname{U} \rho = \rho) \to \forall (\operatorname{z} : \mathbb{C}) , (\operatorname{Module} . \operatorname{End} . \operatorname{HasEigenvalue} \operatorname{U} \operatorname{z}) \to \Vert \operatorname{z} \Vert \leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.faithful_fixed_eigenvalue_norm_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

A strictly positive invariant element bounds the order unit from below. Positivity of every power then bounds its action uniformly on every eigenvector. An eigenvalue of modulus greater than one would contradict this bound through geometric growth.

**Theorem 1.26 (root mem iff).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \forall (\operatorname{z} : \mathbb{C}) , \operatorname{z} \in (\operatorname{Phi} . \operatorname{charpoly} . \operatorname{roots}) \Leftrightarrow \operatorname{Module} . \operatorname{End} . \operatorname{HasEigenvalue} \operatorname{Phi} \operatorname{z}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.root_mem_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for root_mem_iff. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.27 (roots finite).**

$$\forall (\operatorname{d} : \mathbb{N}) , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \{\operatorname{z} : \mathbb{C} | \operatorname{z} \in (\operatorname{Phi} . \operatorname{charpoly} . \operatorname{roots})\} . \operatorname{Finite}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.roots_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for roots_finite. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.28 (roots nonempty).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{NeZero} \operatorname{d}] , \forall (\operatorname{Phi} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{l[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \{\operatorname{z} : \mathbb{C} | \operatorname{z} \in (\operatorname{Phi} . \operatorname{charpoly} . \operatorname{roots})\} . \operatorname{Nonempty}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.roots_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for roots_nonempty. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.29 (extrema tendsto).**

$$\forall (\operatorname{d} : \mathbb{N}) , [\operatorname{NeZero} \operatorname{d}] , \forall (\alpha : \operatorname{Type} *) , \forall (\operatorname{l} : \operatorname{Filter} \alpha) , \forall (\operatorname{A} : \alpha \to (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{L[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , \forall (\operatorname{B} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{L[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C})) , (\operatorname{Tendsto} \operatorname{A} \operatorname{l} (\operatorname{nhds} \operatorname{B})) \to \operatorname{Tendsto} (\lambda \operatorname{x} \mapsto \operatorname{minReSpectrum} (\operatorname{A} \operatorname{x}) . \operatorname{toLinearMap}) \operatorname{l} (\operatorname{nhds} (\operatorname{minReSpectrum} \operatorname{B} . \operatorname{toLinearMap})) \land \operatorname{Tendsto} (\lambda \operatorname{x} \mapsto \operatorname{maxReSpectrum} (\operatorname{A} \operatorname{x}) . \operatorname{toLinearMap}) \operatorname{l} (\operatorname{nhds} (\operatorname{maxReSpectrum} \operatorname{B} . \operatorname{toLinearMap}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.extrema_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for extrema_tendsto. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

**Theorem 1.30 (superTrace continuous).**

$$\forall (\operatorname{d} : \mathbb{N}) , \operatorname{Continuous} (\lambda \operatorname{L} : (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C} \to_{L[\mathbb{C}]} \operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) \mapsto (\operatorname{LinearMap} . \operatorname{trace} \mathbb{C} (\operatorname{Matrix} (\operatorname{Fin} \operatorname{d}) (\operatorname{Fin} \operatorname{d}) \mathbb{C}) \operatorname{L} . \operatorname{toLinearMap}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.superTrace_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. vom Ende, D. Chruściński, G. Kimura, P. Muratore-Ginanneschi (2025). *Universal Bound on the Eigenvalues of 2-Positive Trace-Preserving Maps*. DOI: [10.1016/j.laa.2025.10.022](https://doi.org/10.1016/j.laa.2025.10.022). URL: <https://arxiv.org/abs/2506.02145v1>.

*Commentary.*

The displayed statement gives the hypotheses and conclusion for superTrace_continuous. Matrices are complex matrices of the displayed finite dimension; LinearMap.trace denotes the endomorphism trace. All sums over Fin d run over its full finite universe.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.adjoint_twoPositive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.congrMap_twoPositive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.extrema_tendsto`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.faithful_fixed_eigenvalue_norm_le_one`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.hsAdjoint_entry`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.hsAdjoint_inner_left`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.hsInner`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.maxReSpectrum`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.minReSpectrum`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.pair_extraction`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.positive_diag_of_two`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.regularization_strictly_improving`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.regularization_twoPositive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.root_mem_iff`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.roots_finite`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.roots_nonempty`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.spectralBound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.superTrace_continuous`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.superoperator_trace_real_twoPositive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.traceIdentity_twoPositive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.transition`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.transition_colStochastic`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.transition_trace_bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_add`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_comp`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_positive`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_smul`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.twoPositive_star_preserving`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.unital_iff_adjoint_tracePreserving`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.weightedAdjoint`
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](TomiyamaDiagonalKPositivity.md)
