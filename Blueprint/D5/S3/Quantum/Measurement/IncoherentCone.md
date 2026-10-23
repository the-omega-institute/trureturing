# IncoherentCone

## Abstract

Finite-dimensional spectral and overlap bounds for antidistinguishability.

**Theorem 1.1 (psd closed).**

$$\forall (\operatorname{n} : \mathbb{N}) , \operatorname{IsClosed} \{\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C} | (\operatorname{A}).\operatorname{PosSemidef}\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncoherentCone.psd_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The positive semidefinite matrices form a closed set.

**Theorem 1.2 (flatten inner).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , \forall (\operatorname{Z} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , \operatorname{inner} \mathbb{R} (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Matrix}.\operatorname{CartesianVariance}.\operatorname{vectorize} \operatorname{n} \operatorname{A}) (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Matrix}.\operatorname{CartesianVariance}.\operatorname{vectorize} \operatorname{n} \operatorname{Z}) = \operatorname{RHLinalg}.\operatorname{rtrace} ((\operatorname{A}).\operatorname{conjTranspose} \cdot \operatorname{Z})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncoherentCone.flatten_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The real inner product after vectorization equals the real trace pairing.

**Theorem 1.3 (trace hermitianPart).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{G} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , ((\operatorname{G}).\operatorname{IsHermitian}) \to \forall (\operatorname{Z} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , \operatorname{RHLinalg}.\operatorname{rtrace} (\operatorname{G} \cdot (\operatorname{selfAdjointPart} \mathbb{R} \operatorname{Z} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C})) = \operatorname{RHLinalg}.\operatorname{rtrace} (\operatorname{G} \cdot \operatorname{Z})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncoherentCone.trace_hermitianPart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The trace pairing with a Hermitian matrix depends only on the self-adjoint part of the other matrix.

**Theorem 1.4 (rankone trace).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{Y} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , \forall (\operatorname{x} : \operatorname{Fin} \operatorname{n} \to \mathbb{C}) , \operatorname{RHLinalg}.\operatorname{rtrace} (\operatorname{Matrix}.\operatorname{vecMulVec} (\operatorname{x}) (\operatorname{star} (\operatorname{x})) \cdot \operatorname{Y}) = \operatorname{RHLinalg}.\operatorname{hermForm} \operatorname{Y} \operatorname{x}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncoherentCone.rankone_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The trace pairing with an outer product equals the Hermitian quadratic form.

**Theorem 1.5 (psd entry bound of trace).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , ((\operatorname{A}).\operatorname{PosSemidef}) \to \forall (\operatorname{R} : \mathbb{R}) , (0 < \operatorname{R}) \to (\operatorname{RHLinalg}.\operatorname{rtrace} (\operatorname{A}) \leq \operatorname{R}) \to \forall (\operatorname{i} : \operatorname{Fin} \operatorname{n}) , \forall (\operatorname{j} : \operatorname{Fin} \operatorname{n}) , \Vert \operatorname{A} \operatorname{i} \operatorname{j} \Vert \leq \operatorname{R}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncoherentCone.psd_entry_bound_of_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

A positive semidefinite matrix with real trace at most a positive R has every entry of norm at most R.

**Theorem 1.6 (incoherent closed).**

$$\forall (n : \mathbb{N}) , IsClosed \{A : Matrix (Fin n) (Fin n) \mathbb{C} | IsIncoherent A\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncoherentCone.incoherent_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.7 (incoherent separation).**

$$\forall (n : \mathbb{N}) (A : Matrix (Fin n) (Fin n) \mathbb{C}) , (A . IsHermitian) \to (\neg IsIncoherent A) \to \exists Y : Matrix (Fin n) (Fin n) \mathbb{C} , LocallyPsd Y \land RHLinalg . rtrace (A \cdot Y) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncoherentCone.incoherent_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/IncoherentCone.flatten_inner`
- Truth anchor: `D5/S3/Quantum/Measurement/IncoherentCone.incoherent_closed`
- Truth anchor: `D5/S3/Quantum/Measurement/IncoherentCone.incoherent_separation`
- Truth anchor: `D5/S3/Quantum/Measurement/IncoherentCone.psd_closed`
- Truth anchor: `D5/S3/Quantum/Measurement/IncoherentCone.psd_entry_bound_of_trace`
- Truth anchor: `D5/S3/Quantum/Measurement/IncoherentCone.rankone_trace`
- Truth anchor: `D5/S3/Quantum/Measurement/IncoherentCone.trace_hermitianPart`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityGram](AntidistinguishabilityGram.md)
