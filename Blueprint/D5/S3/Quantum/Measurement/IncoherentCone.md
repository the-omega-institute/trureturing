# IncoherentCone

## Abstract

Finite-dimensional spectral and overlap bounds for antidistinguishability.

**Theorem 1.1 (incoherent closed).**

$$\forall (n : \mathbb{N}) , IsClosed \{A : Matrix (Fin n) (Fin n) \mathbb{C} | IsIncoherent A\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncoherentCone.incoherent_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.2 (incoherent separation).**

$$\forall (n : \mathbb{N}) (A : Matrix (Fin n) (Fin n) \mathbb{C}) , (A . IsHermitian) \to (\neg IsIncoherent A) \to \exists Y : Matrix (Fin n) (Fin n) \mathbb{C} , LocallyPsd Y \land RHLinalg . rtrace (A \cdot Y) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncoherentCone.incoherent_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/IncoherentCone.incoherent_closed`
- Truth anchor: `D5/S3/Quantum/Measurement/IncoherentCone.incoherent_separation`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityGram](AntidistinguishabilityGram.md)
