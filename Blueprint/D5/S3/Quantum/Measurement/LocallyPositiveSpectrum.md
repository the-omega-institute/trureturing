# LocallyPositiveSpectrum

## Abstract

Finite-dimensional spectral and overlap bounds for antidistinguishability.

**Theorem 1.1 (local psd negIndex).**

$$\forall (n : \mathbb{N}) , (1 \leq n) \to \forall (Y : Matrix (Fin n) (Fin n) \mathbb{C}) (hY : LocallyPsd Y) , RHLinalg . negIndex hY . 1 \leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/LocallyPositiveSpectrum.local_psd_negIndex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.2 (local psd kernel eq zero).**

$$\forall (n : \mathbb{N}) (Y : Matrix (Fin n) (Fin n) \mathbb{C}) , (LocallyPsd Y) \to \forall (v : Fin n \to \mathbb{C}) , (RHLinalg . hermForm Y v < 0) \to \forall (x : Fin n \to \mathbb{C}) , (Y \times_{v} x = 0) \to x = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/LocallyPositiveSpectrum.local_psd_kernel_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.3 (local psd reciprocal budget).**

$$\forall (n : \mathbb{N}) (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) \mathbb{C}) (hY : LocallyPsd Y) (p : Fin (n + 1)) , (hY . 1 . eigenvalues p < 0) \to (\forall (i : Fin (n + 1)) , i \neq p \to 0 < hY . 1 . eigenvalues i) \land (\sum i \in univ . erase p , (hY . 1 . eigenvalues i)^{-1}) \leq (- hY . 1 . eigenvalues p)^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/LocallyPositiveSpectrum.local_psd_reciprocal_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/LocallyPositiveSpectrum.local_psd_kernel_eq_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/LocallyPositiveSpectrum.local_psd_negIndex`
- Truth anchor: `D5/S3/Quantum/Measurement/LocallyPositiveSpectrum.local_psd_reciprocal_budget`
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityGram](AntidistinguishabilityGram.md)
- Dependency: [D5/S3/Weil/ZetaLinear/PoleCapacityRankOne](../../Weil/ZetaLinear/PoleCapacityRankOne.md)
