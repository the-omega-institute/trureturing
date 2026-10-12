# OverlapSpectralTruncation

## Abstract

Finite-dimensional spectral and overlap bounds for antidistinguishability.

**Definition 1.1 (indexSpectral).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . IsHermitian) (v : Fin n \to \mathbb{R}) , indexSpectral hA v = conjStarAlgAut \mathbb{C} (Matrix (Fin n) (Fin n) \mathbb{C}) hA . eigenvectorUnitary (diagonal (fun (j : Fin n) \mapsto (v j : \mathbb{C})))$$

*Formalization.* `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.indexSpectral` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete definition. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Definition 1.2 (topThree).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . IsHermitian) , topThree hA = indexSpectral hA (fun (j : Fin n) \mapsto if ((((finCongr (n = Fintype . card (Fin n))) . trans RHLinalg . eigEquiv)) . symm j) . val < 3 then hA . eigenvalues j else 0)$$

*Formalization.* `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete definition. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.3 (topThree psd).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . PosSemidef) , (topThree hA . isHermitian) . PosSemidef$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.4 (norm square frob distance le).**

$$\forall (n : \mathbb{N}) (A B : Matrix (Fin n) (Fin n) \mathbb{C}) , (\forall (i j : Fin n) , \Vert A i j \Vert \leq 1) \to (\forall (i j : Fin n) , \Vert B i j \Vert \leq 1) \to RHLinalg . frobSq ((RHLinalg . normSqMatrix A) . map (algebraMap \mathbb{R} \mathbb{C}) - (RHLinalg . normSqMatrix B) . map (algebraMap \mathbb{R} \mathbb{C})) \leq 4 \cdot RHLinalg . frobSq (A - B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.norm_square_frob_distance_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.5 (topThree diag le).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . PosSemidef) , (\forall (i : Fin n) , A i i = 1) \to \forall (i : Fin n) , (topThree hA . isHermitian i i) . re \leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_diag_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.6 (topThree square psd).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . PosSemidef) , (3 \leq n) \to ((RHLinalg . normSqMatrix (topThree hA . isHermitian)) . map (algebraMap \mathbb{R} \mathbb{C})) . PosSemidef$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_square_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.7 (spectral failure fourth bound).**

$$\forall (n : \mathbb{N}) , (4 \leq n) \to \forall (lam : Fin n \to \mathbb{R}) , (\forall (k : Fin n) , 0 \leq lam k) \to (Antitone lam) \to ((\sum k \in univ . erase (\langle 0\rangle : Fin n) , Real . sqrt (lam k)) < Real . sqrt (lam \langle 0\rangle)) \to 12 \cdot (lam \langle 3\rangle)^{2} \leq (\sum k , (lam k)^{2}) - (\sum k , lam k)^{2} / 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.spectral_failure_fourth_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.8 (topThree square rank).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . PosSemidef) , (3 \leq n) \to ((RHLinalg . normSqMatrix (topThree hA . isHermitian)) . map (algebraMap \mathbb{R} \mathbb{C})) . rank \leq 9$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_square_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.9 (topThree failure distance).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . PosSemidef) , (4 \leq n) \to ((\sum k \in univ . erase (\langle 0\rangle : Fin n) , Real . sqrt ((fun k : Fin n \mapsto hA . isHermitian . eigenvalues (((finCongr (n = Fintype . card (Fin n))) . trans RHLinalg . eigEquiv) k)) k)) < Real . sqrt ((fun k : Fin n \mapsto hA . isHermitian . eigenvalues (((finCongr (n = Fintype . card (Fin n))) . trans RHLinalg . eigEquiv) k)) \langle 0\rangle)) \to RHLinalg . frobSq (A - topThree hA . isHermitian) \leq ((n : \mathbb{R}) - 3) \cdot (RHLinalg . frobSq A - (RHLinalg . rtrace A)^{2} / 2) / 4$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_failure_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.indexSpectral`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.norm_square_frob_distance_le`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.spectral_failure_fourth_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_diag_le`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_failure_distance`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_psd`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_square_psd`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapSpectralTruncation.topThree_square_rank`
- Dependency: [D5/S3/Quantum/Matrix/CommutatorGap](../Matrix/CommutatorGap.md)
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityGram](AntidistinguishabilityGram.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound](../TensorNetworks/BridgeGraph/QuantumMaxFlowBound.md)
