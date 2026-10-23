# OverlapLowRankDistance

## Abstract

Finite-dimensional spectral and overlap bounds for antidistinguishability.

**Theorem 1.1 (A scalar lower bound for every eigenvalue).**

$$\forall I : Type, [Fintype\left(I\right)] [DecidableEq\left(I\right)], \forall A : Matrix\left(I, I, \mathbb{C}\right), \forall h : (A).IsHermitian, \forall a : \mathbb{R}, (A - a \cdot (1 : Matrix\left(I, I, \mathbb{C}\right))).PosSemidef \implies \forall i : I, a \leq (h).eigenvalues\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.eigenvalue_lower_of_psd_sub_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

For a Hermitian matrix A on an arbitrary finite index type, positive semidefiniteness of A minus a times the identity implies that every eigenvalue of A is at least a. Evaluate the quadratic form on a unit eigenvector. The index type may be empty, in which case the conclusion has no instances.

**Theorem 1.2 (cSq nonneg).**

$$\forall (n : \mathbb{N}) , (2 \leq n) \to 0 \leq cSq n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.cSq_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.3 (delta budget).**

$$\forall (n : \mathbb{N}) , (10 \leq n) \to ((n : \mathbb{R}) - 3) \cdot ((n : \mathbb{R}) \cdot ((n : \mathbb{R}) - 1)) \cdot delta n = ((n : \mathbb{R}) - 9) / 16$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.delta_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.4 (frobSq add le twice).**

$$\forall (n : \mathbb{N}) (A B : Matrix (Fin n) (Fin n) \mathbb{C}) , RHLinalg . frobSq (A + B) \leq 2 \cdot RHLinalg . frobSq A + 2 \cdot RHLinalg . frobSq B$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.frobSq_add_le_twice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.5 (delta pos).**

$$\forall (n : \mathbb{N}) , (10 \leq n) \to 0 < delta n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.delta_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.6 (cSq lt half).**

$$\forall (n : \mathbb{N}) , (2 \leq n) \to cSq n < 1 / 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.cSq_lt_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.7 (offDiag card).**

$$\forall (n : \mathbb{N}) , (((univ : Finset (Fin n)) . offDiag)) . card = n \cdot (n - 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.offDiag_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Definition 1.8 (equalOverlap).**

$$\forall (n : \mathbb{N}) (c : \mathbb{R}) , equalOverlap n c = (1 - c) \cdot (1 : Matrix (Fin n) (Fin n) \mathbb{C}) + c \cdot Matrix . of (Function . const (Fin n) (Function . const (Fin n) (1 : \mathbb{C})))$$

*Formalization.* `D5/S3/Quantum/Measurement/OverlapLowRankDistance.equalOverlap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete definition. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.9 (low rank distance lower).**

$$\forall (\iota : Type) [Fintype \iota] [DecidableEq \iota] \{A B : Matrix \iota \iota \mathbb{C}\} (hA : A . IsHermitian) , (B . IsHermitian) \to \forall (a : \mathbb{R}) , (0 \leq a) \to (\forall (i : \iota) , a \leq hA . eigenvalues i) \to \forall (r : \mathbb{N}) , (B . rank \leq r) \to ((Fintype . card \iota : \mathbb{R}) - r) \cdot a^{2} \leq RHLinalg . frobSq (A - B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.low_rank_distance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.10 (delta overlap budget).**

$$\forall (n : \mathbb{N}) , (10 \leq n) \to (2 \cdot ((n : \mathbb{R}) \cdot ((n : \mathbb{R}) - 1)) \cdot delta n)^{2} \leq ((n : \mathbb{R}) - 9) / 64$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.delta_overlap_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.11 (quantitative rank contradiction).**

$$\forall (n : \mathbb{N}) , (10 \leq n) \to \forall (dist2 : \mathbb{R}) , (dist2 \leq 2 \cdot (((n : \mathbb{R}) - 9) / 16) + 2 \cdot (((n : \mathbb{R}) - 9) / 64)) \to (((n : \mathbb{R}) - 9) \cdot (1 - cSq n)^{2} \leq dist2) \to False$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.quantitative_rank_contradiction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.12 (overlap excess identity).**

$$\forall (n : \mathbb{N}) , (2 \leq n) \to \forall (G : Matrix (Fin n) (Fin n) \mathbb{C}) , (\forall (i : Fin n) , G i i = 1) \to (\sum p \in ((univ : Finset (Fin n)) . offDiag) , (\Vert G p . 1 p . 2 \Vert^{2} - cSq n)) = RHLinalg . frobSq G - (n : \mathbb{R})^{2} / 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.overlap_excess_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.13 (equalOverlap low rank distance).**

$$\forall (n r : \mathbb{N}) (c : \mathbb{R}) , (0 \leq c) \to (c \leq 1) \to \forall (B : Matrix (Fin n) (Fin n) \mathbb{C}) , (B . IsHermitian) \to (B . rank \leq r) \to ((n : \mathbb{R}) - r) \cdot (1 - c)^{2} \leq RHLinalg . frobSq (equalOverlap n c - B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.equalOverlap_low_rank_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.14 (overlap target distance bound).**

$$\forall (n : \mathbb{N}) , (2 \leq n) \to \forall (G : Matrix (Fin n) (Fin n) \mathbb{C}) , (\forall (i : Fin n) , G i i = 1) \to \forall (e : \mathbb{R}) , (0 \leq e) \to (\forall (i j : Fin n) , i \neq j \to \Vert G i j \Vert^{2} \leq cSq n + e) \to (0 \leq RHLinalg . frobSq G - (n : \mathbb{R})^{2} / 2) \to RHLinalg . frobSq ((RHLinalg . normSqMatrix G) . map (algebraMap \mathbb{R} \mathbb{C}) - equalOverlap n (cSq n)) \leq (2 \cdot ((n : \mathbb{R}) \cdot ((n : \mathbb{R}) - 1)) \cdot e)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OverlapLowRankDistance.overlap_target_distance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.cSq_lt_half`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.cSq_nonneg`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.delta_budget`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.delta_overlap_budget`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.delta_pos`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.eigenvalue_lower_of_psd_sub_scalar`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.equalOverlap`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.equalOverlap_low_rank_distance`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.frobSq_add_le_twice`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.low_rank_distance_lower`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.offDiag_card`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.overlap_excess_identity`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.overlap_target_distance_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/OverlapLowRankDistance.quantitative_rank_contradiction`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityGram](AntidistinguishabilityGram.md)
