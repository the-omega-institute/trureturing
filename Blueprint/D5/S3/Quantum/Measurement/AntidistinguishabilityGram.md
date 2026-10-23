# AntidistinguishabilityGram

## Abstract

Finite-dimensional spectral and overlap bounds for antidistinguishability.

**Definition 1.1 (IsAntidistinguishable).**

$$\forall \{n d : \mathbb{N}\} (\psi : Fin n \to EuclideanSpace \mathbb{C} (Fin d)) , IsAntidistinguishable\left(\psi\right) = (\exists (M : Fin n \to Matrix (Fin d) (Fin d) \mathbb{C}) , (\forall (i : Fin n) , (M\left(i\right)).\operatorname{PosSemidef}) \land (((\sum i , M\left(i\right)) = 1) \land (\forall (i : Fin n) , star (\psi i : Fin d \to \mathbb{C}) \cdot_{v} (M\left(i\right) \times_{v} (\psi i : Fin d \to \mathbb{C})) = 0)))$$

*Formalization.* `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.IsAntidistinguishable` (`✓ std3`).

*Citation.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

Section 2.1, page 3: “The set of states is antidistinguishable if there exists a POVM such that ⟨ψi|Mi|ψi⟩ = 0 for all 0 ≤ i ≤ n − 1.” Fin n indexes the measurement effects, and Fin d indexes the finite-dimensional state space.

**Definition 1.2 (cSq).**

$$\forall (n : \mathbb{N}) , cSq n = ((n : \mathbb{R}) - 2) / (2 \cdot ((n : \mathbb{R}) - 1))$$

*Formalization.* `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.cSq` (`✓ std3`).

*Citation.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

Corollary 5.4, page 15: “Let n ≥ 2 be an integer and let S = {|ψ₀⟩, |ψ₁⟩, . . . , |ψₙ₋₁⟩}. If” the displayed source overlap bound holds, “then S is antidistinguishable.” The formula is the square of that source cap, with subtraction and division in ℝ.

**Definition 1.3 (delta).**

$$\forall (n : \mathbb{N}) , delta n = ((n : \mathbb{R}) - 9) / (16 \cdot (n : \mathbb{R}) \cdot ((n : \mathbb{R}) - 1) \cdot ((n : \mathbb{R}) - 3))$$

*Formalization.* `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete definition. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Definition 1.4 (IsIncoherent).**

$$\forall (n : \mathbb{N}) , \forall (G : Matrix (Fin n) (Fin n) \mathbb{C}) , IsIncoherent\left(G\right) = (\exists (F : Fin n \to Matrix (Fin n) (Fin n) \mathbb{C}) , (\forall (i : Fin n) , (F\left(i\right)).\operatorname{PosSemidef}) \land (((\sum i : Fin n , F\left(i\right)) = G) \land (\forall (i : Fin n) , F\left(i, i, i\right) = 0)))$$

*Formalization.* `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.IsIncoherent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The displayed predicate is the matrix-effect certificate used here: one positive semidefinite summand for each coordinate, with zero on that coordinate’s diagonal. This certificate is consumed by the Gram-to-POVM construction.

**Definition 1.5 (LocallyPsd).**

$$\forall (n : \mathbb{N}) , \forall (Y : Matrix (Fin n) (Fin n) \mathbb{C}) , LocallyPsd\left(Y\right) = (((Y).\operatorname{IsHermitian}) \land (\forall (j : Fin n) , \forall (x : Fin n \to \mathbb{C}) , (x\left(j\right) = 0) \to (0 \leq RHLinalg . hermForm Y x)))$$

*Formalization.* `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.LocallyPsd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The displayed predicate bounds the Hermitian quadratic form on each coordinate hyperplane. It organizes the dual-cone argument.

**Theorem 1.6 (orderedSpectrum antitone).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . IsHermitian) , Antitone ((fun k : Fin n \mapsto hA . eigenvalues (((finCongr (n = Fintype . card (Fin n))) . trans RHLinalg . eigEquiv) k)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.orderedSpectrum_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.7 (orderedSpectrum nonneg).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . PosSemidef) , \forall (k : Fin n) , 0 \leq (fun k : Fin n \mapsto hA . isHermitian . eigenvalues (((finCongr (n = Fintype . card (Fin n))) . trans RHLinalg . eigEquiv) k)) k$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.orderedSpectrum_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.8 (sum orderedSpectrum).**

$$\forall (n : \mathbb{N}) \{A : Matrix (Fin n) (Fin n) \mathbb{C}\} (hA : A . IsHermitian) (f : \mathbb{R} \to \mathbb{R}) , (\sum k , f ((fun k : Fin n \mapsto hA . eigenvalues (((finCongr (n = Fintype . card (Fin n))) . trans RHLinalg . eigEquiv) k)) k)) = \sum j , f (hA . eigenvalues j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.sum_orderedSpectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.9 (gramPsd).**

$$\forall (n d : \mathbb{N}) (\psi : Fin n \to EuclideanSpace \mathbb{C} (Fin d)) , ((Matrix . gram \mathbb{C} \psi)) . PosSemidef$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.gramPsd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.10 (Positive complementary projection).**

$$\forall (d : \mathbb{N}) , \forall (P : Matrix (Fin d) (Fin d) \mathbb{C}) , ((P).\operatorname{IsHermitian}) \to ((P \cdot P = P) \to ((1 - P).\operatorname{PosSemidef}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.hermitian_projection_complement_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The complement of a Hermitian idempotent is positive semidefinite.

**Theorem 1.11 (Matrix Penrose inverse).**

$$\forall (n : \mathbb{N}) , \forall (d : \mathbb{N}) , \forall (A : Matrix (Fin d) (Fin n) \mathbb{C}) , \exists (B : Matrix (Fin n) (Fin d) \mathbb{C}) , (A \cdot B \cdot A = A) \land ((B \cdot A \cdot B = B) \land (((A \cdot B).\operatorname{IsHermitian}) \land ((B \cdot A).\operatorname{IsHermitian})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.matrix_penrose_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

Every rectangular complex matrix admits a Penrose inverse: both absorption identities hold and both products are Hermitian. The construction transports the finite-dimensional Moore–Penrose inverse through Matrix.toEuclideanLin.

**Theorem 1.12 (Kernels of positive summands).**

$$\forall (n : \mathbb{N}) , \forall (F : Fin n \to Matrix (Fin n) (Fin n) \mathbb{C}) , (\forall (j : Fin n) , (F\left(j\right)).\operatorname{PosSemidef}) \to (\forall (x : Fin n \to \mathbb{C}) , ((\sum i : Fin n , F\left(i\right)) \times_{v} x = 0) \to (\forall (i : Fin n) , F\left(i\right) \times_{v} x = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.psd_summand_kills_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

If a vector belongs to the kernel of a finite sum of positive semidefinite matrices, it belongs to the kernel of every summand.

**Theorem 1.13 (Projection of positive summands).**

$$\forall (n : \mathbb{N}) , \forall (F : Fin n \to Matrix (Fin n) (Fin n) \mathbb{C}) , (\forall (i : Fin n) , (F\left(i\right)).\operatorname{PosSemidef}) \to (\forall (Q : Matrix (Fin n) (Fin n) \mathbb{C}) , ((Q).\operatorname{IsHermitian}) \to (((\sum i : Fin n , F\left(i\right)) \cdot Q = \sum i : Fin n , F\left(i\right)) \to (\forall (i : Fin n) , Q \cdot F\left(i\right) \cdot Q = F\left(i\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.psd_summand_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

A Hermitian matrix that fixes the sum of positive semidefinite matrices fixes each summand on both sides.

**Theorem 1.14 (stateGram diag).**

$$\forall (n : \mathbb{N}) , \forall (d : \mathbb{N}) , \forall (\psi : Fin n \to EuclideanSpace \mathbb{C} (Fin d)) , (\forall (i : Fin n) , \Vert \psi\left(i\right) \Vert = 1) \to (\forall (i : Fin n) , (Matrix . gram \mathbb{C} \psi)\left(i, i\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.stateGram_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted.

**Theorem 1.15 (incoherent gram antidistinguishable).**

$$\forall (n : \mathbb{N}) , \forall (d : \mathbb{N}) , (1 \leq n) \to (\forall (\psi : Fin n \to EuclideanSpace \mathbb{C} (Fin d)) , (IsIncoherent\left((Matrix . gram \mathbb{C} \psi)\right)) \to (IsAntidistinguishable\left(\psi\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.incoherent_gram_antidistinguishable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, Vincent Russo, Jamie Sikora (2025). *Tight bounds for antidistinguishability and circulant sets of pure quantum states*. DOI: [10.22331/q-2025-02-04-1622](https://doi.org/10.22331/q-2025-02-04-1622). URL: <https://arxiv.org/abs/2311.17047v2>.

*Commentary.*

A Gram certificate yields positive measurement effects through a finite Penrose inverse and a positive complementary projection. This implication applies to arbitrary finite vector families; normalization is not needed.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.IsAntidistinguishable`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.IsIncoherent`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.LocallyPsd`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.cSq`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.delta`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.gramPsd`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.hermitian_projection_complement_psd`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.incoherent_gram_antidistinguishable`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.matrix_penrose_exists`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.orderedSpectrum_antitone`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.orderedSpectrum_nonneg`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.psd_summand_kills_kernel`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.psd_summand_projection`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.stateGram_diag`
- Truth anchor: `D5/S3/Quantum/Measurement/AntidistinguishabilityGram.sum_orderedSpectrum`
- Dependency: [D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse](../../Observer/Hilbert/FiniteMoorePenroseInverse.md)
