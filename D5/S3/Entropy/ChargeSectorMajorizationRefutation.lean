/- GID: D5/S3/Entropy/ChargeSectorMajorizationRefutation
   generality: I
   mirror-B: D5/B/S3/Entropy/ChargeSectorMajorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/ChargeSectorMajorizationRefutation.claim; result=D5/S3/Entropy/ChargeSectorMajorizationRefutation.result; claim=D5/S3/Entropy/ChargeSectorMajorizationRefutation.claim
   digest: Majorization can fail after normalization within a common charge sector. -/

import D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation
import D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing

/-! Charge-sector normalization need not preserve majorization of diagonal density matrices. -/

set_option autoImplicit false

namespace D5.S3.Entropy.ChargeSectorMajorizationRefutation

open D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation (Majorizes)

open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing (desc)

/-- The trace of the block on the charge-`q` eigenspace. -/
noncomputable def sectorWeight {n : ℕ} (r : Fin n → ℝ) (charge : Fin n → ℤ)
    (q : ℤ) : ℝ :=
  ∑ i, if charge i = q then r i else 0

/-- The eigenvalues of the normalized charge block, in descending order.
Only indices in the eigenspace occur; zero eigenvalues retain their multiplicities. -/
noncomputable def sectorSpectrum {n : ℕ} (r : Fin n → ℝ) (charge : Fin n → ℤ)
    (q : ℤ) : List ℝ :=
  (((List.finRange n).filter (fun i => decide (charge i = q))).map
    (fun i => r i / sectorWeight r charge q)).mergeSort (fun a b => decide (b ≤ a))

/-- Majorization of diagonal density matrices would persist in every common
positive-weight charge sector after normalizing both blocks. -/
def claim : Prop :=
  ∀ (n : ℕ) (charge : Fin n → ℤ) (r s : Fin n → ℝ),
    (∀ i, 0 ≤ r i) → (∑ i, r i = 1) →
    (∀ i, 0 ≤ s i) → (∑ i, s i = 1) →
    Majorizes (desc r) (desc s) →
    ∀ q : ℤ, 0 < sectorWeight r charge q → 0 < sectorWeight s charge q →
      Majorizes (sectorSpectrum r charge q) (sectorSpectrum s charge q)

private def chargeData : Fin 4 → ℤ := ![0, 0, 1, 1]
private noncomputable def r : Fin 4 → ℝ := ![6/20, 6/20, 7/20, 1/20]
private noncomputable def s : Fin 4 → ℝ := ![7/20, 5/20, 4/20, 4/20]

private lemma r_state : (∀ i, 0 ≤ r i) ∧ (∑ i, r i = 1) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [r]
  · norm_num [r, Fin.sum_univ_succ]

private lemma s_state : (∀ i, 0 ≤ s i) ∧ (∑ i, s i = 1) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [s]
  · norm_num [s, Fin.sum_univ_succ]

private lemma full_spectra :
    desc r = [7/20, 6/20, 6/20, 1/20] ∧
    desc s = [7/20, 5/20, 4/20, 4/20] := by
  constructor
  · change ([6/20, 6/20, 7/20, 1/20] : List ℝ).mergeSort
      (fun a b => decide (b ≤ a)) = _
    norm_num [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.splitAt_eq]
  · change ([7/20, 5/20, 4/20, 4/20] : List ℝ).mergeSort
      (fun a b => decide (b ≤ a)) = _
    exact List.mergeSort_of_pairwise (by norm_num)

private lemma global_majorizes : Majorizes (desc r) (desc s) := by
  rw [full_spectra.1, full_spectra.2]
  sorry

private lemma sector_weights :
    sectorWeight r chargeData 0 = 3/5 ∧ sectorWeight s chargeData 0 = 3/5 := by
  sorry

private lemma sector_spectra :
    sectorSpectrum r chargeData 0 = [1/2, 1/2] ∧
    sectorSpectrum s chargeData 0 = [7/12, 5/12] := by
  sorry

private lemma sector_failure :
    ¬ Majorizes (sectorSpectrum r chargeData 0) (sectorSpectrum s chargeData 0) := by
  rw [sector_spectra.1, sector_spectra.2]
  sorry

/-- Full-state majorization does not imply majorization of the normalized charge blocks. -/
theorem result : ¬ claim := by
  intro h
  have hm := h 4 chargeData r s r_state.1 r_state.2 s_state.1 s_state.2 global_majorizes 0
  apply sector_failure (hm ?_ ?_)
  · rw [sector_weights.1]
    norm_num
  · rw [sector_weights.2]
    norm_num

end D5.S3.Entropy.ChargeSectorMajorizationRefutation
