/- GID: D5/S3/Entropy/ChargeSectorMajorizationRefutation
   generality: I
   mirror-B: D5/B/S3/Entropy/ChargeSectorMajorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/ChargeSectorMajorizationRefutation.claim; result=D5/S3/Entropy/ChargeSectorMajorizationRefutation.result; claim=D5/S3/Entropy/ChargeSectorMajorizationRefutation.claim
   digest: Majorization can fail after normalization within a common charge sector. -/

import D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation
import D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
import D5.S3.Entropy.Forgetting.CapacityMonotone

/-!
Charge-sector normalization need not preserve majorization of diagonal density matrices.
This is the sectorwise reading of the question in Arias, Di Giulio, Keski-Vakkuri and Tonni,
arXiv:2301.02117, Section 7, with the normalized blocks of equation (6.1).
-/

set_option autoImplicit false

namespace D5.S3.Entropy.ChargeSectorMajorizationRefutation

open D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation (Majorizes)

open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing (desc)

open D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)

/-- The eigenvalues of the normalized charge block, in descending order.
Only indices in the eigenspace occur; zero eigenvalues retain their multiplicities. -/
noncomputable def sectorSpectrum {n : ℕ} (r : Fin n → ℝ) (charge : Fin n → ℤ)
    (q : ℤ) : List ℝ :=
  (((List.finRange n).filter (fun i => decide (charge i = q))).map
    (fun i => r i / pushforward charge r q)).mergeSort (fun a b => decide (b ≤ a))

/-- Majorization of diagonal density matrices would persist in every common
positive-weight charge sector after normalizing both blocks. -/
def claim : Prop :=
  ∀ (n : ℕ) (charge : Fin n → ℤ) (r s : Fin n → ℝ),
    (∀ i, 0 ≤ r i) → (∑ i, r i = 1) →
    (∀ i, 0 ≤ s i) → (∑ i, s i = 1) →
    Majorizes (desc r) (desc s) →
    ∀ q : ℤ, 0 < pushforward charge r q → 0 < pushforward charge s q →
      Majorizes (sectorSpectrum r charge q) (sectorSpectrum s charge q)

private def chargeData : Fin 4 → ℤ := ![0, 0, 1, 1]
private noncomputable def r : Fin 4 → ℝ := ![6/20, 6/20, 7/20, 1/20]
private noncomputable def s : Fin 4 → ℝ := ![7/20, 5/20, 4/20, 4/20]

private lemma r_state : (∀ i, 0 ≤ r i) ∧ (∑ i, r i = 1) := by
  constructor
  · intro i
    rw [r.eq_1]
    fin_cases i <;> norm_num
  · rw [r.eq_1]
    norm_num [Fin.sum_univ_succ]

private lemma s_state : (∀ i, 0 ≤ s i) ∧ (∑ i, s i = 1) := by
  constructor
  · intro i
    rw [s.eq_1]
    fin_cases i <;> norm_num
  · rw [s.eq_1]
    norm_num [Fin.sum_univ_succ]

private lemma full_spectra :
    desc r = [7/20, 6/20, 6/20, 1/20] ∧
    desc s = [7/20, 5/20, 4/20, 4/20] := by
  constructor
  · change ([6/20, 6/20, 7/20, 1/20] : List ℝ).mergeSort
      (fun a b => decide (b ≤ a)) = _
    apply List.Perm.eq_of_pairwise' (r := fun a b : ℝ => b ≤ a)
      (List.pairwise_mergeSort' _ _) (by norm_num)
    exact (List.mergeSort_perm _ _).trans
      (((List.Perm.swap (7/20 : ℝ) (6/20) [1/20]).cons (6/20)).trans
        (List.Perm.swap (7/20) (6/20) [6/20, 1/20]))
  · change ([7/20, 5/20, 4/20, 4/20] : List ℝ).mergeSort
      (fun a b => decide (b ≤ a)) = _
    exact List.mergeSort_of_pairwise (by norm_num)

private lemma global_majorizes : Majorizes (desc r) (desc s) := by
  rw [full_spectra.1, full_spectra.2]
  constructor
  · intro k hk hk4
    norm_num at hk4
    interval_cases k <;> norm_num
  · norm_num

private lemma sector_weights :
    pushforward chargeData r 0 = 3/5 ∧ pushforward chargeData s 0 = 3/5 := by
  constructor
  · rw [pushforward]
    simp_rw [chargeData.eq_1]
    norm_num [r, Fin.sum_univ_succ]
  · rw [pushforward]
    simp_rw [chargeData.eq_1]
    norm_num [s, Fin.sum_univ_succ]

private lemma sector_spectra :
    sectorSpectrum r chargeData 0 = [1/2, 1/2] ∧
    sectorSpectrum s chargeData 0 = [7/12, 5/12] := by
  constructor
  · unfold sectorSpectrum
    rw [sector_weights.1]
    change ([(6/20 : ℝ) / (3/5), (6/20) / (3/5)].mergeSort
      (fun a b => decide (b ≤ a))) = _
    convert! List.mergeSort_eq_self (fun a b : ℝ => b ≤ a)
      (l := [1/2, 1/2]) (by norm_num) using 1
    norm_num
  · unfold sectorSpectrum
    rw [sector_weights.2]
    change ([(7/20 : ℝ) / (3/5), (5/20) / (3/5)].mergeSort
      (fun a b => decide (b ≤ a))) = _
    convert! List.mergeSort_eq_self (fun a b : ℝ => b ≤ a)
      (l := [7/12, 5/12]) (by norm_num) using 1
    norm_num

private lemma sector_failure :
    ¬ Majorizes (sectorSpectrum r chargeData 0) (sectorSpectrum s chargeData 0) := by
  rw [sector_spectra.1, sector_spectra.2]
  intro h
  have hp := h.1 1 (by norm_num) (by norm_num)
  norm_num at hp

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
