/- GID: D5/S3/Quantum/StationaryPreparation/NormalizedGram
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/NormalizedGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Source entries and positive diagonal equivalence for the actual stationary Gram. -/

import D5.S3.Quantum.StationaryPreparation.NormalizedResiduals

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.NormalizedGram
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.StationaryPreparation.NormalizedResiduals
open D5.S1.Ledger.BoundedTimeSlice
variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A]
variable (a : Multiset A) (blank : A) (U : Unitary (A × K)) (x f : Space K)
variable (hout : ∀ (w : Fin a.card → A) (k : K),
  circuit (fun _ => U) a.card 0 (initialized blank a.card x) (w, k) =
    sectorVector a.card a w * f k)
include hout in
theorem residual_prefix (r : Multiset A) (hr : r ≤ a)
    (w : List A) (hw : w.length ≤ r.card) :
    prefixMemory blank U w (residualMemory a blank U x r) =
      if (w : Multiset A) ≤ r then residualMemory a blank U x (r - (w : Multiset A))
      else 0 := by
  classical
  by_cases hwr : (w : Multiset A) ≤ r
  · rw [if_pos hwr]
    apply suffix_injective blank U (r - (w : Multiset A)).card
    intro v
    have hlen : (w ++ List.ofFn v).length = r.card := by
      simp only [List.length_append, List.length_ofFn, Multiset.card_sub hwr, Multiset.coe_card]
      omega
    rw [← prefix_append, residual_output a blank U x f hout r hr _ hlen,
      residual_output a blank U x f hout (r - (w : Multiset A))
        ((tsub_le_self).trans hr) _ List.length_ofFn]
    have he : ((w ++ List.ofFn v : List A) : Multiset A) = r ↔
        (List.ofFn v : Multiset A) = r - (w : Multiset A) := by
      rw [← Multiset.coe_add]
      constructor
      · intro h
        exact add_left_cancel (h.trans (add_tsub_cancel_of_le hwr).symm)
      · intro h
        rw [h, add_tsub_cancel_of_le hwr]
    simp only [he]
  · rw [if_neg hwr]
    apply suffix_injective blank U (r.card - w.length)
    intro v
    have hlen : (w ++ List.ofFn v).length = r.card := by
      simp only [List.length_append, List.length_ofFn]
      omega
    rw [← prefix_append, residual_output a blank U x f hout r hr _ hlen, map_zero]
    have he : ((w ++ List.ofFn v : List A) : Multiset A) ≠ r := by
      intro h
      apply hwr
      rw [← h, ← Multiset.coe_add]
      exact le_add_right le_rfl
    simp [he]
include hout in
theorem residual_inner_of_le (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hsr : s ≤ r) :
    inner ℂ (residualMemory a blank U x r) (residualMemory a blank U x s) =
      (multiplicity s.card s : ℂ) * inner ℂ (residualMemory a blank U x (r - s)) f := by
  classical
  rw [prefix_inner_sum blank U s.card]
  trans ∑ w : Fin s.card → A, if occupation w = s then
    inner ℂ (residualMemory a blank U x (r - s)) f else 0
  · apply Finset.sum_congr rfl
    intro w _
    rw [residual_output a blank U x f hout s hs _ List.length_ofFn]
    by_cases hw : occupation w = s
    · have hl : (List.ofFn w).length ≤ r.card := by
        simpa only [List.length_ofFn] using Multiset.card_le_card hsr
      rw [residual_prefix a blank U x f hout r hr _ hl]
      change (List.ofFn w : Multiset A) = s at hw
      simp [occupation, hw, hsr]
    · simp [occupation] at hw
      simp [occupation, hw]
  · simp [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity,
      sectorWords, ← Finset.sum_filter]
include hout in
theorem residual_inner_of_not_le (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hcard : s.card ≤ r.card) (hsr : ¬ s ≤ r) :
    inner ℂ (residualMemory a blank U x r) (residualMemory a blank U x s) = 0 := by
  classical
  rw [prefix_inner_sum blank U s.card]
  apply Finset.sum_eq_zero
  intro w _
  rw [residual_output a blank U x f hout s hs _ List.length_ofFn,
    residual_prefix a blank U x f hout r hr _ (by simpa using hcard)]
  by_cases hw : (List.ofFn w : Multiset A) = s
  · simp [hw, hsr]
  · simp [hw]

include hout in
theorem normalized_inner_of_le (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hsr : s ≤ r) (hf : ‖f‖ = 1) :
    inner ℂ (normalizedResidual a blank U x r) (normalizedResidual a blank U x s) =
      (Real.sqrt ((multiplicity s.card s : ℝ) *
        (multiplicity (r-s).card (r-s) : ℝ) / (multiplicity r.card r : ℝ)) : ℂ) *
        sourceMoment a blank U x f (r-s) := by
  have hscale : Real.sqrt ((multiplicity s.card s : ℝ) *
      (multiplicity (r-s).card (r-s) : ℝ) / (multiplicity r.card r : ℝ)) =
      residualScale s * residualScale (r-s) / residualScale r := by
    rw [Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Real.sqrt_mul (Nat.cast_nonneg _)]
    rfl
  have hsq : (multiplicity s.card s : ℂ) = (residualScale s : ℂ)^2 := by
    exact_mod_cast (scale_sq s).symm
  rw [hscale, sourceMoment, normalizedResidual, normalizedResidual, normalizedResidual,
    inner_smul_left, inner_smul_right, inner_smul_left]
  simp only [map_inv₀, Complex.conj_ofReal]
  rw [residual_inner_of_le a blank U x f hout r s hr hs hsr, hsq,
    Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [scale_ne_zero r, scale_ne_zero s, scale_ne_zero (r-s)]
include hout in
theorem normalized_inner_of_ge (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hrs : r ≤ s) (hf : ‖f‖ = 1) :
    inner ℂ (normalizedResidual a blank U x r) (normalizedResidual a blank U x s) =
      (Real.sqrt ((multiplicity r.card r : ℝ) *
        (multiplicity (s-r).card (s-r) : ℝ) / (multiplicity s.card s : ℝ)) : ℂ) *
        star (sourceMoment a blank U x f (s-r)) := by
  rw [← inner_conj_symm, normalized_inner_of_le a blank U x f hout s r hs hr hrs hf]
  simp [map_mul, RCLike.star_def]
include hout in
theorem normalized_inner_incomparable (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hnsr : ¬ s ≤ r) (hnrs : ¬ r ≤ s) (hf : ‖f‖ = 1) :
    inner ℂ (normalizedResidual a blank U x r) (normalizedResidual a blank U x s) = 0 := by
  have h : inner ℂ (residualMemory a blank U x r) (residualMemory a blank U x s) = 0 := by
    rcases le_total s.card r.card with hcard | hcard
    · exact residual_inner_of_not_le a blank U x f hout r s hr hs hcard hnsr
    · rw [← inner_conj_symm, residual_inner_of_not_le a blank U x f hout s r hs hr hcard hnrs,
        map_zero]
  simp only [normalizedResidual, inner_smul_left, inner_smul_right, h, mul_zero]

def normalizedGram : Matrix (TailBox a.count) (TailBox a.count) ℂ :=
  Matrix.gram ℂ (fun r => normalizedResidual a blank U x (boxOccupation a r))
open Classical in
def normalizationDiagonal (a : Multiset A) : Matrix (TailBox a.count) (TailBox a.count) ℂ :=
  Matrix.diagonal (fun r => (residualScale (boxOccupation a r) : ℂ))

theorem diagonal_positive (a : Multiset A) (r : TailBox a.count) :
    0 < (normalizationDiagonal a r r).re := by
  simpa [normalizationDiagonal] using scale_pos (boxOccupation a r)
theorem diagonal_ne_zero (a : Multiset A) (r : TailBox a.count) :
    normalizationDiagonal a r r ≠ 0 := by
  simpa [normalizationDiagonal] using scale_ne_zero (boxOccupation a r)
theorem diagonal_det_ne_zero (a : Multiset A) : (normalizationDiagonal a).det ≠ 0 := by
  classical
  rw [normalizationDiagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun r _ => scale_ne_zero (boxOccupation a r))
theorem occupation_gram_eq_diagonal : occupationGram a blank U x =
    normalizationDiagonal a * normalizedGram a blank U x * normalizationDiagonal a := by
  classical
  ext r s
  simp only [occupationGram, normalizedGram, normalizationDiagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.gram_apply]
  rw [← scale_normalized a blank U x (boxOccupation a r),
    ← scale_normalized a blank U x (boxOccupation a s), inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  ring
theorem occupation_gram_rank_eq :
    (occupationGram a blank U x).rank = (normalizedGram a blank U x).rank := by
  classical
  rw [occupation_gram_eq_diagonal,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (diagonal_det_ne_zero a),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (diagonal_det_ne_zero a)]
theorem normalized_gram_psd : (normalizedGram a blank U x).PosSemidef :=
  Matrix.posSemidef_gram ℂ _
theorem normalized_gram_rank_le : (normalizedGram a blank U x).rank ≤ Fintype.card K := by
  rw [← occupation_gram_rank_eq]
  exact occupation_gram_rank_le a blank U x

end D5.S3.Quantum.StationaryPreparation.NormalizedGram
