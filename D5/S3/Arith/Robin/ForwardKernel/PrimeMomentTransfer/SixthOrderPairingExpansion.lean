/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderPairingExpansion
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderPairingExpansion
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Six-label pairing-defect convolutions retain only the empty and single-edge terms. -/

/-
proof_shape: partialPairing_six_convolution: bind-only (consumer:
  SixthOrderTopPairingRefutation.model_unit_transfer);
  sixth_four_defect_lower: bind-only (consumer:
  SixthOrderTopPairingRefutation.model_four_defect_lower).
escape_witness: none; this consumed finite-sum reduction organizes the substantive
  sixth-order countermodel proof without providing an independent admission witness.
admission_basis: consumed-helper.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingDefectInversion

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- When defects vanish in orders at most two, a convolution on at most six labels
contains only its empty and single-edge contributions. -/
theorem partialPairing_six_convolution (U : Finset α) (hU : U.card ≤ 6)
    (N : ℝ) (δ : Finset α → ℝ)
    (hsmall : ∀ V ⊆ U, V.card ≤ 2 → δ V = 0) :
    (∑ P : Finset (Finset α) with IsPartialPairing U P,
      N ^ P.card * δ (U \ pairingSupport P)) =
      δ U + N * ∑ e ∈ U.powersetCard 2, δ (U \ e) := by
  let S : Finset (Finset (Finset α)) := Finset.univ.filter (IsPartialPairing U)
  let S₁ := S.filter (fun P => P.card = 1)
  have hmem (P : Finset (Finset α)) : P ∈ S ↔ IsPartialPairing U P := by
    simp [S]
  have hmem₁ (P : Finset (Finset α)) : P ∈ S₁ ↔ IsPartialPairing U P ∧ P.card = 1 := by
    simp [S₁, S]
  have hsingleton (e : Finset α) : {e} ∈ S₁ ↔ e ∈ U.powersetCard 2 := by
    simp [hmem₁, IsPartialPairing, pairingSupport, Finset.mem_powersetCard, and_comm]
  have h0 : (∅ : Finset (Finset α)) ∈ S := by
    simp [S, IsPartialPairing, pairingSupport]
  have h01 : (∅ : Finset (Finset α)) ∉ S₁ := by simp [hmem₁]
  have hsub : insert ∅ S₁ ⊆ S := by
    intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact h0
    · exact (Finset.mem_filter.mp hP).1
  have hreduced : (∑ P ∈ S, N ^ P.card * δ (U \ pairingSupport P)) =
      ∑ P ∈ insert ∅ S₁, N ^ P.card * δ (U \ pairingSupport P) := by
    symm
    apply Finset.sum_subset hsub
    intro P hP hnot
    have hP' := (hmem P).1 hP
    have hcard : 2 ≤ P.card := by
      have hne : P ≠ ∅ := fun he => hnot (Finset.mem_insert.mpr (Or.inl he))
      have hneq : P.card ≠ 1 := fun hc => hnot
        (Finset.mem_insert.mpr (Or.inr ((hmem₁ P).2 ⟨hP', hc⟩)))
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    rw [hsmall (U \ pairingSupport P) Finset.sdiff_subset
      (by rw [(pairing_remainder_card U P hP').1]; omega), mul_zero]
  have hsingle : (∑ e ∈ U.powersetCard 2, N * δ (U \ e)) =
      ∑ P ∈ S₁, N ^ P.card * δ (U \ pairingSupport P) := by
    apply Finset.sum_nbij' (fun e => {e}) pairingSupport
    · intro e he
      exact (hsingleton e).2 he
    · intro P hP
      obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp ((hmem₁ P).1 hP).2
      simpa [pairingSupport] using (hsingleton e).1 hP
    · intro e he
      simp [pairingSupport]
    · intro P hP
      obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp ((hmem₁ P).1 hP).2
      simp [pairingSupport]
    · intro e he
      simp [pairingSupport]
  change (∑ P ∈ S, N ^ P.card * δ (U \ pairingSupport P)) = _
  rw [hreduced, Finset.sum_insert h01, ← hsingle, ← Finset.mul_sum]
  simp [pairingSupport]

/-- A quantitative lower bound for the four-label defect of the sixth-order model. -/
theorem sixth_four_defect_lower (N : ℝ) (hN : 100 ≤ N) :
    N ^ 2 / 2 ≤ Real.sqrt 15 * (N * (N - 1) * (N - 2) * (N - 3)) / N ^ 2 -
      3 * (N - 1) ^ 2 := by
  have hpos : 0 < N := by linarith
  have hslo : (15 : ℝ) / 4 ≤ Real.sqrt 15 := by
    have hs : 0 ≤ Real.sqrt 15 := by positivity
    nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num]
  have hshi : Real.sqrt 15 ≤ (4 : ℝ) := by
    have hs : 0 ≤ Real.sqrt 15 := by positivity
    nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num]
  have hp : N ^ 4 - 6 * N ^ 3 ≤ N * (N - 1) * (N - 2) * (N - 3) := by
    nlinarith [sq_nonneg N]
  rw [le_sub_iff_add_le, le_div_iff₀ (sq_pos_of_pos hpos)]
  have hprod := mul_le_mul_of_nonneg_left hp (show 0 ≤ Real.sqrt 15 by positivity)
  have hlarge : (0 : ℝ) ≤ N ^ 4 - 6 * N ^ 3 := by
    nlinarith [show 0 ≤ N^3 * (N - 6) by exact mul_nonneg (pow_nonneg hpos.le 3) (by linarith)]
  have hlo := mul_le_mul_of_nonneg_right hslo hlarge
  have hnp : 0 ≤ N^3 * (N - 100) := mul_nonneg (pow_nonneg hpos.le 3) (by linarith)
  have hnp₂ : 0 ≤ N^2 * (N - 100) := mul_nonneg (sq_nonneg N) (by linarith)
  nlinarith [hprod, hlo, hnp, hnp₂, sq_nonneg N]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
