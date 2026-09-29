/- GID: D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A prescribed label law lifts to the world at the same total-variation distance whenever its support has nonempty fibers. -/

import D5.S3.TotalVariation.Equality.DataProcessingEquality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Equality.DataProcessingEquality

variable {W Z : Type*} [Fintype W] [Fintype Z] [DecidableEq Z]

/-- The deterministic label kernel `K w z = [λ w = z]`. -/
def labelKernel (lab : W → Z) (w : W) (z : Z) : ℝ :=
  if lab w = z then 1 else 0

/-- **Lifting a label law at equal distance.** Let `ρ` be a probability mass function on a finite
world `W`, `λ : W → Z` a label map with pushforward `P = λ_* ρ`, and `Q` a probability mass
function on `Z`. Some world law pushes forward to `Q` exactly when every label of positive
`Q`-mass has a nonempty fiber; in that case one such world law `ρ'` has
`TV(ρ, ρ') = TV(P, Q)`. -/
theorem fiberwise_equal_distance_lift (ρ : W → ℝ) (hρ0 : ∀ w, 0 ≤ ρ w) (hρ1 : ∑ w, ρ w = 1)
    (lab : W → Z) (Q : Z → ℝ) (hQ0 : ∀ z, 0 ≤ Q z) (hQ1 : ∑ z, Q z = 1) :
    ((∃ ρ' : W → ℝ, (∀ w, 0 ≤ ρ' w) ∧ ∑ w, ρ' w = 1 ∧ channelOutput (labelKernel lab) ρ' = Q) ↔
      ∀ z, 0 < Q z → ∃ w, lab w = z) ∧
    ((∀ z, 0 < Q z → ∃ w, lab w = z) →
      ∃ ρ' : W → ℝ, (∀ w, 0 ≤ ρ' w) ∧ ∑ w, ρ' w = 1 ∧
        channelOutput (labelKernel lab) ρ' = Q ∧
        totalVariation ρ ρ' = totalVariation (channelOutput (labelKernel lab) ρ) Q) := by
  classical
  -- pushforward along the label map is the fiber sum
  have hpush : ∀ (p : W → ℝ) (z : Z),
      channelOutput (labelKernel lab) p z = ∑ w ∈ Finset.univ.filter (fun w => lab w = z), p w := by
    intro p z
    simp only [channelOutput, labelKernel, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hkernel : (∀ w z, 0 ≤ labelKernel lab w z) ∧ ∀ w, ∑ z, labelKernel lab w z = 1 := by
    refine ⟨fun w z => by unfold labelKernel; split_ifs <;> norm_num, fun w => ?_⟩
    simp [labelKernel]
  set P := channelOutput (labelKernel lab) ρ with hP
  -- the lift under the support condition
  have hlift : (∀ z, 0 < Q z → ∃ w, lab w = z) →
      ∃ ρ' : W → ℝ, (∀ w, 0 ≤ ρ' w) ∧ ∑ w, ρ' w = 1 ∧
        channelOutput (labelKernel lab) ρ' = Q ∧
        totalVariation ρ ρ' = totalVariation P Q := by
    intro hsupp
    -- a chosen fiber element for labels of zero `P`-mass and positive `Q`-mass
    let pick : Z → Option W := fun z => if h : ∃ w, lab w = z then some h.choose else none
    let ρ' : W → ℝ := fun w =>
      if 0 < P (lab w) then Q (lab w) * ρ w / P (lab w)
      else if pick (lab w) = some w then Q (lab w) else 0
    have hP0 : ∀ z, 0 ≤ P z := fun z => by
      rw [hP, hpush]; exact Finset.sum_nonneg fun w _ => hρ0 w
    have hρ'0 : ∀ w, 0 ≤ ρ' w := by
      intro w
      simp only [ρ']
      split_ifs with h1
      · exact div_nonneg (mul_nonneg (hQ0 _) (hρ0 w)) (hP0 _)
      · exact hQ0 _
      · exact le_rfl
    -- on a fiber of zero mass, `ρ` vanishes
    have hzero_fiber : ∀ w, ¬ 0 < P (lab w) → ρ w = 0 := by
      intro w hw
      have hPz : P (lab w) = 0 := le_antisymm (not_lt.mp hw) (hP0 _)
      rw [hP, hpush] at hPz
      exact (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hρ0 v).mp hPz w (by simp)
    have hpush' : channelOutput (labelKernel lab) ρ' = Q := by
      funext z
      rw [hpush]
      by_cases hz : 0 < P z
      · have : ∀ w ∈ Finset.univ.filter (fun w => lab w = z), ρ' w = Q z * ρ w / P z := by
          intro w hw
          have hwz : lab w = z := (Finset.mem_filter.mp hw).2
          simp only [ρ', hwz, if_pos hz]
        rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← Finset.mul_sum]
        have hPsum : ∑ w ∈ Finset.univ.filter (fun w => lab w = z), ρ w = P z := by
          rw [hP, hpush]
        rw [hPsum, mul_div_assoc, div_self hz.ne', mul_one]
      · have : ∀ w ∈ Finset.univ.filter (fun w => lab w = z),
            ρ' w = if pick z = some w then Q z else 0 := by
          intro w hw
          have hwz : lab w = z := (Finset.mem_filter.mp hw).2
          simp only [ρ', hwz, if_neg hz]
        rw [Finset.sum_congr rfl this]
        by_cases hex : ∃ w, lab w = z
        · have hpick : pick z = some hex.choose := by simp only [pick, dif_pos hex]
          rw [Finset.sum_eq_single hex.choose]
          · rw [if_pos hpick]
          · intro w _ hw
            rw [if_neg]
            rw [hpick]
            exact fun h => hw (Option.some_injective _ h).symm
          · intro hnot
            exact (hnot (by simp [hex.choose_spec])).elim
        · have hQz : Q z = 0 := by
            by_contra hne
            exact hex (hsupp z (lt_of_le_of_ne (hQ0 z) (Ne.symm hne)))
          simp [hQz]
    have hsum1 : ∑ w, ρ' w = 1 := by
      have hK := hkernel.2
      calc ∑ w, ρ' w = ∑ w, ρ' w * ∑ z, labelKernel lab w z := by simp [hK]
        _ = ∑ z, channelOutput (labelKernel lab) ρ' z := by
            simp only [channelOutput, Finset.mul_sum]
            exact Finset.sum_comm
        _ = 1 := by rw [hpush']; exact hQ1
    refine ⟨ρ', hρ'0, hsum1, hpush', ?_⟩
    -- every fiber changes with one sign, so the frozen criterion gives equal distance
    have hcrit := (total_variation_channel_eq_iff_no_sign_mixing ρ ρ' (labelKernel lab) hkernel).mpr
    rw [← hpush', hP]
    refine (hcrit fun z => ?_).symm
    by_cases hz : 0 < P z
    · by_cases hle : P z ≤ Q z
      · right
        intro w hw
        unfold labelKernel
        split_ifs with hwz
        · exfalso
          have : ρ' w = Q z * ρ w / P z := by simp only [ρ', hwz, if_pos hz]
          rw [this] at hw
          have : ρ w ≤ Q z * ρ w / P z := by
            rw [le_div_iff₀ hz]
            nlinarith [hρ0 w]
          linarith
        · rfl
      · left
        intro w hw
        unfold labelKernel
        split_ifs with hwz
        · exfalso
          have : ρ' w = Q z * ρ w / P z := by simp only [ρ', hwz, if_pos hz]
          rw [this] at hw
          have : Q z * ρ w / P z ≤ ρ w := by
            rw [div_le_iff₀ hz]
            nlinarith [hρ0 w, not_le.mp hle]
          linarith
        · rfl
    · right
      intro w hw
      unfold labelKernel
      split_ifs with hwz
      · exfalso
        have hρw : ρ w = 0 := hzero_fiber w (by rw [hwz]; exact hz)
        linarith [hρ'0 w]
      · rfl
  refine ⟨⟨fun ⟨ρ', _, _, hρ'Q⟩ z hz => ?_, fun h => ?_⟩, hlift⟩
  · by_contra hne
    push Not at hne
    have : channelOutput (labelKernel lab) ρ' z = 0 := by
      rw [hpush]
      exact Finset.sum_eq_zero fun w hw => absurd (Finset.mem_filter.mp hw).2 (hne w)
    rw [hρ'Q] at this
    linarith
  · obtain ⟨ρ', h0, h1, hQ', -⟩ := hlift h
    exact ⟨ρ', h0, h1, hQ'⟩

#print axioms fiberwise_equal_distance_lift

end D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift
