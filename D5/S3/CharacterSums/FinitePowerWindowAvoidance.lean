/- GID: D5/S3/CharacterSums/FinitePowerWindowAvoidance
   generality: G
   mirror-B: D5/B/S3/CharacterSums/FinitePowerWindowAvoidance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite real obstacles admit a complete power window with an explicit lower scale. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Complete power windows avoiding finitely many real obstacles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Finset

namespace D5.S3.CharacterSums.FinitePowerWindowAvoidance

private theorem geometric_gap (R : ℕ) (E : Finset ℝ) (A T : ℝ)
    (hA : 1 ≤ A) (hT : 0 < T) (hE : E.card ≤ R) :
    ∃ t : ℝ, T / A ^ R ≤ t ∧ t ≤ T ∧
      ∀ a ∈ E, a ≤ A * t → a ≤ t := by
  classical
  induction R generalizing E T with
  | zero =>
    have he : E = ∅ := card_eq_zero.mp (by omega)
    exact ⟨T, by simp, le_rfl, by simp [he]⟩
  | succ R ih =>
    have hA0 : 0 < A := by linarith
    by_cases h : ∃ a ∈ E, T < a ∧ a ≤ A * T
    · obtain ⟨a, ha, hTa, _⟩ := h
      obtain ⟨t, hlo, hhi, ht⟩ := ih (E.erase a) (T / A)
        (div_pos hT hA0) (by rw [card_erase_of_mem ha]; omega)
      refine ⟨t, ?_, hhi.trans (div_le_self hT.le hA), ?_⟩
      · calc
          T / A ^ (R + 1) = (T / A) / A ^ R := by rw [div_div]; congr 1; ring
          _ ≤ t := hlo
      · intro b hb hbAt
        by_cases hba : b = a
        · subst b
          have : A * t ≤ T := by
            have := (le_div_iff₀ hA0).mp hhi
            nlinarith
          exact (hTa.not_ge (hbAt.trans this)).elim
        · exact ht b (mem_erase.mpr ⟨hba, hb⟩) hbAt
    · refine ⟨T, div_le_self hT.le (one_le_pow₀ hA), le_rfl, ?_⟩
      intro a ha hau
      by_contra hat
      exact h ⟨a, ha, lt_of_not_ge hat, hau⟩

/-- Arbitrary real obstacles admit a whole power window. The exponent loss is
`L * (L*C/η)^card {a ∈ E | 1<a≤X^C}` when `η<C`, and the optimal `L` when `C≤η`. -/
theorem finite_power_window (E : Finset ℝ) (η C X L : ℝ)
    (hη : η < C → 0 < η) (hX : 1 < X) (hL : 1 ≤ L) :
    let J := if C ≤ η then L
      else L * (L * C / η) ^ (E.filter (fun a => 1 < a ∧ a ≤ X ^ C)).card
    ∃ Y : ℝ, 1 < Y ∧ X ^ (1 / J) ≤ Y ∧ Y ^ L ≤ X ∧
      ∀ x ∈ Set.Icc Y (Y ^ L), ∀ a ∈ E, a ≤ x ^ C → a ≤ x ^ η := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < L := by linarith
  have hlog : 0 < log X := log_pos hX
  by_cases hC : C ≤ η
  · simp only [hC, ↓reduceIte]
    let t := log X / L
    have ht : 0 < t := div_pos hlog hL0
    have hy : (exp t) ^ L = X := by
      rw [← exp_mul, show t * L = log X by dsimp [t]; field_simp, exp_log hX0]
    refine ⟨exp t, one_lt_exp_iff.mpr ht, ?_, hy.le, ?_⟩
    · rw [rpow_def_of_pos hX0]
      exact (exp_le_exp.mpr (by dsimp [t]; ring_nf; rfl))
    · intro x hx a _ ha
      have hx1 : 1 ≤ x := (one_lt_exp_iff.mpr ht).le.trans hx.1
      exact ha.trans (rpow_le_rpow_of_exponent_le hx1 hC)
  · simp only [hC, ↓reduceIte]
    have hηC : η < C := lt_of_not_ge hC
    have hη : 0 < η := hη hηC
    have hC0 : 0 < C := hη.trans hηC
    let A := L * C / η
    let T := η * log X / L
    have hA : 1 ≤ A := by
      apply (le_div_iff₀ hη).mpr
      nlinarith
    have hT : 0 < T := by dsimp [T]; positivity
    let E0 := E.filter (fun a => 1 < a ∧ a ≤ X ^ C)
    obtain ⟨s, hslo, hshi, hs⟩ := geometric_gap E0.card
      (E0.image log) A T hA hT card_image_le
    have hs0 : 0 < s := lt_of_lt_of_le (div_pos hT (pow_pos (by linarith) _)) hslo
    let t := s / η
    have ht : 0 < t := div_pos hs0 hη
    have htupper : L * t ≤ log X := by
      have := (le_div_iff₀ hL0).mp hshi
      dsimp [t]
      apply (mul_le_mul_iff_right₀ hη).mp
      field_simp
      nlinarith
    refine ⟨exp t, one_lt_exp_iff.mpr ht, ?_, ?_, ?_⟩
    · rw [rpow_def_of_pos hX0, exp_le_exp]
      dsimp [t]
      apply (le_div_iff₀ hη).mpr
      calc
        log X * (1 / (L * (L * C / η) ^ (E.filter (fun a => 1 < a ∧ a ≤ X ^ C)).card)) * η =
            T / A ^ (E.filter (fun a => 1 < a ∧ a ≤ X ^ C)).card := by dsimp [T, A]; ring
        _ ≤ s := hslo
    · rw [← exp_mul]
      exact (le_log_iff_exp_le hX0).mp (by simpa only [mul_comm] using htupper)
    · intro x hx a ha hax
      have hx0 : 0 < x := (exp_pos t).trans_le hx.1
      have hxlo : t ≤ log x := (le_log_iff_exp_le hx0).mpr hx.1
      have hxhi : log x ≤ L * t := by
        rw [log_le_iff_le_exp hx0]
        rw [mul_comm L t, exp_mul]
        exact hx.2
      have hx1 : 1 ≤ x := (one_lt_exp_iff.mpr ht).le.trans hx.1
      by_cases ha1 : 1 < a
      · have ha0 : 0 < a := zero_lt_one.trans ha1
        have halog : log a ≤ C * log x := by
          simpa only [log_rpow hx0, mul_comm] using log_le_log ha0 hax
        have hxX : x ≤ X := by
          rw [← log_le_log_iff hx0 hX0]
          exact hxhi.trans htupper
        have haX : a ≤ X ^ C := hax.trans (rpow_le_rpow hx0.le hxX hC0.le)
        have hmember : log a ∈ E0.image log :=
          mem_image_of_mem log (mem_filter.mpr ⟨ha, ha1, haX⟩)
        have hbound : log a ≤ A * s := by
          have := mul_le_mul_of_nonneg_left hxhi hC0.le
          have heq : C * (L * t) = A * s := by dsimp [t, A]; ring
          exact halog.trans (heq ▸ this)
        have hsmall := hs _ hmember hbound
        rw [rpow_def_of_pos hx0, ← log_le_iff_le_exp ha0]
        have : s ≤ log x * η := by
          have := (div_le_iff₀ hη).mp hxlo
          exact this
        exact hsmall.trans this
      · exact (le_of_not_gt ha1).trans (one_le_rpow hx1 hη.le)

end D5.S3.CharacterSums.FinitePowerWindowAvoidance
