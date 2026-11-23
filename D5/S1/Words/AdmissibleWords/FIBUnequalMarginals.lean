/- GID: D5/S1/Words/AdmissibleWords/FIBUnequalMarginals
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FIBUnequalMarginals
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A common five-event law has one joint difference constraint at arbitrary marginals. -/

import D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction

/-! Exact common-law region for two oriented differences with unequal event masses. -/

set_option autoImplicit false

open Set MeasureTheory
open D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction

namespace D5.S1.Words.AdmissibleWords.FIBUnequalMarginals

/-- The two differences have their individual ranges and a single shared capacity. -/
theorem joint_range {s h k t w a b : ℝ} :
    (∃ A : Fin 5 → Set ℝ, Nested A ∧
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1) ∧
      volume.real (A 0) = s ∧ volume.real (A 1) = h ∧ volume.real (A 2) = k ∧
      volume.real (A 3) = t ∧ volume.real (A 4) = w ∧
      volume.real (A 4 \ A 0) = a ∧ volume.real (A 3 \ A 1) = b) ↔
      0 ≤ s ∧ h ≤ 1 ∧ k ≤ 1 ∧ t ≤ k ∧
      (max 0 (w - s) ≤ a ∧ a ≤ min w (h - s)) ∧
      (max 0 (t - h) ≤ b ∧ b ≤ min t (1 - h)) ∧ a + b ≤ k - s := by
  constructor
  · rintro ⟨A, nested, measured, sMass, hMass, kMass, tMass, wMass, wa, tb⟩
    obtain ⟨sH, sK, tK, wH, wK⟩ := nested
    have finite (i : Fin 5) : volume (A i) ≠ ⊤ := measure_ne_top_of_subset (measured i).2 (by simp)
    have upper (i : Fin 5) : volume.real (A i) ≤ 1 := by
      simpa [Real.volume_real_Ico] using
        (measureReal_mono (μ := volume) (measured i).2 (by simp))
    have cap := shared_capacity volume (finite 2) (measured 0).1
      (measured 1).1 (measured 3).1 sH sK tK wH wK
    rw [wa, tb, kMass, sMass] at cap
    have aw : a ≤ w := by
      rw [← wa, ← wMass]
      exact measureReal_mono sdiff_subset (finite 4)
    have ah : a ≤ h - s := by
      rw [← wa, ← hMass, ← sMass, ← measureReal_sdiff sH (measured 0).1 (finite 1)]
      exact measureReal_mono (sdiff_subset_sdiff_left wH)
        (measure_ne_top_of_subset sdiff_subset (finite 1))
    have asLower : w - s ≤ a := by
      have split := measureReal_inter_add_sdiff (μ := volume) (s := A 4) (measured 0).1 (finite 4)
      have overlap := measureReal_mono (μ := volume) (s₁ := A 4 ∩ A 0) inter_subset_right (finite 0)
      rw [wa, wMass] at split
      rw [sMass] at overlap
      linarith
    have bt : b ≤ t := by
      rw [← tb, ← tMass]
      exact measureReal_mono sdiff_subset (finite 3)
    have bh : b ≤ 1 - h := by
      rw [← tb]
      apply (measureReal_mono (sdiff_subset_sdiff_left (measured 3).2)
        (measure_ne_top_of_subset sdiff_subset (by simp))).trans_eq
      rw [measureReal_sdiff (measured 1).2 (measured 1).1 (by simp), hMass]
      simp [Real.volume_real_Ico]
    have bhLower : t - h ≤ b := by
      have split := measureReal_inter_add_sdiff (μ := volume) (s := A 3) (measured 1).1 (finite 3)
      have overlap := measureReal_mono (μ := volume) (s₁ := A 3 ∩ A 1) inter_subset_right (finite 1)
      rw [tb, tMass] at split
      rw [hMass] at overlap
      linarith
    refine ⟨sMass ▸ measureReal_nonneg, hMass ▸ upper 1, kMass ▸ upper 2, ?_,
      ⟨max_le (wa ▸ measureReal_nonneg) asLower, le_min aw ah⟩,
      ⟨max_le (tb ▸ measureReal_nonneg) bhLower, le_min bt bh⟩, cap⟩
    rw [← tMass, ← kMass]
    exact measureReal_mono tK (finite 2)
  · rintro ⟨hs, hh, hk, htk, ⟨haLower, haUpper⟩, ⟨hbLower, hbUpper⟩, hab⟩
    obtain ⟨ha, hws⟩ := max_le_iff.mp haLower
    obtain ⟨haw, hah⟩ := le_min_iff.mp haUpper
    obtain ⟨hb, hth⟩ := max_le_iff.mp hbLower
    obtain ⟨hbt, hbh⟩ := le_min_iff.mp hbUpper
    let r := max (s + a) (max (t - b) (h + k - 1))
    have hsa : s + a ≤ r := le_max_left _ _
    have htb : t - b ≤ r := (le_max_left _ _).trans (le_max_right _ _)
    have hck : h + k - 1 ≤ r := (le_max_right _ _).trans (le_max_right _ _)
    have hrh : r ≤ h := max_le (by linarith) (max_le (by linarith) (by linarith))
    have hrkb : r ≤ k - b := max_le (by linarith) (max_le (by linarith) (by linarith))
    have hrk : r ≤ k := by linarith
    have hr : 0 ≤ r := by linarith
    have ht : 0 ≤ t - b := by linarith
    have hw : 0 ≤ w - a := by linarith
    let S := Ico 0 s
    let K := Ico 0 k
    let H := Ico 0 (k + h - r) \ Ico r k
    let T := Ico 0 (r + b) \ Ico (t - b) r
    let W := Ico 0 (s + a) \ Ico (w - a) s
    let A : Fin 5 → Set ℝ := ![S, H, K, T, W]
    have sLaw : MeasurableSet S ∧ S ⊆ Ico 0 1 :=
      ⟨measurableSet_Ico, Ico_subset_Ico_right (by linarith)⟩
    have kLaw : MeasurableSet K ∧ K ⊆ Ico 0 1 := ⟨measurableSet_Ico, Ico_subset_Ico_right hk⟩
    have hLaw : MeasurableSet H ∧ H ⊆ Ico 0 1 :=
      ⟨measurableSet_Ico.diff measurableSet_Ico,
        sdiff_subset.trans (Ico_subset_Ico_right (by linarith))⟩
    have tK : T ⊆ K := sdiff_subset.trans (Ico_subset_Ico_right (by linarith))
    have tLaw : MeasurableSet T ∧ T ⊆ Ico 0 1 :=
      ⟨measurableSet_Ico.diff measurableSet_Ico, tK.trans kLaw.2⟩
    have wSmall : W ⊆ Ico 0 r := sdiff_subset.trans (Ico_subset_Ico_right hsa)
    have wK : W ⊆ K := wSmall.trans (Ico_subset_Ico_right hrk)
    have wLaw : MeasurableSet W ∧ W ⊆ Ico 0 1 :=
      ⟨measurableSet_Ico.diff measurableSet_Ico, wK.trans kLaw.2⟩
    have firstInH : Ico 0 r ⊆ H := by
      intro x hx
      exact ⟨⟨hx.1, by linarith [hx.2]⟩, fun bad => (not_lt_of_ge bad.1) hx.2⟩
    have sH : S ⊆ H := (Ico_subset_Ico_right (by linarith : s ≤ r)).trans firstInH
    have sK : S ⊆ K := Ico_subset_Ico_right (by linarith)
    have wH : W ⊆ H := wSmall.trans firstInH
    have sMass : volume.real S = s := by
      dsimp only [S]
      rw [Real.volume_real_Ico_of_le hs, sub_zero]
    have kMass : volume.real K = k := by
      dsimp only [K]
      rw [Real.volume_real_Ico_of_le (by linarith), sub_zero]
    have hMass : volume.real H = h := by
      dsimp only [H]
      rw [measureReal_sdiff (Ico_subset_Ico hr (by linarith)) measurableSet_Ico (by simp),
        Real.volume_real_Ico_of_le (by linarith), Real.volume_real_Ico_of_le hrk]
      linarith
    have tMass : volume.real T = t := by
      dsimp only [T]
      rw [measureReal_sdiff (Ico_subset_Ico ht (by linarith)) measurableSet_Ico (by simp),
        Real.volume_real_Ico_of_le (by linarith), Real.volume_real_Ico_of_le htb]
      linarith
    have wMass : volume.real W = w := by
      dsimp only [W]
      rw [measureReal_sdiff (Ico_subset_Ico hw (by linarith)) measurableSet_Ico (by simp),
        Real.volume_real_Ico_of_le (by linarith), Real.volume_real_Ico_of_le (by linarith)]
      linarith
    have ws : W \ S = Ico s (s + a) := by
      have horder : w - a ≤ s := by linarith
      ext x
      simp only [W, S, mem_sdiff, mem_Ico]
      grind
    have th : T \ H = Ico r (r + b) := by
      have hstop : r + b ≤ k := by linarith
      ext x
      simp only [T, H, mem_sdiff, mem_Ico]
      grind
    have wDiff : volume.real (W \ S) = a := by
      rw [ws, Real.volume_real_Ico_of_le (by linarith)]
      linarith
    have tDiff : volume.real (T \ H) = b := by
      rw [th, Real.volume_real_Ico_of_le (by linarith)]
      linarith
    refine ⟨A, ⟨sH, sK, tK, wH, wK⟩, ?_, sMass, hMass, kMass, tMass, wMass, wDiff, tDiff⟩
    intro v
    fin_cases v
    · exact sLaw
    · exact hLaw
    · exact kLaw
    · exact tLaw
    · exact wLaw

end D5.S1.Words.AdmissibleWords.FIBUnequalMarginals
