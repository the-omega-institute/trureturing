/- GID: D5/S3/Analytic/Oscillation/MontgomerySublogCount
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomerySublogCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sublogarithmic count discrepancy controls the uniform Montgomery leading coefficient. -/

import D5.S3.Analytic.Oscillation.MontgomeryCountUpper
import D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! The inclusive counting error controls the Lorentz pair sum at each cutoff. -/

open Filter Set
open scoped Topology

noncomputable section

namespace D5.S3.Analytic.Oscillation.MontgomerySublogCount

open OrdinateCounting (Spectrum CountAsymptotic count_mono)
open SpectrumPhaseCutoff (mem_cut)
open MontgomeryCountUpper (pairSum)
open MontgomeryWindow (pairCos)
open SmoothedSpectrumCounting.CutDensity (countMain)
open Omega.MeasureTheory.LorentzIntervalMass (kernel lorentz_sum_upper)

private abbrev c : ℝ := 1 / (2 * Real.pi)
private abbrev C : ℝ := 2 * Real.pi

private theorem uniform_discrepancy (S : Spectrum) (C : ℝ)
    (err : Tendsto (fun x : ℝ => ((S.N x : ℝ) - countMain C x) / Real.log x) atTop (𝓝 0))
    {η : ℝ} (positive : 0 < η) :
    ∃ A : ℝ, 1 < A ∧ ∀ Y x, A ≤ x → x ≤ Y →
      |(S.N x : ℝ) - countMain C x| ≤ η * Real.log Y := by
  have absErr := err.abs
  rw [abs_zero] at absErr
  obtain ⟨a, ha⟩ := eventually_atTop.mp (absErr.eventually (gt_mem_nhds positive))
  refine ⟨max 2 a, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Y x hx hxy
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ((le_max_left 2 a).trans hx)
  have hl := Real.log_pos hx1
  have he := ha _ ((le_max_right 2 a).trans hx)
  rw [abs_div, abs_of_pos hl] at he
  exact ((div_lt_iff₀ hl).mp he).le.trans
    (mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans hx1) hxy) positive.le)

private theorem interval_mass_padded (S : Spectrum) {Y u r p : ℝ}
    (uY : u ≤ Y) (r0 : 0 ≤ r) (p0 : 0 < p) :
    (∑ j ∈ S.cut Y, if S.gamma j - u ∈ Icc (-r) r then (S.mult j : ℝ) else 0) ≤
      (S.N (min Y (u + r)) : ℝ) - (S.N (u - r - p) : ℝ) := by
  classical
  let a := u - r - p
  let b := min Y (u + r)
  have hab : a ≤ b := le_min (by dsimp [a]; linarith) (by dsimp [a]; linarith)
  have hcut : S.cut a ⊆ S.cut b := fun _ hj => mem_cut.mpr ((mem_cut.mp hj).trans hab)
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ j ∈ S.cut b \ S.cut a, (S.mult j : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
      intro j hj
      obtain ⟨hY, hr⟩ := Finset.mem_filter.mp hj
      apply Finset.mem_sdiff.mpr
      refine ⟨mem_cut.mpr (le_min (mem_cut.mp hY) (by linarith [hr.2])), ?_⟩
      intro h
      have h' := mem_cut.mp h
      dsimp [a] at h'
      linarith [hr.1]
    _ = _ := by
      rw [Finset.sum_sdiff_eq_sub hcut]
      simp only [Spectrum.N, Nat.cast_sum, a, b]

private theorem relative_main_increment {C a b Y : ℝ}
    (hC : 0 < C) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Y) :
    countMain C b - countMain C a ≤ (Real.log (Y / C) / C) * (b - a) := by
  let k := Real.log (Y / C) / C
  let g := fun x : ℝ => k * x - countMain C x
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt g (k - Real.log (x / C) / C) x := by
    have hm := (Real.hasDerivAt_mul_log (div_pos hx hC).ne').comp x
      ((hasDerivAt_id x).div_const C)
    have hf := hm.sub ((hasDerivAt_id x).div_const C)
    have hm' : HasDerivAt (countMain C) (Real.log (x / C) / C) x := by
      convert hf using 1
      · funext z
        unfold countMain
        dsimp
        ring
      · ring
    change HasDerivAt ((fun z : ℝ => k * z) - countMain C)
      (k - Real.log (x / C) / C) x
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul k).sub hm'
  have hmono : MonotoneOn g (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun x hx => (hd x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (ha.trans hx.1)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (ha.trans hx.1)).deriv]
      apply sub_nonneg.mpr
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (div_pos (ha.trans hx.1) hC)
          (div_le_div_of_nonneg_right (hx.2.le.trans hb) hC.le)) hC.le
  have h := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  dsimp [g] at h
  dsimp [k] at h
  linarith

/-- The leading counting asymptotic follows from the sublogarithmic discrepancy. -/
theorem countAsymptotic_of_sublog (S : Spectrum)
    (err : Tendsto (fun Y : ℝ => ((S.N Y : ℝ) - countMain C Y) / Real.log Y) atTop (𝓝 0)) :
    CountAsymptotic S := by
  have hC : 0 < C := by positivity
  have hshift : Tendsto (fun Y : ℝ => (Real.log C + 1) / Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hmain : Tendsto (fun Y : ℝ => countMain C Y / (Y * Real.log Y)) atTop (𝓝 c) := by
    have h := (hshift.const_sub 1).const_mul c
    rw [sub_zero, mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    rw [countMain, Real.log_div (zero_lt_one.trans hY).ne' hC.ne']
    dsimp [c, C] at *
    field_simp [(Real.log_pos hY).ne', (zero_lt_one.trans hY).ne', Real.pi_ne_zero]
    ring
  have he := err.mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  rw [zero_mul] at he
  have h := hmain.add he
  rw [add_zero] at h
  apply h.congr
  intro Y
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem lorentz_row_le (S : Spectrum) {A η Y : ℝ}
    (hA : 1 < A) (hY : A ≤ Y)
    (hdisc : ∀ x, A ≤ x → x ≤ Y →
      |(S.N x : ℝ) - countMain C x| ≤ η * Real.log Y)
    {u : ℝ} (hu : u ≤ Y) :
    ∑ j ∈ S.cut Y, (S.mult j : ℝ) * kernel (S.gamma j - u) ≤
      2 * Real.pi * (c * Real.log Y) + ((S.N A : ℝ) + 2 * η * Real.log Y + c) := by
  have hlog := Real.log_pos (hA.trans_le hY)
  have hc : 0 < c := by positivity
  have hC : 0 < C := by positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [Real.pi_gt_three]
  have hY0 : 0 < Y := zero_lt_one.trans (hA.trans_le hY)
  refine lorentz_sum_upper (S.cut Y) (fun j => S.gamma j - u)
    (fun j => (S.mult j : ℝ)) (fun _ _ => Nat.cast_nonneg _)
    (ρ := c * Real.log Y) (B := (S.N A : ℝ) + 2 * η * Real.log Y + c) ?_
  intro r hr
  let p := 1 / Real.log Y
  have hp : 0 < p := one_div_pos.mpr hlog
  let l := u - r - p
  let h := min Y (u + r)
  let a := max A l
  let b := max A h
  have hlh : l ≤ h := le_min (by dsimp [l]; linarith) (by dsimp [l]; linarith)
  have hab : a ≤ b := max_le_max_left A hlh
  have hbY : b ≤ Y := max_le hY (min_le_left _ _)
  have haY := hab.trans hbY
  have hwidth : b - a ≤ 2 * r + p := by
    apply sub_le_iff_le_add.mpr
    have hAl : A ≤ a := le_max_left _ _
    have hla : l ≤ a := le_max_right _ _
    have hh : h ≤ u + r := min_le_right _ _
    exact max_le (by linarith) (by dsimp [l] at hla; linarith)
  have hlower : (S.N a : ℝ) ≤ (S.N A : ℝ) + (S.N l : ℝ) := by
    by_cases hAl : A ≤ l
    · rw [show a = l from max_eq_right hAl]
      linarith [Nat.cast_nonneg (α := ℝ) (S.N A)]
    · rw [show a = A from max_eq_left (le_of_not_ge hAl)]
      linarith [Nat.cast_nonneg (α := ℝ) (S.N l)]
  have hupper := count_mono S (show h ≤ b from le_max_right _ _)
  have haerr := abs_le.mp (hdisc a (le_max_left _ _) haY)
  have hberr := abs_le.mp (hdisc b (le_max_left _ _) hbY)
  have hmain := relative_main_increment hC
    (lt_of_lt_of_le (zero_lt_one.trans hA) (le_max_left _ _)) hab hbY
  have hrho : Real.log (Y / C) / C ≤ c * Real.log Y := by
    have hratio := div_le_self hY0.le hC1
    rw [show c * Real.log Y = Real.log Y / C by dsimp [c, C]; ring]
    exact div_le_div_of_nonneg_right (Real.log_le_log (div_pos hY0 hC) hratio) hC.le
  have hmain' := hmain.trans (mul_le_mul_of_nonneg_right hrho (sub_nonneg.mpr hab))
  have hinterval := interval_mass_padded S hu hr hp
  change _ ≤ (S.N h : ℝ) - (S.N l : ℝ) at hinterval
  have hscale := mul_le_mul_of_nonneg_left hwidth (mul_nonneg hc.le hlog.le)
  have hpad : c * Real.log Y * p = c := by dsimp [p]; field_simp
  nlinarith only [hinterval, hlower, hupper, haerr.1, hberr.2, hmain', hscale, hpad]

private theorem pairSum_le_from_local_count (S : Spectrum) {A η Y : ℝ}
    (hA : 1 < A) (hY : A ≤ Y)
    (hdisc : ∀ x, A ≤ x → x ≤ Y →
      |(S.N x : ℝ) - countMain C x| ≤ η * Real.log Y) (t : ℝ) :
    pairSum S Y t ≤ (S.N Y : ℝ) *
      (2 * Real.pi * (c * Real.log Y) + ((S.N A : ℝ) + 2 * η * Real.log Y + c)) := by
  classical
  let bound := 2 * Real.pi * (c * Real.log Y) + ((S.N A : ℝ) + 2 * η * Real.log Y + c)
  unfold pairSum
  calc
    _ ≤ ∑ j ∈ S.cut Y, (S.mult j : ℝ) * bound := by
      apply Finset.sum_le_sum
      intro j hj
      have row := lorentz_row_le S hA hY hdisc (mem_cut.mp hj)
      apply le_trans _ (mul_le_mul_of_nonneg_left row (Nat.cast_nonneg _))
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      rw [pairCos, kernel, show (S.gamma k - S.gamma j) ^ 2 =
        (S.gamma j - S.gamma k) ^ 2 by ring, ← mul_assoc]
      simpa only [mul_assoc, mul_one] using mul_le_mul_of_nonneg_left
        (Real.cos_le_one ((S.gamma j - S.gamma k) * t))
        (show 0 ≤ (S.mult j : ℝ) * (S.mult k : ℝ) *
          (4 / (4 + (S.gamma j - S.gamma k) ^ 2)) by positivity)
    _ = _ := by rw [← Finset.sum_mul]; simp only [bound, Spectrum.N, Nat.cast_sum]

/-- Sublogarithmic count discrepancy gives the sharp leading upper coefficient uniformly in phase. -/
theorem pairSum_le_of_sublog_discrepancy (S : Spectrum)
    (err : Tendsto (fun Y : ℝ => ((S.N Y : ℝ) - countMain C Y) / Real.log Y) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ Y : ℝ in atTop, ∀ t : ℝ,
      pairSum S Y t ≤ (2 * Real.pi * c ^ 2 + ε) * (Y * Real.log Y ^ 2) := by
  have hc : 0 < c := by positivity
  let η := ε / (4 * c)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨A, hA, hdisc⟩ := uniform_discrepancy S C err hη
  have hratio := countAsymptotic_of_sublog S err
  let B := (S.N A : ℝ) + c
  have hz : Tendsto (fun Y : ℝ => B / Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hrow : Tendsto (fun Y : ℝ => 2 * Real.pi * c + 2 * η + B / Real.log Y)
      atTop (𝓝 (2 * Real.pi * c + 2 * η)) := by
    simpa using hz.const_add (2 * Real.pi * c + 2 * η)
  have hprod := hratio.mul hrow
  have hlt : c * (2 * Real.pi * c + 2 * η) < 2 * Real.pi * c ^ 2 + ε := by
    have hηeq : c * (2 * η) = ε / 2 := by dsimp [η]; field_simp; ring
    calc
      _ = 2 * Real.pi * c ^ 2 + c * (2 * η) := by ring
      _ < _ := by rw [hηeq]; linarith
  filter_upwards [hprod.eventually (gt_mem_nhds hlt), eventually_ge_atTop A] with Y hlim hY
  intro t
  have hlog := Real.log_pos (hA.trans_le hY)
  have hY0 := zero_lt_one.trans (hA.trans_le hY)
  apply (pairSum_le_from_local_count S hA hY (hdisc Y) t).trans
  calc
    _ = ((S.N Y : ℝ) / (Y * Real.log Y) *
        (2 * Real.pi * c + 2 * η + B / Real.log Y)) * (Y * Real.log Y ^ 2) := by
      dsimp [B]
      field_simp [hlog.ne', hY0.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hlim.le (by positivity)

end D5.S3.Analytic.Oscillation.MontgomerySublogCount
