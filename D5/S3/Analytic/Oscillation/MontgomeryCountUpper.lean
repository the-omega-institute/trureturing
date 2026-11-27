/- GID: D5/S3/Analytic/Oscillation/MontgomeryCountUpper
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryCountUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded two-term count discrepancy gives a uniform Montgomery upper bound. -/

import D5.S3.Analytic.Oscillation.MontgomeryWindow
import D5.S3.Fourier.Concentration.LorentzIntervalMass
import Mathlib.Analysis.Real.Pi.Bounds

/-! A bound on the count in closed intervals controls the ordered Lorentz pair sum. -/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.Analytic.Oscillation.MontgomeryCountUpper

open OrdinateCounting (Spectrum CountAsymptotic)
open MontgomeryWindow (pairCos)
open D5.S3.Fourier.Concentration.LorentzIntervalMass (kernel lorentz_sum_upper)

private abbrev c : ℝ := 1 / (2 * Real.pi)

private theorem c_pos : 0 < c := by positivity

private theorem c_le_one : c ≤ 1 := by
  apply (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr
  linarith [Real.pi_gt_three]

/-- Main term in the two-term ordinate count. -/
def countMain (Y : ℝ) : ℝ := c * Y * (Real.log (c * Y) - 1)

private theorem countMain_sub_le {a b Y : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbY : b ≤ Y) :
    countMain b - countMain a ≤ c * Real.log Y * (b - a) := by
  have hb := ha.trans_le hab
  have hca := mul_pos c_pos ha
  have hcb := mul_pos c_pos hb
  have hquot : (c * b) / (c * a) = b / a := by
    field_simp [c_pos.ne']
  have hlog : Real.log (c * b) - Real.log (c * a) ≤ b / a - 1 := by
    rw [← Real.log_div hcb.ne' hca.ne', hquot]
    exact Real.log_le_sub_one_of_pos (div_pos hb ha)
  have herr : c * a * (Real.log (c * b) - Real.log (c * a)) ≤ c * (b - a) := by
    calc
      _ ≤ c * a * (b / a - 1) := mul_le_mul_of_nonneg_left hlog hca.le
      _ = _ := by field_simp
  have hlogY : Real.log (c * b) ≤ Real.log Y :=
    Real.log_le_log hcb ((mul_le_of_le_one_left hb.le c_le_one).trans hbY)
  calc
    countMain b - countMain a =
        c * (b - a) * (Real.log (c * b) - 1) +
          c * a * (Real.log (c * b) - Real.log (c * a)) := by unfold countMain; ring
    _ ≤ c * (b - a) * (Real.log (c * b) - 1) + c * (b - a) := add_le_add_right herr _
    _ = c * (b - a) * Real.log (c * b) := by ring
    _ ≤ c * (b - a) * Real.log Y :=
      mul_le_mul_of_nonneg_left hlogY (mul_nonneg c_pos.le (sub_nonneg.mpr hab))
    _ = _ := by ring

private theorem cut_mono (S : Spectrum) {a b : ℝ} (hab : a ≤ b) :
    S.cut a ⊆ S.cut b := by
  intro j hj
  simp only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hj ⊢
  exact hj.trans hab

private theorem interval_mass_le (S : Spectrum) {A D : ℝ}
    (hA : 1 ≤ A) (hcount : ∀ Y ≥ A, |(S.N Y : ℝ) - countMain Y| ≤ D)
    {Y u r : ℝ} (hY : A ≤ Y) (hY1 : 1 < Y) (hu : u ≤ Y) (hr : 0 ≤ r) :
    (∑ j ∈ S.cut Y, if S.gamma j - u ∈ Icc (-r) r then (S.mult j : ℝ) else 0) ≤
      2 * (c * Real.log Y) * r + ((S.N A : ℝ) + 2 * D + c) := by
  classical
  have hlog := Real.log_pos hY1
  let δ := 1 / Real.log Y
  have hδ : 0 < δ := one_div_pos.mpr hlog
  let a := max A (u - r - δ)
  let b := max A (min Y (u + r))
  have haA : A ≤ a := le_max_left _ _
  have hbA : A ≤ b := le_max_left _ _
  have haU : u - r - δ ≤ a := le_max_right _ _
  have hab : a ≤ b := by
    apply max_le hbA
    exact (le_min (by linarith) (by linarith)).trans (le_max_right _ _)
  have hbY : b ≤ Y := max_le hY (min_le_left _ _)
  have hwidth : b - a ≤ 2 * r + δ := by
    apply sub_le_iff_le_add.mpr
    exact max_le (by linarith) ((min_le_right _ _).trans (by linarith))
  have hdisj : Disjoint (S.cut A) (S.cut b \ S.cut a) := by
    refine Finset.disjoint_left.mpr ?_
    exact fun j hjA hdiff => (Finset.mem_sdiff.mp hdiff).2 (cut_mono S haA hjA)
  have hsub : (S.cut Y).filter (fun j => S.gamma j - u ∈ Icc (-r) r) ⊆
      S.cut A ∪ (S.cut b \ S.cut a) := by
    intro j hj
    obtain ⟨hjY, hjI⟩ := Finset.mem_filter.mp hj
    by_cases hjA : j ∈ S.cut A
    · exact Finset.mem_union_left _ hjA
    · apply Finset.mem_union_right
      rw [Finset.mem_sdiff]
      simp only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hjY hjA ⊢
      refine ⟨(le_min hjY (by linarith [hjI.2])).trans (le_max_right _ _), ?_⟩
      exact not_le.mpr (max_lt (lt_of_not_ge hjA) (by linarith [hjI.1]))
  have hmass :
      (∑ j ∈ S.cut Y, if S.gamma j - u ∈ Icc (-r) r then (S.mult j : ℝ) else 0) ≤
        (S.N A : ℝ) + ((S.N b : ℝ) - (S.N a : ℝ)) := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ j ∈ S.cut A ∪ (S.cut b \ S.cut a), (S.mult j : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => Nat.cast_nonneg _
      _ = _ := by
        rw [Finset.sum_union hdisj, Finset.sum_sdiff_eq_sub (cut_mono S hab)]
        simp only [Spectrum.N, Nat.cast_sum]
  have hcountDiff : (S.N b : ℝ) - (S.N a : ℝ) ≤ countMain b - countMain a + 2 * D := by
    linarith [(abs_le.mp (hcount a haA)).1, (abs_le.mp (hcount b hbA)).2]
  have hmain := countMain_sub_le (by linarith : 0 < a) hab hbY
  have hslack : c * Real.log Y * δ = c := by dsimp [δ]; field_simp
  have hscale := mul_le_mul_of_nonneg_left hwidth (mul_nonneg c_pos.le hlog.le)
  calc
    _ ≤ (S.N A : ℝ) + ((S.N b : ℝ) - (S.N a : ℝ)) := hmass
    _ ≤ (S.N A : ℝ) + (countMain b - countMain a + 2 * D) :=
      add_le_add_right hcountDiff _
    _ ≤ (S.N A : ℝ) + (c * Real.log Y * (b - a) + 2 * D) := by linarith
    _ ≤ (S.N A : ℝ) + (c * Real.log Y * (2 * r + δ) + 2 * D) := by linarith
    _ = _ := by rw [mul_add, hslack]; ring

/-- The ordered, unnormalized Montgomery sum over the inclusive cutoff. -/
def pairSum (S : Spectrum) (Y t : ℝ) : ℝ :=
  ∑ j ∈ S.cut Y, ∑ k ∈ S.cut Y,
    (S.mult j : ℝ) * (S.mult k : ℝ) * pairCos (S.gamma j - S.gamma k) t

private theorem pairSum_le (S : Spectrum) {A D : ℝ} (hA : 1 ≤ A)
    (hcount : ∀ Y ≥ A, |(S.N Y : ℝ) - countMain Y| ≤ D)
    {Y : ℝ} (hY : A ≤ Y) (hY1 : 1 < Y) (t : ℝ) :
    pairSum S Y t ≤ (S.N Y : ℝ) *
      (2 * Real.pi * (c * Real.log Y) + ((S.N A : ℝ) + 2 * D + c)) := by
  classical
  let B : ℝ := (S.N A : ℝ) + 2 * D + c
  unfold pairSum
  calc
    _ ≤ ∑ j ∈ S.cut Y, (S.mult j : ℝ) * (2 * Real.pi * (c * Real.log Y) + B) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjY : S.gamma j ≤ Y := by simpa [Spectrum.cut] using hj
      have hrow := lorentz_sum_upper (S.cut Y) (fun k => S.gamma k - S.gamma j)
        (fun k => (S.mult k : ℝ)) (fun k _ => Nat.cast_nonneg (S.mult k))
        (ρ := c * Real.log Y) (B := B)
        (fun r hr => interval_mass_le S hA hcount hY hY1 hjY hr)
      apply le_trans _ (mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg _))
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      rw [pairCos, kernel, show (S.gamma k - S.gamma j) ^ 2 =
        (S.gamma j - S.gamma k) ^ 2 by ring, ← mul_assoc]
      simpa only [mul_assoc] using mul_le_of_le_one_right
        (show 0 ≤ (S.mult j : ℝ) * (S.mult k : ℝ) *
          (4 / (4 + (S.gamma j - S.gamma k) ^ 2)) by positivity)
        (Real.cos_le_one ((S.gamma j - S.gamma k) * t))
    _ = _ := by rw [← Finset.sum_mul]; simp only [B, Spectrum.N, Nat.cast_sum]

/-- Bounded two-term discrepancy implies the normalized counting asymptotic. -/
theorem count_asymptotic_of_bounded_discrepancy (S : Spectrum) {D : ℝ}
    (hcount : ∀ᶠ Y : ℝ in atTop, |(S.N Y : ℝ) - countMain Y| ≤ D) :
    CountAsymptotic S := by
  let C := D + |c * (Real.log c - 1)|
  have hzero : Tendsto (fun Y : ℝ => C / Real.log Y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C
  have herr : Tendsto (fun Y : ℝ => (S.N Y : ℝ) / (Y * Real.log Y) - c) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hzero
    filter_upwards [hcount, eventually_gt_atTop (1 : ℝ)] with Y hY hY1
    have hY0 : 0 < Y := by linarith
    have hlog := Real.log_pos hY1
    have hD : 0 ≤ D := (abs_nonneg _).trans hY
    have hterm :
        |countMain Y - c * (Y * Real.log Y)| = |c * (Real.log c - 1)| * Y := by
      unfold countMain
      rw [Real.log_mul c_pos.ne' hY0.ne',
        show c * Y * (Real.log c + Real.log Y - 1) - c * (Y * Real.log Y) =
          c * (Real.log c - 1) * Y by ring, abs_mul, abs_of_pos hY0]
    rw [Real.norm_eq_abs, show (S.N Y : ℝ) / (Y * Real.log Y) - c =
      ((S.N Y : ℝ) - c * (Y * Real.log Y)) / (Y * Real.log Y) by field_simp,
      abs_div, abs_of_pos (mul_pos hY0 hlog)]
    have hbound : |(S.N Y : ℝ) - c * (Y * Real.log Y)| ≤ C * Y := by
      calc
        _ ≤ |(S.N Y : ℝ) - countMain Y| + |countMain Y - c * (Y * Real.log Y)| :=
          abs_sub_le _ _ _
        _ ≤ D + |c * (Real.log c - 1)| * Y := by rw [hterm]; exact add_le_add_left hY _
        _ ≤ C * Y := by dsimp [C]; linarith [le_mul_of_one_le_right hD hY1.le]
    calc
      _ ≤ C * Y / (Y * Real.log Y) := div_le_div_of_nonneg_right hbound (by positivity)
      _ = _ := by field_simp
  simpa [CountAsymptotic] using herr.add_const c

/-- The count discrepancy bounds the leading coefficient uniformly in the phase. -/
theorem pairSum_le_of_bounded_discrepancy (S : Spectrum) {D : ℝ}
    (hcount : ∀ᶠ Y : ℝ in atTop, |(S.N Y : ℝ) - countMain Y| ≤ D)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ Y : ℝ in atTop, ∀ t : ℝ,
      pairSum S Y t ≤ (2 * Real.pi * c ^ 2 + ε) * (Y * Real.log Y ^ 2) := by
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hcount
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  let B : ℝ := (S.N A : ℝ) + 2 * D + c
  have hratio := count_asymptotic_of_bounded_discrepancy S hcount
  have hrow : Tendsto (fun Y : ℝ => 2 * Real.pi * c + B / Real.log Y)
      atTop (𝓝 (2 * Real.pi * c)) := by
    have hz : Tendsto (fun Y : ℝ => B / Real.log Y) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul B
    simpa using hz.const_add (2 * Real.pi * c)
  have hprod :
      Tendsto (fun Y : ℝ => (S.N Y : ℝ) / (Y * Real.log Y) *
        (2 * Real.pi * c + B / Real.log Y)) atTop (𝓝 (2 * Real.pi * c ^ 2)) := by
    convert hratio.mul hrow using 2
    ring
  filter_upwards [hprod.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε)),
    eventually_ge_atTop A, eventually_gt_atTop (1 : ℝ)] with Y hYlim hY hY1
  intro t
  have hlog := Real.log_pos hY1
  have hY0 : 0 < Y := by linarith
  apply (pairSum_le S hA (fun Z hZ => hA₀ Z ((le_max_right _ _).trans hZ)) hY hY1 t).trans
  change (S.N Y : ℝ) * (2 * Real.pi * (c * Real.log Y) + B) ≤ _
  calc
    _ = ((S.N Y : ℝ) / (Y * Real.log Y) * (2 * Real.pi * c + B / Real.log Y)) *
          (Y * Real.log Y ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hYlim.le (by positivity)

#print axioms pairSum_le_of_bounded_discrepancy

end D5.S3.Analytic.Oscillation.MontgomeryCountUpper
