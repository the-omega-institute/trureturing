/- GID: D5/S3/Analytic/Oscillation/MontgomeryCountUpper
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/MontgomeryCountUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded two-term count discrepancy gives a uniform Montgomery upper bound. -/

import D5.S3.Analytic.Oscillation.MontgomeryWindow
import D5.S3.Analytic.Oscillation.SmoothedSpectrumCounting
import D5.S3.MeasureTheory.LorentzIntervalMass
import Mathlib.Analysis.Real.Pi.Bounds

/-! A bound on the count in closed intervals controls the ordered Lorentz pair sum. -/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.Analytic.Oscillation.MontgomeryCountUpper

open OrdinateCounting (Spectrum CountAsymptotic)
open MontgomeryWindow (pairCos)
open Omega.MeasureTheory.LorentzIntervalMass (kernel lorentz_sum_upper)
open SmoothedSpectrumCounting (meanScale normalized_count_tends_one)
open SmoothedSpectrumCounting.CutDensity (countMain eventual_count_bound)

local notation "mainTerm" => countMain (2 * Real.pi)

private abbrev c : ℝ := 1 / (2 * Real.pi)

private theorem c_pos : 0 < c := by positivity

private theorem c_le_one : c ≤ 1 := by
  apply (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr
  linarith [Real.pi_gt_three]

private theorem mainTerm_eq (Y : ℝ) : mainTerm Y = c * Y * (Real.log (c * Y) - 1) := by
  rw [countMain, show Y / (2 * Real.pi) = c * Y by dsimp [c]; ring]
  dsimp [c]
  ring

private theorem countMain_sub_le {a b Y : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbY : b ≤ Y) :
    mainTerm b - mainTerm a ≤ c * Real.log Y * (b - a) := by
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
    mainTerm b - mainTerm a =
        c * (b - a) * (Real.log (c * b) - 1) +
          c * a * (Real.log (c * b) - Real.log (c * a)) := by simp only [mainTerm_eq]; ring
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

private theorem interval_mass_le (S : Spectrum) {A D Y u r : ℝ}
    (hA : 1 ≤ A) (hcount : ∀ x, A ≤ x → x ≤ Y → |(S.N x : ℝ) - mainTerm x| ≤ D)
    (hY : A ≤ Y) (hY1 : 1 < Y) (hu : u ≤ Y) (hr : 0 ≤ r) :
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
  have hcountDiff : (S.N b : ℝ) - (S.N a : ℝ) ≤ mainTerm b - mainTerm a + 2 * D := by
    linarith [(abs_le.mp (hcount a haA (hab.trans hbY))).1, (abs_le.mp (hcount b hbA hbY)).2]
  have hmain := countMain_sub_le (by linarith : 0 < a) hab hbY
  have hslack : c * Real.log Y * δ = c := by dsimp [δ]; field_simp
  have hscale := mul_le_mul_of_nonneg_left hwidth (mul_nonneg c_pos.le hlog.le)
  calc
    _ ≤ (S.N A : ℝ) + ((S.N b : ℝ) - (S.N a : ℝ)) := hmass
    _ ≤ (S.N A : ℝ) + (mainTerm b - mainTerm a + 2 * D) :=
      add_le_add_right hcountDiff _
    _ ≤ (S.N A : ℝ) + (c * Real.log Y * (b - a) + 2 * D) := by linarith
    _ ≤ (S.N A : ℝ) + (c * Real.log Y * (2 * r + δ) + 2 * D) := by linarith
    _ = _ := by rw [mul_add, hslack]; ring

/-- The ordered, unnormalized Montgomery sum over the inclusive cutoff. -/
def pairSum (S : Spectrum) (Y t : ℝ) : ℝ :=
  ∑ j ∈ S.cut Y, ∑ k ∈ S.cut Y,
    (S.mult j : ℝ) * (S.mult k : ℝ) * pairCos (S.gamma j - S.gamma k) t

/-- Count control on the interval from the initial height through the cutoff bounds the
absolute ordered pair sum. -/
theorem abs_pairSum_le_of_local_discrepancy (S : Spectrum) {A D Y : ℝ} (hA : 1 ≤ A)
    (hcount : ∀ x, A ≤ x → x ≤ Y → |(S.N x : ℝ) - mainTerm x| ≤ D)
    (hY : A ≤ Y) (hY1 : 1 < Y) (t : ℝ) :
    |pairSum S Y t| ≤ (S.N Y : ℝ) *
      (2 * Real.pi * (c * Real.log Y) + ((S.N A : ℝ) + 2 * D + c)) := by
  classical
  let B : ℝ := (S.N A : ℝ) + 2 * D + c
  unfold pairSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
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
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro k _
      rw [pairCos, kernel, show (S.gamma k - S.gamma j) ^ 2 =
        (S.gamma j - S.gamma k) ^ 2 by ring, ← mul_assoc, abs_mul, abs_of_nonneg (by positivity)]
      have hweight : 0 ≤ (S.mult j : ℝ) * (S.mult k : ℝ) *
          (4 / (4 + (S.gamma j - S.gamma k) ^ 2)) := by positivity
      simpa only [mul_assoc] using
        mul_le_of_le_one_right hweight (Real.abs_cos_le_one ((S.gamma j - S.gamma k) * t))
    _ = _ := by rw [← Finset.sum_mul]; simp only [B, Spectrum.N, Nat.cast_sum]

/-- Bounded two-term discrepancy implies the normalized counting asymptotic. -/
theorem count_asymptotic_of_bounded_discrepancy (S : Spectrum) {D : ℝ}
    (hcount : ∀ᶠ Y : ℝ in atTop, |(S.N Y : ℝ) - mainTerm Y| ≤ D) :
    CountAsymptotic S := by
  obtain ⟨E, hE⟩ := eventual_count_bound S (by positivity : 0 < 2 * Real.pi) hcount
  have h := (normalized_count_tends_one S E hE).const_mul c
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
  have hY0 : 0 < Y := by linarith
  have hlog := Real.log_pos hY
  dsimp [meanScale, c]
  field_simp [hY0.ne', hlog.ne', Real.pi_ne_zero]

/-- The count discrepancy bounds the leading coefficient uniformly in the phase. -/
theorem pairSum_le_of_bounded_discrepancy (S : Spectrum) {D : ℝ}
    (hcount : ∀ᶠ Y : ℝ in atTop, |(S.N Y : ℝ) - mainTerm Y| ≤ D)
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
  have hpair := abs_pairSum_le_of_local_discrepancy S hA
    (fun Z hZ _ => hA₀ Z ((le_max_right _ _).trans hZ)) hY hY1 t
  apply ((le_abs_self (pairSum S Y t)).trans hpair).trans
  change (S.N Y : ℝ) * (2 * Real.pi * (c * Real.log Y) + B) ≤ _
  calc
    _ = ((S.N Y : ℝ) / (Y * Real.log Y) * (2 * Real.pi * c + B / Real.log Y)) *
          (Y * Real.log Y ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hYlim.le (by positivity)

#print axioms pairSum_le_of_bounded_discrepancy

end D5.S3.Analytic.Oscillation.MontgomeryCountUpper
