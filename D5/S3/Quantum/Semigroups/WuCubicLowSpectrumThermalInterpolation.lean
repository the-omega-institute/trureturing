import D5.S3.Quantum.Semigroups.WuCubicBoundaryThermal
import D5.S3.Quantum.Semigroups.WuCubicCornerInterpolation
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCorner
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrumLevelInterpolation
import Mathlib.Analysis.Calculus.DSlope
import OmegaBuild.Commands

/-! Thermal and box interpolation of the normalized Wu cubic deficit at fixed frame. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrumThermalInterpolation

open _root_.Matrix Filter Set
open scoped BigOperators Topology

open WuCubicDirectedOccupationCap (Mat)
open WuRepeatedMiddleCubic (alpha weight)
open WuCubicAngularCertificate
  (normalizedDeficit physicalFrame cutEnergy cutBias lowerCoeff upperCoeff longCoeff)
open WuCubicBoundaryThermal (jumpContribution spectralCharge normalizedDeficit_eq_jumpContribution
  normalizedDeficit_second_le c_second_hasDerivAt e_second_hasDerivAt)
open WuCubicCornerInterpolation (corner_interpolation corner_floor boxCorner finite_box_floor)
open WuCubicLowSpectrumLevelInterpolation (levelSlice levelSlice_floor)
open WuCubicLowSpectrumCorner
  (cornerLower thermalCenterLower cornerLower_le_normalizedDeficit shellCorner_normalizedDeficit)
open WuCubicSharpAngularSlice (imbalanceSliceMin squareSliceMin squareBoundaryMin squareEdgeMin)

open private gamma h gibbsLow gibbsHigh cutA cutB c e bias from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private levelsAt totalAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private centeredEntropy h_hasDerivAt alpha_hasDerivAt bias_hasDerivAt
  jumpContribution_hasDerivAt h_second_hasDerivAt alpha_second_hasDerivAt
  bias_second_hasDerivAt jumpContribution_second_hasDerivAt from
  D5.S3.Quantum.Semigroups.WuCubicBoundaryThermal
open private normalizedDeficit_second_eq jumpContribution_eq c_hasDerivAt e_hasDerivAt
  logMean alphaDen alpha_eq_logCoordinate thermalLog thermalLog_hasDerivAt h_eq from
  D5.S3.Quantum.Semigroups.WuCubicBoundaryThermal
open private logUpper logRatioLower logRatioUpper logSeries gibbsArgument
  thermalBase thermalFactor from D5.S3.Quantum.Semigroups.WuCubicBoundaryCorner
open private entropyLower massLogUpper logLower from
  D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCorner
open private crossCoeff directedCoeff from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

section

open private logCoordinate from D5.S3.Quantum.Semigroups.WuCubicBoundaryThermal

private theorem alpha_continuousWithinAt_one : ContinuousWithinAt alpha (Ici 1) 1 := by
  let A : ℝ → ℝ := fun s => 1 / 2 * Real.log ((1 + s) / (1 - s))
  have hA : HasDerivAt A 1 0 := by
    simpa [A] using
      Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range 0
        (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hM : ContinuousAt (dslope A 0) 0 :=
    continuousAt_dslope_same.mpr hA.differentiableAt
  have hs : ContinuousAt logCoordinate 1 := by
    unfold logCoordinate
    fun_prop (disch := norm_num)
  have hs0 : logCoordinate 1 = 0 := by norm_num [logCoordinate]
  have hM' : ContinuousAt (fun r => dslope A 0 (logCoordinate r)) 1 :=
    (hs0.symm ▸ hM : ContinuousAt (dslope A 0) (logCoordinate 1)).comp hs
  have hD : ContinuousAt (fun r => (1 + logCoordinate r ^ 2 / 3) *
      dslope A 0 (logCoordinate r)) 1 := by
    exact (continuousAt_const.add ((hs.pow 2).div_const 3)).mul hM'
  have hquot : ContinuousAt (fun r => (1 / 2) /
      ((1 + logCoordinate r ^ 2 / 3) * dslope A 0 (logCoordinate r))) 1 :=
    continuousAt_const.div hD (by simp [hs0, hA.deriv])
  refine hquot.continuousWithinAt.congr_of_mem ?_ (mem_Ici.mpr le_rfl)
  intro r hr
  rcases eq_or_lt_of_le (mem_Ici.mp hr) with rfl | hr
  · norm_num [alpha, hs0, hA.deriv]
  · have hsne : logCoordinate r ≠ 0 := by
      unfold logCoordinate
      exact div_ne_zero (sub_ne_zero.mpr hr.ne') (by linarith)
    rw [alpha_eq_logCoordinate hr, dslope_of_ne A hsne]
    simp [alphaDen, logMean, A, slope_fun_def_field]

end

private theorem normalizedDeficit_thermal_continuousOn (U : unitary Mat) {m n q : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hq : 0 ≤ q) :
    ContinuousOn (fun r => normalizedDeficit r U m n q) (Ici 1) := by
  have ha : ContinuousOn alpha (Ici 1) := by
    intro r hr
    rcases eq_or_lt_of_le (mem_Ici.mp hr) with rfl | hr
    · exact alpha_continuousWithinAt_one
    · exact (alpha_hasDerivAt hr).continuousAt.continuousWithinAt
  have hh : ContinuousOn h (Ici 1) := by
    refine ContinuousOn.congr ?_ (fun r hr => h_eq (zero_lt_one.trans_le (mem_Ici.mp hr)))
    exact (continuousOn_const.sub (fun r hr =>
      ((c_hasDerivAt (zero_lt_one.trans_le (mem_Ici.mp hr))).continuousAt.const_mul
        (2 : ℝ)).continuousWithinAt)).add
      (ha.mul fun r hr => (thermalLog_hasDerivAt
        (zero_lt_one.trans_le (mem_Ici.mp hr))).continuousAt.continuousWithinAt)
  let J := jumpContribution U m n q
  have hj : ContinuousOn J (Ici 1) := fun r hr =>
    (jumpContribution_hasDerivAt U m n q
      (zero_lt_one.trans_le (mem_Ici.mp hr))).continuousAt.continuousWithinAt
  have hb : ContinuousOn bias (Ici 1) := fun r hr =>
    (bias_hasDerivAt (zero_lt_one.trans_le (mem_Ici.mp hr))).continuousAt.continuousWithinAt
  exact (((hh.mul_const (totalAt m n q)).add
    (ha.mul_const (centeredEntropy (m ^ 3) (n ^ 3) (q ^ 3)))).add hj).add
      (hb.mul_const (spectralCharge U m n q)) |>.congr
      (fun _ hr => normalizedDeficit_eq_jumpContribution U (mem_Ici.mp hr) hm hn hq)

private theorem normalizedDeficit_thermal_differentiable (U : unitary Mat) {m n q r : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hq : 0 ≤ q) (hr : 1 < r) :
    DifferentiableAt ℝ (fun y => normalizedDeficit y U m n q) r ∧
      DifferentiableAt ℝ (deriv (fun y => normalizedDeficit y U m n q)) r := by
  let T := totalAt m n q
  let Q := centeredEntropy (m ^ 3) (n ^ 3) (q ^ 3)
  let J := jumpContribution U m n q
  let C := spectralCharge U m n q
  let F := fun y => h y * T + alpha y * Q + J y + bias y * C
  have heq : (fun y => normalizedDeficit y U m n q) =ᶠ[𝓝 r] F := by
    filter_upwards [lt_mem_nhds hr] with y hy
    exact normalizedDeficit_eq_jumpContribution U hy.le hm hn hq
  let F₁ := fun y => deriv h y * T + deriv alpha y * Q + deriv J y + deriv bias y * C
  have hF (y : ℝ) (hy : 1 < y) : HasDerivAt F (F₁ y) y := by
    have hy₀ := zero_lt_one.trans hy
    have hh := h_hasDerivAt hy
    have ha := alpha_hasDerivAt hy
    have hb := bias_hasDerivAt hy₀
    exact ((((hh.congr_deriv hh.deriv.symm).mul_const T).fun_add
      ((ha.congr_deriv ha.deriv.symm).mul_const Q)).fun_add
      (jumpContribution_hasDerivAt U m n q hy₀)).fun_add
      ((hb.congr_deriv hb.deriv.symm).mul_const C)
  refine ⟨(hF r hr).differentiableAt.congr_of_eventuallyEq heq, ?_⟩
  have hfirst : deriv F =ᶠ[𝓝 r] F₁ := by
    filter_upwards [lt_mem_nhds hr] with y hy
    exact (hF y hy).deriv
  have hr₀ := zero_lt_one.trans hr
  have hdiff : DifferentiableAt ℝ F₁ r :=
    ((((h_second_hasDerivAt hr).mul_const T).fun_add
      ((alpha_second_hasDerivAt hr).mul_const Q)).fun_add
      (jumpContribution_second_hasDerivAt U m n q hr₀)).fun_add
      ((bias_second_hasDerivAt hr₀).mul_const C) |>.differentiableAt
  exact hdiff.congr_of_eventuallyEq (heq.deriv.trans hfirst)

private theorem jumpContribution_curvature_at (U : unitary Mat) (m n q : ℝ)
    {r : ℝ} (hr : 0 < r) :
    deriv (deriv (jumpContribution U m n q)) r =
      deriv (deriv c) r * (∑ i, ∑ j, weight (physicalFrame U) i j *
        (levelsAt m n q i - levelsAt m n q j)^2 * (levelsAt m n q i + levelsAt m n q j)) +
      deriv (deriv e) r * (∑ i, ∑ j, weight (physicalFrame U) i j *
        (levelsAt m n q i - levelsAt m n q j)^3) := by
  let x := levelsAt m n q
  let A := ∑ i, ∑ j, weight (physicalFrame U) i j * (x i - x j)^2 * (x i + x j)
  let B := ∑ i, ∑ j, weight (physicalFrame U) i j * (x i - x j)^3
  rw [jumpContribution_eq]
  change deriv (deriv (fun y => c y * A + e y * B)) r = _
  have hfirst : deriv (fun y => c y * A + e y * B) =ᶠ[𝓝 r]
      (fun y => deriv c y * A + deriv e y * B) := by
    filter_upwards [lt_mem_nhds hr] with y hy
    rw [deriv_fun_add ((c_hasDerivAt hy).mul_const _).differentiableAt
      ((e_hasDerivAt hy).mul_const _).differentiableAt, deriv_mul_const_field',
      deriv_mul_const_field']
  rw [hfirst.deriv_eq, deriv_fun_add ((c_second_hasDerivAt hr).mul_const _).differentiableAt
    ((e_second_hasDerivAt hr).mul_const _).differentiableAt, deriv_mul_const_field',
    deriv_mul_const_field']

private theorem normalizedDeficit_thermal_second_le (U : unitary Mat) {m n q r : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hn : n ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hr : 1 < r) (hhi : r ≤ 6 / 5) :
    deriv (deriv (fun y => normalizedDeficit y U m n q)) r ≤ 80 := by
  let p (x t : ℝ) := x + t * (1 - x)
  let D (t : ℝ) := deriv (deriv
    (fun y => normalizedDeficit y U (p m t) (p n t) (p q t))) r
  have hmem {t x : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
      p x t ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · rcases eq_or_lt_of_le hx.1 with h | h
      · simpa [p, ← h] using ht.1
      · exact h.trans_le (le_add_of_nonneg_right (mul_nonneg ht.1.le (sub_nonneg.mpr hx.2)))
    · change x + t * (1 - x) ≤ 1
      linarith only [mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr hx.2)]
  have hpositive {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : D t ≤ 80 := by
    obtain ⟨hm₀, hm₁⟩ := hmem ht hm
    obtain ⟨hn₀, hn₁⟩ := hmem ht hn
    obtain ⟨hq₀, hq₁⟩ := hmem ht hq
    have hl := lt_min hm₀ (lt_min hn₀ hq₀)
    have hmass : 0 < totalAt (p m t) (p n t) (p q t) := by
      unfold totalAt
      positivity
    exact (normalizedDeficit_second_le U hl ⟨min_le_left _ _, hm₁⟩
      ⟨(min_le_right _ _).trans (min_le_left _ _), hn₁⟩
      ⟨(min_le_right _ _).trans (min_le_right _ _), hq₁⟩ hr hhi hmass le_rfl le_rfl).trans
      (min_le_left _ _)
  let T (t : ℝ) := totalAt (p m t) (p n t) (p q t)
  let x (t : ℝ) := levelsAt (p m t) (p n t) (p q t)
  have hT : Continuous T := by unfold T totalAt p; fun_prop
  have hp (a : ℝ) : Continuous (p a) := by unfold p; fun_prop
  have hx (i : Fin 4) : Continuous (fun t => x t i) := by
    fin_cases i
    · exact hp m
    · exact hp n
    · exact hp q
    · exact continuous_const
  have hentropy : Continuous (fun t => centeredEntropy ((p m t)^3) ((p n t)^3) ((p q t)^3)) := by
    have hlog : Continuous (fun t => T t * Real.log (T t / 4)) := by
      convert (Real.continuous_mul_log.comp (hT.div_const 4)).const_mul (4 : ℝ) using 1
      funext t
      dsimp only [Function.comp_apply]
      ring
    exact ((hlog.sub (Real.continuous_mul_log.comp ((hp m).pow 3))).sub
      (Real.continuous_mul_log.comp ((hp n).pow 3))).sub
      (Real.continuous_mul_log.comp ((hp q).pow 3))
  let F (t : ℝ) :=
    deriv (deriv h) r * T t +
      deriv (deriv alpha) r * centeredEntropy ((p m t)^3) ((p n t)^3) ((p q t)^3) +
      (deriv (deriv c) r * (∑ i, ∑ j, weight (physicalFrame U) i j *
        (x t i - x t j)^2 * (x t i + x t j)) +
       deriv (deriv e) r * (∑ i, ∑ j, weight (physicalFrame U) i j *
        (x t i - x t j)^3)) +
      deriv (deriv bias) r * spectralCharge U (p m t) (p n t) (p q t)
  have hF : Continuous F := by
    unfold F spectralCharge
    fun_prop
  have hmodel {t : ℝ} (hm' : 0 ≤ p m t) (hn' : 0 ≤ p n t) (hq' : 0 ≤ p q t) :
      D t = F t := by
    unfold D F T x
    rw [normalizedDeficit_second_eq U hm' hn' hq' hr,
      jumpContribution_curvature_at U _ _ _ (zero_lt_one.trans hr)]
    simp only [deriv_mul_const_field']
  have hF₀ : F 0 = deriv (deriv (fun y => normalizedDeficit y U m n q)) r := by
    have hp₀ (a : ℝ) : p a 0 = a := by simp [p]
    simpa [D, hp₀] using (hmodel (t := 0) (by simpa only [hp₀] using hm.1)
      (by simpa only [hp₀] using hn.1) (by simpa only [hp₀] using hq.1)).symm
  rw [← hF₀]
  apply le_of_tendsto (hF.continuousAt.continuousWithinAt (s := Ioi (0 : ℝ)))
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  rw [← hmodel (hmem ht hm).1.le (hmem ht hn).1.le (hmem ht hq).1.le]
  exact hpositive ht

private theorem thermal_interpolation_hypotheses (U : unitary Mat) {m n q lo hi : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hn : n ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hlo : 1 ≤ lo) (hhi : hi ≤ 6 / 5) :
    let f := fun t => normalizedDeficit t U m n q
    ContinuousOn f (Icc lo hi) ∧ DifferentiableOn ℝ f (Ioo lo hi) ∧
      DifferentiableOn ℝ (deriv f) (Ioo lo hi) ∧ (∀ t ∈ Ioo lo hi, deriv^[2] f t ≤ 80) := by
  have hdiff (t : ℝ) (ht : t ∈ Ioo lo hi) :=
    normalizedDeficit_thermal_differentiable U hm.1 hn.1 hq.1 (hlo.trans_lt ht.1)
  refine ⟨(normalizedDeficit_thermal_continuousOn U hm.1 hn.1 hq.1).mono
    (fun _ ht => hlo.trans ht.1), fun t ht => (hdiff t ht).1.differentiableWithinAt,
    fun t ht => (hdiff t ht).2.differentiableWithinAt, ?_⟩
  intro t ht
  simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
    normalizedDeficit_thermal_second_le U hm hn hq (hlo.trans_lt ht.1) (ht.2.le.trans hhi)

/-- The fixed-spectrum deficit lies above its thermally corrected chord.
On a singleton interval the chord is its common endpoint value. -/
theorem normalizedDeficit_thermal_chord (U : unitary Mat) {m n q lo hi r : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hn : n ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 6 / 5) (hr : r ∈ Icc lo hi) :
    (if lo = hi then normalizedDeficit lo U m n q else
      ((hi - r) / (hi - lo)) * normalizedDeficit lo U m n q +
        ((r - lo) / (hi - lo)) * normalizedDeficit hi U m n q -
        40 * (r - lo) * (hi - r)) ≤ normalizedDeficit r U m n q := by
  by_cases heq : lo = hi
  · subst hi
    obtain rfl := le_antisymm hr.2 hr.1
    simp
  · rw [ite_eq_right heq]
    obtain ⟨hc, hd, hd', hC⟩ := thermal_interpolation_hypotheses U hm hn hq hlo hhi
    simpa only [show (80 : ℝ) / 2 = 40 by norm_num] using
      corner_interpolation 80 lo hi r (lt_of_le_of_ne hlohi heq) hc hd hd' hC hr.1 hr.2

/-- A common thermal endpoint floor loses at most ten times the squared interval width. -/
theorem normalizedDeficit_thermal_floor (U : unitary Mat) {m n q lo hi r L : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hn : n ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hlo : 1 ≤ lo) (hhi : hi ≤ 6 / 5) (hr : r ∈ Icc lo hi)
    (hleft : L ≤ normalizedDeficit lo U m n q) (hright : L ≤ normalizedDeficit hi U m n q) :
    L - 10 * (hi - lo)^2 ≤ normalizedDeficit r U m n q := by
  obtain ⟨hc, hd, hd', hC⟩ := thermal_interpolation_hypotheses U hm hn hq hlo hhi
  convert corner_floor 80 lo hi r L (hr.1.trans hr.2) hc hd hd' hC (by norm_num)
    hleft hright hr.1 hr.2 using 1
  ring

/-- The sixteen corner bounds give a floor on the full closed thermal and level box.
The left index selects the thermal coordinate and the right indices select the three levels. -/
theorem normalizedDeficit_box_floor (U : unitary Mat) {lo hi x : Sum Unit (Fin 3) → ℝ}
    {L : ℝ} (hlo : 1 ≤ lo (.inl ())) (hhi : hi (.inl ()) ≤ 6 / 5)
    (hloLevel : ∀ i, 0 ≤ lo (.inr i)) (hhiLevel : ∀ i, hi (.inr i) ≤ 1)
    (hx : ∀ i, x i ∈ Icc (lo i) (hi i))
    (hcorner : ∀ ε : Sum Unit (Fin 3) → Bool,
      let y := boxCorner lo hi ε
      L + 10 * (hi (.inl ()) - lo (.inl ()))^2 + 3 * (∑ i : Fin 3, (hi (.inr i) - lo (.inr i))^2) ≤
        normalizedDeficit (y (.inl ())) U (y (.inr 0)) (y (.inr 1)) (y (.inr 2))) :
    L ≤ normalizedDeficit (x (.inl ())) U (x (.inr 0)) (x (.inr 1)) (x (.inr 2)) := by
  let f (y : Sum Unit (Fin 3) → ℝ) :=
    normalizedDeficit (y (.inl ())) U (y (.inr 0)) (y (.inr 1)) (y (.inr 2))
  let loss (i : Sum Unit (Fin 3)) : ℝ :=
    (Sum.elim (fun _ => (10 : ℝ)) (fun _ => (3 : ℝ)) i) * (hi i - lo i)^2
  refine finite_box_floor f lo hi loss x L hx ?_ ?_
  · intro ε
    simpa only [Fintype.sum_sum_type, Fintype.sum_unique, loss, Sum.elim_inl, Sum.elim_inr,
      Finset.mul_sum, add_assoc, f] using hcorner ε
  · intro y hy i
    have hlevels (k : Fin 3) : y (.inr k) ∈ Icc (0 : ℝ) 1 :=
      ⟨(hloLevel k).trans (hy (.inr k)).1, (hy (.inr k)).2.trans (hhiLevel k)⟩
    rcases i with ⟨⟨⟩⟩ | k
    · have hslice (t : ℝ) : f (Function.update y (.inl ()) t) =
          normalizedDeficit t U (y (.inr 0)) (y (.inr 1)) (y (.inr 2)) := by
        simp [f, Function.update_of_ne]
      simp only [hslice, loss, Sum.elim_inl]
      exact normalizedDeficit_thermal_floor U (hlevels 0) (hlevels 1) (hlevels 2)
        hlo hhi (hy (.inl ())) (min_le_left _ _) (min_le_right _ _)
    · let z : Fin 3 → ℝ := fun j => y (.inr j)
      have hslice (t : ℝ) : f (Function.update y (.inr k) t) =
          levelSlice (y (.inl ())) U z k t := by
        simp [f, levelSlice, z, Function.update_apply]
      have ht : y (.inl ()) ∈ Icc (1 : ℝ) (6 / 5) :=
        ⟨hlo.trans (hy (.inl ())).1, (hy (.inl ())).2.trans hhi⟩
      have hself : levelSlice (y (.inl ())) U z k (z k) = f y := by
        simp [levelSlice, f, Function.update_eq_self, z]
      simp only [hslice, loss, Sum.elim_inr]
      rw [← hself]
      exact levelSlice_floor U ht hlevels k (hloLevel k) (hhiLevel k) (hy (.inr k))
        (min_le_left _ _) (min_le_right _ _)

open private logCoordinate from D5.S3.Quantum.Semigroups.WuCubicBoundaryCorner

private theorem shellLeft_normalizedDeficit (U : unitary Mat) :
    (3 / 400 : ℝ) ≤ normalizedDeficit (1199 / 1000) U (63 / 100) (3 / 4) (9 / 10) := by
  let r : ℝ := 1199 / 1000
  let m : ℝ := 63 / 100
  let n : ℝ := 3 / 4
  let q : ℝ := 9 / 10
  let L := lowerCoeff r m n q / 2
  let R := upperCoeff r n q / 2
  have hL : L ∈ Icc 0 (lowerCoeff r m n q) := by
    norm_num [L, r, m, n, q, lowerCoeff, crossCoeff, directedCoeff, c, e, gamma]
  have hR : R ∈ Icc 0 (upperCoeff r n q) := by
    norm_num [R, r, n, q, upperCoeff, crossCoeff, directedCoeff, c, e, gamma]
  have hcharges : (0 : ℝ) ∈ Icc 0 (cutBias r m n q 0) ∧
      (0 : ℝ) ∈ Icc 0 (cutBias r m n q 2) := by
    norm_num [r, m, n, q, cutBias, cutB, bias, e, gamma]
  have hmargin : (3 / 400 : ℝ) ≤ cornerLower r m n q L R 0 0 := by
    norm_num [r, m, n, q, L, R, cornerLower, thermalCenterLower, entropyLower, massLogUpper,
      thermalBase, thermalFactor, gibbsArgument, gibbsLow, gibbsHigh, totalAt, logLower, logUpper,
      logRatioLower, logRatioUpper, logSeries, logCoordinate, Finset.sum_range_succ,
      cutEnergy, cutBias, cutA, cutB, lowerCoeff, upperCoeff, longCoeff, crossCoeff,
      directedCoeff, c, e, bias, gamma, imbalanceSliceMin, squareSliceMin, squareBoundaryMin,
      squareEdgeMin, min_def]
  exact hmargin.trans (cornerLower_le_normalizedDeficit U (by norm_num [r]) (by norm_num [m])
    (by norm_num [m, n]) (by norm_num [n, q]) (by norm_num [q]) hL hR hcharges.1 hcharges.2)

/-- The left corner surplus pays the full chord correction on the shell
interval, preserving the right corner's positive margin. -/
theorem shellThermalInterval_normalizedDeficit (U : unitary Mat) {r : ℝ}
    (hr : r ∈ Icc (1199 / 1000 : ℝ) (6 / 5)) :
    (7 / 1000 : ℝ) ≤ normalizedDeficit r U (63 / 100) (3 / 4) (9 / 10) := by
  let lo : ℝ := 1199 / 1000
  let hi : ℝ := 6 / 5
  let a := (hi - r) / (hi - lo)
  let b := (r - lo) / (hi - lo)
  have hw : 0 ≤ hi - lo := by norm_num [hi, lo]
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hr.2) hw
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hr.1) hw
  have hchord := normalizedDeficit_thermal_chord U (m := 63 / 100) (n := 3 / 4) (q := 9 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl hr
  rw [ite_eq_right (by norm_num : (1199 / 1000 : ℝ) ≠ 6 / 5)] at hchord
  have hlinear := add_le_add (mul_le_mul_of_nonneg_left (shellLeft_normalizedDeficit U) ha)
    (mul_le_mul_of_nonneg_left (shellCorner_normalizedDeficit U) hb)
  have hmargin : (7 / 1000 : ℝ) ≤ a * (3 / 400) + b * (7 / 1000) -
      40 * (r - lo) * (hi - r) := by
    have hspan : 0 ≤ hi - r := sub_nonneg.mpr hr.2
    calc
      (7 / 1000 : ℝ) ≤ 7 / 1000 + ((23 / 50) * (hi - r) + 40 * (hi - r) ^ 2) :=
        le_add_of_nonneg_right (add_nonneg (mul_nonneg (by norm_num) hspan)
          (mul_nonneg (by norm_num) (sq_nonneg _)))
      _ = _ := by
        dsimp only [a, b, lo, hi]
        ring
  exact hmargin.trans ((sub_le_sub_right hlinear _).trans hchord)

#print axioms normalizedDeficit_thermal_chord
#print axioms normalizedDeficit_thermal_floor
#print axioms normalizedDeficit_box_floor
#print axioms shellThermalInterval_normalizedDeficit

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrumThermalInterpolation
