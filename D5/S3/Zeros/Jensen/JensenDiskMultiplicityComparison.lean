/- GID: D5/S3/Zeros/Jensen/JensenDiskMultiplicityComparison
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/JensenDiskMultiplicityComparison
   mirror-E: none(waiver:consumed-fixed-window-construction)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.CircleIntegral]
   utility: none
   digest: Analytic units and a boundary logarithm compare polynomial root occurrences on the original disk. -/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
open Set Filter Polynomial Metric
open scoped Topology

private theorem glued_unit (F : ℂ → ℂ) (c : ℂ) (delta : ℝ) (m : ℕ)
    (hd : 0 < delta) (hm : 1 ≤ m) (hF : AnalyticOnNhd ℂ F (closedBall c delta))
    (ho : analyticOrderAt F c = m)
    (hi : ∀ z ∈ closedBall c delta, z ≠ c → F z ≠ 0) :
    ∃ U : ℂ → ℂ, AnalyticOnNhd ℂ U (closedBall c delta) ∧
      (∀ z ∈ closedBall c delta, U z ≠ 0) ∧ ∀ z, F z = (z - c) ^ m * U z := by
  classical
  obtain ⟨V, hVa, hV0, hV⟩ :=
    (hF c (mem_closedBall_self hd.le)).analyticOrderAt_eq_natCast.mp ho
  have hFc : F c = 0 := by
    simpa [smul_eq_mul, zero_pow (show m ≠ 0 by omega)] using hV.self_of_nhds
  let U : ℂ → ℂ := fun z => if z = c then V c else F z / (z - c) ^ m
  have hUV : V =ᶠ[𝓝 c] U := by
    filter_upwards [hV] with z hz
    by_cases hzc : z = c
    · simp [U, hzc]
    · have hz0 : (z - c) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzc)
      dsimp [U]
      rw [if_neg hzc, hz, smul_eq_mul, mul_div_cancel_left₀ _ hz0]
  have hUa : AnalyticOnNhd ℂ U (closedBall c delta) := by
    intro z hz
    by_cases hzc : z = c
    · subst z; exact hVa.congr hUV
    · have ha : AnalyticAt ℂ (fun w => F w / (w - c) ^ m) z :=
        (hF z hz).div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hzc))
      apply ha.congr
      filter_upwards [eventually_ne_nhds hzc] with w hw
      simp [U, hw]
  refine ⟨U, hUa, ?_, ?_⟩
  · intro z hz
    by_cases hzc : z = c
    · simpa [U, hzc] using hV0
    · simpa [U, hzc] using div_ne_zero (hi z hz hzc)
        (pow_ne_zero _ (sub_ne_zero.mpr hzc))
  · intro z
    by_cases hzc : z = c
    · simp [hzc, hFc, zero_pow (show m ≠ 0 by omega)]
    · simp only [U, if_neg hzc]
      exact (mul_div_cancel₀ (F z) (pow_ne_zero _ (sub_ne_zero.mpr hzc))).symm

private theorem boundary_log_comparison (F : ℂ → ℂ) (P : ℂ[X]) (c : ℂ) (delta : ℝ)
    (hd : 0 < delta) (hF : AnalyticOnNhd ℂ F (closedBall c delta))
    (hFn : ∀ z ∈ sphere c delta, F z ≠ 0)
    (hclose : ∀ z ∈ sphere c delta, ‖P.eval z - F z‖ < ‖F z‖) :
    (∀ z ∈ sphere c delta, P.eval z ≠ 0) ∧
      (∮ z in C(c, delta), P.derivative.eval z / P.eval z) =
        ∮ z in C(c, delta), deriv F z / F z := by
  have hPn : ∀ z ∈ sphere c delta, P.eval z ≠ 0 := by
    intro z hz hp
    have h := hclose z hz
    rw [hp, zero_sub, norm_neg] at h
    exact (lt_irrefl _ h)
  let q : ℂ → ℂ := fun z => P.eval z / F z
  let L : ℂ → ℂ := fun z => Complex.log (q z)
  have hq (z : ℂ) (hz : z ∈ sphere c delta) : q z ∈ Complex.slitPlane := by
    have hFz := hFn z hz
    have he : q z - 1 = (P.eval z - F z) / F z := by dsimp [q]; field_simp
    have hsmall : ‖q z - 1‖ < 1 := by
      rw [he, norm_div]
      exact (div_lt_one (norm_pos_iff.mpr hFz)).mpr (hclose z hz)
    simpa only [add_sub_cancel] using Complex.mem_slitPlane_of_norm_lt_one hsmall
  have hL (z : ℂ) (hz : z ∈ sphere c delta) :
      HasDerivAt L (P.derivative.eval z / P.eval z - deriv F z / F z) z := by
    have hFz := hFn z hz
    have hPz := hPn z hz
    have hFd := (hF z (sphere_subset_closedBall hz)).differentiableAt.hasDerivAt
    have hqd := (P.hasDerivAt z).div hFd hFz
    convert hqd.clog (hq z hz) using 1 <;>
      dsimp [L, q, Pi.div_def] <;> field_simp [hPz, hFz] <;> ring
  have hPc : ContinuousOn (fun z => P.derivative.eval z / P.eval z) (sphere c delta) :=
    P.derivative.continuous.continuousOn.div P.continuous.continuousOn hPn
  have hFc : ContinuousOn (fun z => deriv F z / F z) (sphere c delta) :=
    (hF.deriv.continuousOn.mono sphere_subset_closedBall).div
      (hF.continuousOn.mono sphere_subset_closedBall) hFn
  have hiP := hPc.circleIntegrable hd.le
  have hiF := hFc.circleIntegrable hd.le
  have hiDiff := (hPc.sub hFc).circleIntegrable hd.le
  have hzero := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hd.le
    (fun z hz => (hL z hz).hasDerivWithinAt)
  rw [circleIntegral.integral_sub hiP hiF] at hzero
  exact ⟨hPn, sub_eq_zero.mp hzero⟩

private theorem unit_log_count (F U : ℂ → ℂ) (c : ℂ) (delta : ℝ) (m : ℕ)
    (hd : 0 < delta) (hUa : AnalyticOnNhd ℂ U (closedBall c delta))
    (hUn : ∀ z ∈ closedBall c delta, U z ≠ 0)
    (hf : ∀ z, F z = (z - c) ^ m * U z) :
    (∮ z in C(c, delta), deriv F z / F z) = (2 * Real.pi * Complex.I) * m := by
  have hunit : AnalyticOnNhd ℂ (fun z => deriv U z / U z) (closedBall c delta) :=
    hUa.deriv.div hUa hUn
  have hzero : (∮ z in C(c, delta), deriv U z / U z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hd.le
      (s := ∅) Set.countable_empty hunit.continuousOn
      (fun z hz => (hunit z (ball_subset_closedBall hz.1)).differentiableAt)
  have he (z : ℂ) (hz : z ∈ sphere c delta) :
      deriv F z / F z = (m : ℂ) * (z - c)⁻¹ + deriv U z / U z := by
    have hzc : z ≠ c := by
      intro he; subst z
      have : (0 : ℝ) = delta := by simpa using mem_sphere_iff_norm.mp hz
      linarith
    have hu := hUn z (sphere_subset_closedBall hz)
    have hz0 := sub_ne_zero.mpr hzc
    have hdF := (((hasDerivAt_id z).sub_const c).pow m).mul
      (hUa z (sphere_subset_closedBall hz)).differentiableAt.hasDerivAt
    change HasDerivAt (fun w => (w - c) ^ m * U w)
      ((m : ℂ) * (z - c) ^ (m - 1) * 1 * U z + (z - c) ^ m * deriv U z) z at hdF
    have hFe : F = fun z => (z - c) ^ m * U z := funext hf
    rw [hFe, hdF.deriv]
    by_cases hm : m = 0
    · simp [hm]
    · have hp : (z - c) ^ m = (z - c) ^ (m - 1) * (z - c) := by
        rw [← pow_succ]; congr 1; omega
      simp only [id_eq, sub_zero, mul_one]
      rw [hp]
      field_simp [hu, hz0, pow_ne_zero (m - 1) hz0]
      <;> ring
  rw [circleIntegral.integral_congr hd.le he]
  have hc : ContinuousOn (fun z : ℂ => (m : ℂ) * (z - c)⁻¹) (sphere c delta) := by
    apply continuousOn_const.mul
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz he
    change z - c = 0 at he
    have := mem_sphere_iff_norm.mp hz
    rw [he, norm_zero] at this
    linarith
  rw [circleIntegral.integral_add (hc.circleIntegrable hd.le)
    (hunit.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hd.le), hzero,
    add_zero, circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv _ hd.ne']
  ring

private theorem polynomial_log_count (P : ℂ[X]) (c : ℂ) (delta : ℝ)
    (hd : 0 < delta) (hP : P ≠ 0) (hPn : ∀ z ∈ sphere c delta, P.eval z ≠ 0) :
    (∮ z in C(c, delta), P.derivative.eval z / P.eval z) =
      (2 * Real.pi * Complex.I) * (P.roots.filter (fun z => ‖z - c‖ < delta)).card := by
  classical
  have hroot (a : ℂ) (ha : a ∈ P.roots) : a ∉ sphere c delta := by
    intro hb
    exact hPn a hb ((Polynomial.mem_roots hP).mp ha)
  have hi (a : ℂ) (ha : a ∈ P.roots) : CircleIntegrable (fun z => (z - a)⁻¹) c delta := by
    apply ContinuousOn.circleIntegrable hd.le
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz he
    change z - a = 0 at he
    exact hroot a ha (sub_eq_zero.mp he ▸ hz)
  have haint (a : ℂ) (ha : a ∈ P.roots) :
      (∮ z in C(c, delta), (z - a)⁻¹) =
        if ‖a - c‖ < delta then (2 * Real.pi * Complex.I) else 0 := by
    split_ifs with hb
    · exact circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_iff_norm.mpr hb)
    · have hn : a ∉ closedBall c delta := by
        intro hc
        have hle := mem_closedBall_iff_norm.mp hc
        have he := le_antisymm hle (le_of_not_gt hb)
        exact hroot a ha (mem_sphere_iff_norm.mpr he)
      have han : AnalyticOnNhd ℂ (fun z : ℂ => (z - a)⁻¹) (closedBall c delta) := by
        intro z hz
        exact (analyticAt_id.sub analyticAt_const).inv
          (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hn))
      exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hd.le
        (s := ∅) Set.countable_empty han.continuousOn
        (fun z hz => (han z (ball_subset_closedBall hz.1)).differentiableAt)
  have hsum_integrable : ∀ s : Multiset ℂ, s ≤ P.roots →
      CircleIntegrable (fun z => (s.map (fun a => (z - a)⁻¹)).sum) c delta := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _
      simpa using (continuousOn_const.circleIntegrable hd.le :
        CircleIntegrable (fun _ : ℂ => (0 : ℂ)) c delta)
    | @cons a s ih =>
      intro hsub
      simpa only [Multiset.map_cons, Multiset.sum_cons, Pi.add_def] using
        (hi a (Multiset.mem_of_le hsub (by simp))).add
          (ih ((Multiset.le_cons_self _ _).trans hsub))
  have hs : ∀ s : Multiset ℂ, s ≤ P.roots →
      (∮ z in C(c, delta), (s.map (fun a => (z - a)⁻¹)).sum) =
        (2 * Real.pi * Complex.I) * (s.filter (fun a => ‖a - c‖ < delta)).card := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp [circleIntegral]
    | @cons a s ih =>
      intro hsub
      have ha : a ∈ P.roots := Multiset.mem_of_le hsub (by simp)
      have hs : s ≤ P.roots := le_trans (Multiset.le_cons_self _ _) hsub
      have his := hsum_integrable s hs
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [circleIntegral.integral_add (hi a ha) his, haint a ha, ih hs]
      by_cases hb : ‖a - c‖ < delta <;>
        simp [hb, mul_add, Nat.cast_add, Nat.cast_one, add_comm]
  have he (z : ℂ) (hz : P.eval z ≠ 0) :=
    (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hz
  calc
    _ = (∮ z in C(c, delta), (P.roots.map (fun a => (z - a)⁻¹)).sum) :=
      circleIntegral.integral_congr hd.le (fun z hz => by
        simpa only [one_div] using he z (hPn z hz))
    _ = _ := hs P.roots le_rfl

private theorem retained_disk_count (F : ℂ → ℂ) (P : ℂ[X]) (c : ℂ)
    (delta : ℝ) (m : ℕ) (hd : 0 < delta) (hm : 1 ≤ m)
    (hF : AnalyticOnNhd ℂ F (closedBall c delta)) (ho : analyticOrderAt F c = m)
    (hi : ∀ z ∈ closedBall c delta, z ≠ c → F z ≠ 0)
    (he : ∀ z ∈ sphere c delta, ‖P.eval z - F z‖ < ‖F z‖) :
    P ≠ 0 ∧ (∀ z ∈ sphere c delta, P.eval z ≠ 0) ∧
      (P.roots.filter (fun z => ‖z - c‖ < delta)).card = m := by
  have hFn : ∀ z ∈ sphere c delta, F z ≠ 0 := by
    intro z hz
    apply hi z (sphere_subset_closedBall hz)
    intro heq; subst z
    have := mem_sphere_iff_norm.mp hz
    simp only [sub_self, norm_zero] at this
    linarith
  obtain ⟨hPn, hcomp⟩ := boundary_log_comparison F P c delta hd hF hFn he
  have hP : P ≠ 0 := by
    intro hp
    have hb : c + (delta : ℂ) ∈ sphere c delta := by
      simp [mem_sphere_iff_norm, abs_of_pos hd]
    exact hPn _ hb (by simp [hp])
  obtain ⟨U, hUa, hUn, hf⟩ := glued_unit F c delta m hd hm hF ho hi
  have hpint := polynomial_log_count P c delta hd hP hPn
  have hfint := unit_log_count F U c delta m hd hUa hUn hf
  have hmul := hpint.symm.trans (hcomp.trans hfint)
  have hconst : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  exact ⟨hP, hPn, Nat.cast_injective (mul_left_cancel₀ hconst hmul)⟩

end D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
