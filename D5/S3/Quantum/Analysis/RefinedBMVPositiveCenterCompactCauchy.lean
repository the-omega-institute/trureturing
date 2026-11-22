/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterCompactCauchy
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cauchy bounds for the centered short-gap Taylor replay. -/

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The Cauchy remainder of the short-gap chart -/

open Metric
open scoped BigOperators Topology

namespace RefinedBMV.PositiveCenter.CompactGap

/-- At radial parameter one, the first omitted Taylor coefficient has index 15.
Cauchy's estimate on the circle of radius $7/2$ bounds the omitted series
by the geometric series with ratio $2/7$. -/
theorem shortGap_taylorRemainder_le {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 (7 / 2)))
    (hbound : ∀ w ∈ sphere (0 : ℂ) (7 / 2), ‖f w‖ ≤ (2 : ℝ) ^ 21) :
    ‖f 1 - ∑ n ∈ Finset.range 15, iteratedDeriv n f 0 / (n.factorial : ℂ)‖ ≤
      (2 : ℝ) ^ 36 / (5 * 7 ^ 14) := by
  have h₁ : (1 : ℂ) ∈ ball 0 (7 / 2) := by
    norm_num [mem_ball, dist_zero_right]
  have hSeries :
      HasSum (fun n : ℕ ↦ iteratedDeriv n f 0 / (n.factorial : ℂ)) (f 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      Complex.hasSum_taylorSeries_on_ball hf.differentiableOn h₁
  have hTail := (hasSum_nat_add_iff' 15).2 hSeries
  have hGeom : HasSum (fun n : ℕ ↦ (2 : ℝ) ^ 21 * (2 / 7) ^ (n + 15))
      ((2 : ℝ) ^ 36 / (5 * 7 ^ 14)) := by
    have h := (hasSum_geometric_of_lt_one (r := (2 : ℝ) / 7) (by norm_num)
      (by norm_num)).mul_left ((2 : ℝ) ^ 21 * (2 / 7) ^ 15)
    convert h using 1
    · ext n
      rw [pow_add]
      ring
    · norm_num
  refine hTail.norm_le_of_bounded hGeom fun n ↦ ?_
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (n + 15) (by norm_num : 0 < (7 / 2 : ℝ)) hf hbound
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  calc
    ‖iteratedDeriv (n + 15) f 0‖ ≤
        ((n + 15).factorial : ℝ) * (2 : ℝ) ^ 21 / (7 / 2 : ℝ) ^ (n + 15) := hc
    _ = (2 : ℝ) ^ 21 * (2 / 7) ^ (n + 15) * ((n + 15).factorial : ℝ) := by
      rw [div_eq_mul_inv, ← inv_pow, show (7 / 2 : ℝ)⁻¹ = 2 / 7 by norm_num]
      ring

/-- Apply the remainder bound to the homogeneous sums supplied by coefficient lookup.
At the fixed chart point, the lookup is needed only through degree 14. -/
theorem shortGap_taylorRemainder_le_of_lookup {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 (7 / 2)))
    (hbound : ∀ w ∈ sphere (0 : ℂ) (7 / 2), ‖f w‖ ≤ (2 : ℝ) ^ 21)
    (hlookup : ∀ n < 15, a n = iteratedDeriv n f 0 / (n.factorial : ℂ)) :
    ‖f 1 - ∑ n ∈ Finset.range 15, a n‖ ≤ (2 : ℝ) ^ 36 / (5 * 7 ^ 14) := by
  have hpoly : ∑ n ∈ Finset.range 15, a n =
      ∑ n ∈ Finset.range 15, iteratedDeriv n f 0 / (n.factorial : ℂ) :=
    Finset.sum_congr rfl fun n hn ↦ hlookup n (Finset.mem_range.mp hn)
  rw [hpoly]
  exact shortGap_taylorRemainder_le hf hbound

/-- Coordinates in the order lower coordinate, gap, and parameter, with the max norm. -/
abbrev ShortGapChart := ℂ × ℂ × ℂ

private def chartU : ShortGapChart := (1, 0, 0)
private def chartD : ShortGapChart := (0, 1, 0)

private noncomputable def chartPartial (F : ShortGapChart → ℂ) (e p : ShortGapChart) : ℂ :=
  fderiv ℂ F p e

/-- The replay differential expression acting on a function of unit chart coordinates.
The radii convert the normalized coordinate derivatives to derivatives in the
independent lower coordinate and gap. -/
noncomputable def chartGapDerivative (F : ShortGapChart → ℂ) (ru rd : ℝ)
    (p : ShortGapChart) : ℂ :=
  chartPartial (chartPartial F chartD) chartU p / ((ru : ℂ) * (rd : ℂ)) -
    chartPartial (chartPartial F chartD) chartD p / (rd : ℂ) ^ 2 -
    chartPartial F chartU p / (2 * (ru : ℂ)) +
    chartPartial F chartD p / (rd : ℂ) - F p / 4

private theorem analyticOnNhd_chartPartial {F : ShortGapChart → ℂ} {s : Set ShortGapChart}
    (hF : AnalyticOnNhd ℂ F s) (e : ShortGapChart) :
    AnalyticOnNhd ℂ (chartPartial F e) s := by
  intro p hp
  exact ((ContinuousLinearMap.apply ℂ ℂ e).analyticAt _).comp (hF.fderiv p hp)

private theorem analyticOnNhd_chartGapDerivative {F : ShortGapChart → ℂ}
    {s : Set ShortGapChart} (hF : AnalyticOnNhd ℂ F s) (ru rd : ℝ) :
    AnalyticOnNhd ℂ (chartGapDerivative F ru rd) s := by
  have hu := analyticOnNhd_chartPartial hF chartU
  have hd := analyticOnNhd_chartPartial hF chartD
  have hud := analyticOnNhd_chartPartial hd chartU
  have hdd := analyticOnNhd_chartPartial hd chartD
  exact (((hud.div_const.sub hdd.div_const).sub hu.div_const).add hd.div_const).sub
    hF.div_const

private theorem analyticOnNhd_chartLine {F : ShortGapChart → ℂ} {s : Set ShortGapChart}
    {p e : ShortGapChart} {r : ℝ} (hF : AnalyticOnNhd ℂ F s)
    (hline : ∀ w ∈ closedBall (0 : ℂ) r, p + w • e ∈ s) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ F (p + w • e)) (closedBall 0 r) := by
  intro w hw
  have h : AnalyticAt ℂ (fun z : ℂ ↦ p + z • e) w := by fun_prop
  exact AnalyticAt.comp (f := fun z : ℂ ↦ p + z • e) (x := w) (hF _ (hline w hw)) h

private theorem diffContOnCl_of_analyticOnNhd_closedBall {f : ℂ → ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) : DiffContOnCl ℂ f (ball 0 r) :=
  (hf.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl

private theorem deriv_chartLine {F : ShortGapChart → ℂ} {p e : ShortGapChart} {w : ℂ}
    (hF : DifferentiableAt ℂ F (p + w • e)) :
    deriv (fun z : ℂ ↦ F (p + z • e)) w = chartPartial F e (p + w • e) := by
  have hline : HasDerivAt (fun z : ℂ ↦ p + z • e) e w := by
    simpa using ((hasDerivAt_id' w).smul_const e).const_add p
  exact (hF.hasFDerivAt.comp_hasDerivAt w hline).deriv

private theorem norm_chartPartial_le {F : ShortGapChart → ℂ} {s : Set ShortGapChart}
    {p e : ShortGapChart} {M : ℝ}
    (hF : AnalyticOnNhd ℂ F s) (hM : ∀ q ∈ s, ‖F q‖ ≤ M)
    (hline : ∀ w ∈ closedBall (0 : ℂ) (1 / 2), p + w • e ∈ s) :
    ‖chartPartial F e p‖ ≤ M / (1 / 2) := by
  have ha := analyticOnNhd_chartLine hF hline
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) (1 / 2) := by norm_num [mem_closedBall]
  have hF0 := (hF _ (hline 0 h0)).differentiableAt
  have heq := deriv_chartLine (p := p) (e := e) (w := 0) hF0
  simp only [zero_smul, add_zero] at heq
  rw [← heq]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
    (diffContOnCl_of_analyticOnNhd_closedBall ha)
    fun w hw ↦ hM _ (hline w (sphere_subset_closedBall hw))

private theorem norm_chartPartial_twice_le {F : ShortGapChart → ℂ} {s : Set ShortGapChart}
    {p e : ShortGapChart} {M : ℝ}
    (hF : AnalyticOnNhd ℂ F s) (hM : ∀ q ∈ s, ‖F q‖ ≤ M)
    (hline : ∀ w ∈ closedBall (0 : ℂ) (1 / 2), p + w • e ∈ s) :
    ‖chartPartial (chartPartial F e) e p‖ ≤ 2 * M / (1 / 2) ^ 2 := by
  have ha := analyticOnNhd_chartLine hF hline
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) (1 / 2) := by norm_num [mem_closedBall]
  have hF0 := (analyticOnNhd_chartPartial hF e _ (hline 0 h0)).differentiableAt
  have heq := deriv_chartLine (p := p) (e := e) (w := 0) hF0
  simp only [zero_smul, add_zero] at heq
  have hnear : deriv (fun z : ℂ ↦ F (p + z • e)) =ᶠ[𝓝 0]
      (fun w ↦ chartPartial F e (p + w • e)) := by
    filter_upwards [closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    exact deriv_chartLine (hF _ (hline w hw)).differentiableAt
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := fun z : ℂ ↦ F (p + z • e)) 2 (by norm_num : (0 : ℝ) < 1 / 2)
    (diffContOnCl_of_analyticOnNhd_closedBall ha)
    fun w hw ↦ hM _ (hline w (sphere_subset_closedBall hw))
  rw [← heq, ← hnear.deriv_eq]
  simpa [iteratedDeriv_succ] using hc

private theorem chart_add_smul_mem {p e : ShortGapChart} {w : ℂ}
    (hp : ‖p‖ ≤ 7 / 2) (he : ‖e‖ ≤ 1) (hw : w ∈ closedBall 0 (1 / 2)) :
    p + w • e ∈ closedBall (0 : ShortGapChart) 4 := by
  rw [mem_closedBall_zero_iff] at hw ⊢
  calc
    ‖p + w • e‖ ≤ ‖p‖ + ‖w • e‖ := norm_add_le _ _
    _ ≤ 7 / 2 + (1 / 2) * 1 :=
      add_le_add hp (by rw [norm_smul]; gcongr)
    _ = 4 := by norm_num

private theorem chart_two_shifts_mem {p : ShortGapChart} {w z : ℂ}
    (hp : ‖p‖ ≤ 7 / 2) (hw : w ∈ closedBall 0 (1 / 2)) (hz : z ∈ closedBall 0 (1 / 2)) :
    p + w • chartU + z • chartD ∈ closedBall (0 : ShortGapChart) 4 := by
  rw [mem_closedBall_zero_iff] at hw hz ⊢
  have hshift : p + w • chartU + z • chartD = (p.1 + w, p.2.1 + z, p.2.2) := by
    ext <;> simp [chartU, chartD, smul_eq_mul]
  rw [hshift]
  simp only [norm_prod_le_iff] at hp ⊢
  refine ⟨(norm_add_le _ _).trans ?_, (norm_add_le _ _).trans ?_, hp.2.2.trans ?_⟩
  · linarith [hp.1]
  · linarith [hp.2.1]
  · norm_num

/-- The two coordinate circles for the mixed derivative fit simultaneously in the
radius-four polydisc. The pure second derivative uses the factorial in Cauchy's estimate. -/
theorem norm_chartGapDerivative_le {F : ShortGapChart → ℂ} {p : ShortGapChart}
    {ru rd : ℝ} (hru : 0 < ru) (hrd : 0 < rd)
    (hF : AnalyticOnNhd ℂ F (closedBall 0 4))
    (hM : ∀ q ∈ closedBall (0 : ShortGapChart) 4, ‖F q‖ ≤ 512)
    (hp : ‖p‖ ≤ 7 / 2) :
    ‖chartGapDerivative F ru rd p‖ ≤
      512 * (4 / (ru * rd) + 8 / rd ^ 2 + 1 / ru + 2 / rd + 1 / 4) := by
  have hu : ‖chartU‖ ≤ 1 := by simp [chartU]
  have hd : ‖chartD‖ ≤ 1 := by simp [chartD]
  have hFu := norm_chartPartial_le hF hM (fun _ hw ↦ chart_add_smul_mem hp hu hw)
  have hFd := norm_chartPartial_le hF hM (fun _ hw ↦ chart_add_smul_mem hp hd hw)
  have hFdd := norm_chartPartial_twice_le hF hM (fun _ hw ↦ chart_add_smul_mem hp hd hw)
  have hFud : ‖chartPartial (chartPartial F chartD) chartU p‖ ≤ (512 / (1 / 2)) / (1 / 2) := by
    let s := (fun w : ℂ ↦ p + w • chartU) '' closedBall (0 : ℂ) (1 / 2)
    have hsub : s ⊆ closedBall (0 : ShortGapChart) 4 := by
      rintro _ ⟨w, hw, rfl⟩
      exact chart_add_smul_mem hp hu hw
    refine norm_chartPartial_le ((analyticOnNhd_chartPartial hF chartD).mono hsub)
      ?_ (fun w hw ↦ ⟨w, hw, rfl⟩)
    rintro _ ⟨w, hw, rfl⟩
    exact norm_chartPartial_le hF hM (fun _ hz ↦ chart_two_shifts_mem hp hw hz)
  have hFp := hM p (mem_closedBall_zero_iff.mpr (hp.trans (by norm_num)))
  unfold chartGapDerivative
  calc
    _ ≤ ‖chartPartial (chartPartial F chartD) chartU p / ((ru : ℂ) * (rd : ℂ))‖ +
        ‖chartPartial (chartPartial F chartD) chartD p / (rd : ℂ) ^ 2‖ +
        ‖chartPartial F chartU p / (2 * (ru : ℂ))‖ +
        ‖chartPartial F chartD p / (rd : ℂ)‖ + ‖F p / 4‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ((512 / (1 / 2)) / (1 / 2)) / (ru * rd) + (2 * 512 / (1 / 2) ^ 2) / rd ^ 2 +
        (512 / (1 / 2)) / (2 * ru) + (512 / (1 / 2)) / rd + 512 / 4 := by
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hru, abs_of_pos hrd, Complex.norm_ofNat]
      gcongr
    _ = _ := by ring

/-- The degree-fourteen chart polynomial is evaluated by summing the lookup values
of its homogeneous pieces at the chosen unit-box point. -/
theorem shortGap_chartRemainder_le {F : ShortGapChart → ℂ} {x : ShortGapChart}
    {ru : ℝ} {a : ℕ → ℂ} (hru : ru = 1 / 8 ∨ ru = 1 / 4)
    (hF : AnalyticOnNhd ℂ F (closedBall 0 4))
    (hM : ∀ q ∈ closedBall (0 : ShortGapChart) 4, ‖F q‖ ≤ 512)
    (hx : ‖x‖ ≤ 1)
    (hlookup : ∀ n < 15, a n = iteratedDeriv n
      (fun w : ℂ ↦ chartGapDerivative F ru (1 / 16) (w • x)) 0 / (n.factorial : ℂ)) :
    ‖chartGapDerivative F ru (1 / 16) x - ∑ n ∈ Finset.range 15, a n‖ ≤
      (2 : ℝ) ^ 36 / (5 * 7 ^ 14) := by
  have hrad : ∀ w ∈ closedBall (0 : ℂ) (7 / 2), ‖w • x‖ ≤ 7 / 2 := by
    intro w hw
    rw [norm_smul]
    calc
      ‖w‖ * ‖x‖ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg w)
      _ ≤ _ := by simpa using mem_closedBall_zero_iff.mp hw
  have hline : ∀ w ∈ closedBall (0 : ℂ) (7 / 2), (0 : ShortGapChart) + w • x ∈
      closedBall (0 : ShortGapChart) 4 := by
    intro w hw
    simpa only [zero_add, mem_closedBall_zero_iff] using
      (hrad w hw).trans (by norm_num : (7 / 2 : ℝ) ≤ 4)
  have hf : DiffContOnCl ℂ (fun w : ℂ ↦ chartGapDerivative F ru (1 / 16) (w • x))
      (ball 0 (7 / 2)) := by
    simpa only [zero_add] using
      diffContOnCl_of_analyticOnNhd_closedBall
        (analyticOnNhd_chartLine (analyticOnNhd_chartGapDerivative hF ru (1 / 16)) hline)
  have hpos : 0 < ru := by rcases hru with rfl | rfl <;> norm_num
  have hbound : ∀ w ∈ sphere (0 : ℂ) (7 / 2),
      ‖chartGapDerivative F ru (1 / 16) (w • x)‖ ≤ (2 : ℝ) ^ 21 := by
    intro w hw
    refine (norm_chartGapDerivative_le hpos (by norm_num) hF hM
      (hrad w (sphere_subset_closedBall hw))).trans ?_
    rcases hru with rfl | rfl <;> norm_num
  simpa only [one_smul] using shortGap_taylorRemainder_le_of_lookup hf hbound hlookup

#print axioms shortGap_taylorRemainder_le
#print axioms shortGap_taylorRemainder_le_of_lookup
#print axioms norm_chartGapDerivative_le
#print axioms shortGap_chartRemainder_le

end RefinedBMV.PositiveCenter.CompactGap
