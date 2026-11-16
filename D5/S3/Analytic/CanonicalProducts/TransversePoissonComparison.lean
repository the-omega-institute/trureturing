/- GID: D5/S3/Analytic/CanonicalProducts/TransversePoissonComparison
   generality: G
   mirror-B: D5/B/S3/Analytic/CanonicalProducts/TransversePoissonComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-sided Poisson bounds for integrated logarithmic defects. -/

import D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment

/-! Two-sided Poisson comparisons from scalar logarithmic estimates. -/

open Filter MeasureTheory
open scoped Topology BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.CanonicalProducts.TransversePoissonComparison
open D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment

private lemma quadratic_pos {g : ℝ} (hg : 0 < g) (x : ℝ) :
    0 < x^2 + g^2 := by
  nlinarith [sq_nonneg x, sq_pos_of_pos hg]

private lemma log_ratio_poisson_bounds {v g T : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) (hg : 0 < g) (hT : 1 ≤ T) :
    16 * T * v / (9 * (T^2 + g^2)) ≤
        Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2)) ∧
    Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2)) ≤
        16 * T * v / (T^2 + g^2) := by
  have hT0 : 0 ≤ T := by linarith
  have hA := quadratic_pos hg (T + v)
  have hB := quadratic_pos hg (T - v)
  have hR := quadratic_pos hg T
  have hn : 0 ≤ 4 * T * v :=
    mul_nonneg (mul_nonneg (by norm_num) hT0) hv0
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hA hB)
  have hu := Real.log_le_sub_one_of_pos (div_pos hA hB)
  have el : 1 - (((T + v)^2 + g^2) / ((T - v)^2 + g^2))⁻¹ =
      4 * T * v / ((T + v)^2 + g^2) := by
    field_simp [hA.ne', hB.ne'] <;> ring
  have eu : ((T + v)^2 + g^2) / ((T - v)^2 + g^2) - 1 =
      4 * T * v / ((T - v)^2 + g^2) := by
    field_simp [hB.ne'] <;> ring
  rw [el] at hl
  rw [eu] at hu
  have hsum : (T + v)^2 ≤ (3 * T / 2)^2 :=
    (sq_le_sq₀ (by linarith : 0 ≤ T + v) (by linarith : 0 ≤ 3 * T / 2)).2
      (by linarith)
  have hdiff : (T / 2)^2 ≤ (T - v)^2 :=
    (sq_le_sq₀ (by linarith : 0 ≤ T / 2) (by linarith : 0 ≤ T - v)).2
      (by linarith)
  have hAupper : 4 * ((T + v)^2 + g^2) ≤ 9 * (T^2 + g^2) := by
    nlinarith [sq_nonneg g]
  have hBlower : T^2 + g^2 ≤ 4 * ((T - v)^2 + g^2) := by
    nlinarith [sq_nonneg g]
  constructor
  · refine le_trans ?_ hl
    apply (div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 9) hR) hA).2
    convert mul_le_mul_of_nonneg_left hAupper hn using 1 <;> ring
  · refine le_trans hu ?_
    apply (div_le_div_iff₀ hB hR).2
    convert mul_le_mul_of_nonneg_left hBlower hn using 1 <;> ring

private lemma endpoint_poisson_bounds {a g T : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hg : 0 < g) (hT : 1 ≤ T) :
    (8 / 9 : ℝ) * (a^2 * T / (T^2 + g^2)) ≤ endpointKernel a g T ∧
    endpointKernel a g T ≤ 8 * (a^2 * T / (T^2 + g^2)) := by
  have hnum : Continuous (fun v : ℝ => (T + v)^2 + g^2) :=
    ((continuous_const.add continuous_id).pow 2).add continuous_const
  have hden : Continuous (fun v : ℝ => (T - v)^2 + g^2) :=
    ((continuous_const.sub continuous_id).pow 2).add continuous_const
  have hlog : Continuous (fun v : ℝ =>
      Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2))) :=
    (hnum.div hden (fun v => (quadratic_pos hg (T - v)).ne')).log
      (fun v => (div_pos (quadratic_pos hg (T + v))
        (quadratic_pos hg (T - v))).ne')
  have hlow : IntervalIntegrable
      (fun v : ℝ => (16 * T / (9 * (T^2 + g^2))) * v) volume 0 a :=
    (continuous_const.mul continuous_id).intervalIntegrable (μ := volume) 0 a
  have hhigh : IntervalIntegrable
      (fun v : ℝ => (16 * T / (T^2 + g^2)) * v) volume 0 a :=
    (continuous_const.mul continuous_id).intervalIntegrable (μ := volume) 0 a
  have hl : ∀ v ∈ Set.Icc (0 : ℝ) a,
      (16 * T / (9 * (T^2 + g^2))) * v ≤
        Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2)) := by
    intro v hv
    calc
      _ = 16 * T * v / (9 * (T^2 + g^2)) := by ring
      _ ≤ _ := (log_ratio_poisson_bounds hv.1 (hv.2.trans ha1) hg hT).1
  have hu : ∀ v ∈ Set.Icc (0 : ℝ) a,
      Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2)) ≤
        (16 * T / (T^2 + g^2)) * v := by
    intro v hv
    calc
      _ ≤ 16 * T * v / (T^2 + g^2) :=
        (log_ratio_poisson_bounds hv.1 (hv.2.trans ha1) hg hT).2
      _ = _ := by ring
  have hL : (∫ v in (0 : ℝ)..a, (16 * T / (9 * (T^2 + g^2))) * v) ≤
      endpointKernel a g T :=
    intervalIntegral.integral_mono_on ha0 hlow
      (hlog.intervalIntegrable (μ := volume) 0 a) hl
  have hU : endpointKernel a g T ≤
      ∫ v in (0 : ℝ)..a, (16 * T / (T^2 + g^2)) * v :=
    intervalIntegral.integral_mono_on ha0
      (hlog.intervalIntegrable (μ := volume) 0 a) hhigh hu
  rw [intervalIntegral.integral_const_mul, integral_id] at hL hU
  constructor
  · convert hL using 1 <;> field_simp [(quadratic_pos hg T).ne'] <;> ring
  · convert hU using 1 <;> ring

theorem integrated_defect_poisson_bounds {I : Type*} (w a gamma : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1 / 2)
    (hgamma : ∀ i, 0 < gamma i)
    (hbudget : Summable (fun i => w i * (a i)^2 / (gamma i)^2))
    (T : ℝ) (hT : 1 ≤ T) :
    (8 / 9 : ℝ) * (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) ≤
      integratedDefect w a gamma T ∧
    integratedDefect w a gamma T ≤
      8 * (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) := by
  classical
  have hT0 : 0 ≤ T := by linarith
  let p : I → ℝ := fun i => w i * (a i)^2 * T / (T^2 + (gamma i)^2)
  let e : I → ℝ := fun i => w i * endpointKernel (a i) (gamma i) T
  have hp0 (i : I) : 0 ≤ p i := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (hw i) (sq_nonneg (a i))) hT0)
      (quadratic_pos (hgamma i) T).le
  have hpbudget (i : I) : p i ≤ T * (w i * (a i)^2 / (gamma i)^2) := by
    calc
      p i ≤ w i * (a i)^2 * T / (gamma i)^2 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg (hw i) (sq_nonneg (a i))) hT0)
          (sq_pos_of_pos (hgamma i)) (by nlinarith [sq_nonneg T])
      _ = T * (w i * (a i)^2 / (gamma i)^2) := by ring
  have hp : Summable p :=
    Summable.of_nonneg_of_le hp0 hpbudget (hbudget.mul_left T)
  have hlo (i : I) : (8 / 9 : ℝ) * p i ≤ e i := by
    have h := mul_le_mul_of_nonneg_left
      (endpoint_poisson_bounds (ha0 i) (ha1 i) (hgamma i) hT).1 (hw i)
    convert h using 1 <;> dsimp [p, e] <;> ring
  have hhi (i : I) : e i ≤ 8 * p i := by
    have h := mul_le_mul_of_nonneg_left
      (endpoint_poisson_bounds (ha0 i) (ha1 i) (hgamma i) hT).2 (hw i)
    convert h using 1 <;> dsimp [p, e] <;> ring
  have he0 (i : I) : 0 ≤ e i :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 9) (hp0 i)).trans (hlo i)
  have he : Summable e :=
    Summable.of_nonneg_of_le he0 hhi (hp.mul_left 8)
  have hidentity : integratedDefect w a gamma T = ∑' i, e i :=
    (integrated_transverse_moment w a gamma hw ha0 ha1 hgamma hbudget).2.2.2.2.1 T hT0
  rw [hidentity]
  change (8 / 9 : ℝ) * (∑' i, p i) ≤ (∑' i, e i) ∧
    (∑' i, e i) ≤ 8 * (∑' i, p i)
  constructor
  · calc
      _ = ∑' i, (8 / 9 : ℝ) * p i := (hp.tsum_mul_left (8 / 9 : ℝ)).symm
      _ ≤ _ := Summable.tsum_le_tsum hlo (hp.mul_left (8 / 9 : ℝ)) he
  · calc
      _ ≤ ∑' i, 8 * p i := Summable.tsum_le_tsum hhi he (hp.mul_left 8)
      _ = _ := hp.tsum_mul_left 8

end D5.S3.Analytic.CanonicalProducts.TransversePoissonComparison
