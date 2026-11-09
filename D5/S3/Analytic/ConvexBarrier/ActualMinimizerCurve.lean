import D5.S3.Analytic.ConvexBarrier.ActualAffineBarrier
import D5.S3.Analytic.ConvexBarrier.ScalarMechanism
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
The actual minimizer curve, its actual k derivative, mixed cubic bound, and
the integral primitive. Zhang--Fu--Dai, arXiv:2611.06404v1, Theorem 3.5,
(3.15)--(3.25). Source only; no Lean execution or independent correctness
evidence is asserted. The only chosen object is F1's attained minimizer.
-/

open Set Filter MeasureTheory
open scoped Topology Interval
open D5.S3.Geometry.PowerCone

namespace D5.S3.Analytic.ConvexBarrier.Actual

def basePoint (r : ℝ) : Base := (r,1-r)
def horizontalDirection : Base := (1,-1)
def ex : Base := (1,0)
def ez : Base := (0,1)

theorem basePoint_mem {r : ℝ} (hr : r ∈ J) : basePoint r ∈ quadrant :=
  ⟨hr.1,sub_pos.mpr hr.2⟩

theorem basePoint_hasDerivAt (r : ℝ) :
    HasDerivAt basePoint horizontalDirection r := by
  simpa [basePoint,horizontalDirection] using (hasDerivAt_id r).prodMk
    ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r))

variable {c ν : ℝ} {F : ScalarPoint → ℝ}
variable (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)

noncomputable def zeta (r : ℝ) : ℝ := fiberMinimizer hF (basePoint r)
noncomputable def graphPoint (r : ℝ) : Base := (r,zeta hF r)
noncomputable def p (r : ℝ) : ℝ := D1 (sectionFunction ν F) (graphPoint hF r) ex
noncomputable def k (r : ℝ) : ℝ := D2 (sectionFunction ν F) (graphPoint hF r) ez ez
noncomputable def m (r : ℝ) : ℝ := D2 (sectionFunction ν F) (graphPoint hF r) ex ez
noncomputable def er (r : ℝ) : Base := (1,-m hF r/k hF r)
noncomputable def qhat (r : ℝ) : ℝ :=
  metric (sectionFunction ν F) (graphPoint hF r) (er hF r) (er hF r)
noncomputable def q (r : ℝ) : ℝ := Real.sqrt (qhat hF r)
noncomputable def kp (r : ℝ) : ℝ :=
  D3 (sectionFunction ν F) (graphPoint hF r) (er hF r) ez ez
noncomputable def sigma (r : ℝ) : ℝ := ∫ t in (1/2 : ℝ)..r, q hF t

theorem graphPoint_mem {r : ℝ} (hr : r ∈ J) : graphPoint hF r ∈ sectionDomain c := by
  exact (fiberMinimizer_spec hF (basePoint_mem hr)).1

theorem zeta_contDiffAt {r : ℝ} (hr : r ∈ J) : ContDiffAt ℝ 2 (zeta hF) r := by
  exact (fiberMinimizer_contDiffAt hF (basePoint_mem hr)).comp r
    ((contDiff_id.prodMk (contDiff_const.sub contDiff_id)).contDiffAt)

theorem graphPoint_contDiffAt {r : ℝ} (hr : r ∈ J) :
    ContDiffAt ℝ 2 (graphPoint hF) r := contDiffAt_id.prodMk (zeta_contDiffAt hF hr)

theorem section_stationary {r : ℝ} (hr : r ∈ J) :
    D1 (sectionFunction ν F) (graphPoint hF r) ez = 0 := by
  rw [section_first hF (graphPoint_mem hF hr)]
  change fiberGradient F (basePoint r,fiberMinimizer hF (basePoint r))/ν = 0
  rw [fiberMinimizer_stationary hF (basePoint_mem hr),zero_div]

theorem k_metric {r : ℝ} (hr : r ∈ J) :
    metric (sectionFunction ν F) (graphPoint hF r) ez ez = k hF r := by
  simp only [metric_apply,metricValue,section_stationary hF hr,k,mul_zero,sub_zero]

theorem k_pos {r : ℝ} (hr : r ∈ J) : 0 < k hF r := by
  rw [← k_metric hF hr]
  exact section_metric_pos hF (graphPoint_mem hF hr) ez (by simp [ez])

theorem zeta_hasDerivAt {r : ℝ} (hr : r ∈ J) :
    HasDerivAt (zeta hF) (-m hF r/k hF r) r := by
  have hz := ((fiberMinimizer_contDiffAt hF (basePoint_mem hr)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt r (basePoint_hasDerivAt r)
  have he := fiberMinimizer_derivative hF (basePoint_mem hr) horizontalDirection
  have hm := section_second hF (graphPoint_mem hF hr) ex ez
  have hk := section_second hF (graphPoint_mem hF hr) ez ez
  have hraw := minimizer_fiber_hessian_pos hF (basePoint_mem hr)
  have hne := (parameter_pos hF).ne'
  have heq : -m hF r/k hF r =
      fderiv ℝ (fiberMinimizer hF) (basePoint r) horizontalDirection := by
    rw [he]
    dsimp only [m,k] at ⊢
    rw [hm,hk]
    change -(_/ν)/(_/ν) = -_/ _
    field_simp [hne,hraw.ne'] <;> ring
  rw [heq]
  exact hz

theorem graphPoint_hasDerivAt {r : ℝ} (hr : r ∈ J) :
    HasDerivAt (graphPoint hF) (er hF r) r :=
  (hasDerivAt_id r).prodMk (zeta_hasDerivAt hF hr)

theorem er_decomposition (r : ℝ) : er hF r = ex + (-m hF r/k hF r) • ez := by
  ext <;> simp [er,ex,ez]

theorem er_first {r : ℝ} (hr : r ∈ J) :
    D1 (sectionFunction ν F) (graphPoint hF r) (er hF r) = p hF r := by
  rw [er_decomposition]
  simp [section_stationary hF hr,p]

theorem er_orthogonal {r : ℝ} (hr : r ∈ J) :
    metric (sectionFunction ν F) (graphPoint hF r) (er hF r) ez = 0 := by
  simp only [metric_apply,metricValue,section_stationary hF hr,mul_zero,sub_zero,
    er_decomposition,map_add,map_smul,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  change m hF r + (-m hF r/k hF r)*k hF r = 0
  field_simp [(k_pos hF hr).ne']
  <;> ring

theorem qhat_pos {r : ℝ} (hr : r ∈ J) : 0 < qhat hF r := by
  exact section_metric_pos hF (graphPoint_mem hF hr) (er hF r)
    (by intro he; have := congrArg Prod.fst he; norm_num [er] at this)

theorem q_pos {r : ℝ} (hr : r ∈ J) : 0 < q hF r := Real.sqrt_pos.mpr (qhat_pos hF hr)
theorem q_sq {r : ℝ} (hr : r ∈ J) : q hF r ^ 2 = qhat hF r :=
  Real.sq_sqrt (qhat_pos hF hr).le

/-- The exact Schur scalar; q is its square root, not this scalar itself. -/
theorem qhat_schur {r : ℝ} (hr : r ∈ J) :
    qhat hF r = D2 (sectionFunction ν F) (graphPoint hF r) ex ex -
      p hF r ^ 2 - m hF r ^ 2/k hF r := by
  have hs := d2_symm (section_smooth hF (graphPoint_mem hF hr)) ez ex
  unfold qhat
  simp only [metric_apply,metricValue,er_first hF hr]
  simp only [er_decomposition hF r,map_add,map_smul,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,hs]
  change _ + (-m hF r/k hF r)*m hF r +
    ((-m hF r/k hF r)*m hF r + (-m hF r/k hF r)*((-m hF r/k hF r)*k hF r)) -
      p hF r*p hF r = _
  field_simp [(k_pos hF hr).ne'] <;> ring

/-- Differentiates the actual composed f_zz, with only a C2 graph. -/
theorem k_hasDerivAt {r : ℝ} (hr : r ∈ J) : HasDerivAt (k hF) (kp hF r) r := by
  have hd := (d2_hasFDerivAt (section_smooth hF (graphPoint_mem hF hr)) ez ez).
    comp_hasDerivAt r (graphPoint_hasDerivAt hF hr)
  exact hd

theorem m_continuousAt {r : ℝ} (hr : r ∈ J) : ContinuousAt (m hF) r := by
  have hf := section_smooth hF (graphPoint_mem hF hr)
  exact ((d2_hasFDerivAt hf ex ez).continuousAt.comp
    (graphPoint_contDiffAt hF hr).continuousAt)

theorem er_continuousAt {r : ℝ} (hr : r ∈ J) : ContinuousAt (er hF) r :=
  continuousAt_const.prodMk (((m_continuousAt hF hr).neg).div
    (k_hasDerivAt hF hr).continuousAt (k_pos hF hr).ne')

theorem qhat_continuousAt {r : ℝ} (hr : r ∈ J) : ContinuousAt (qhat hF) r := by
  have hf := section_smooth hF (graphPoint_mem hF hr)
  have hg := (graphPoint_contDiffAt hF hr).continuousAt
  have he := er_continuousAt hF hr
  have hdf := (hf.fderiv_right (m := 2) (by norm_num)).continuousAt.comp hg
  have hddf := ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).continuousAt.comp hg
  exact ((hddf.clm_apply he).clm_apply he).sub ((hdf.clm_apply he).mul (hdf.clm_apply he))

theorem q_continuousAt {r : ℝ} (hr : r ∈ J) : ContinuousAt (q hF) r :=
  (qhat_continuousAt hF hr).sqrt

/-- sigma is the actual interval integral; its derivative follows from local
continuity and compact-interval integrability inside J. No global primitive. -/
theorem sigma_hasDerivAt {r : ℝ} (hr : r ∈ J) :
    HasDerivAt (sigma hF) (q hF r) r := by
  have h0 : (1/2 : ℝ) ∈ J := by norm_num [J]
  have hc : ContinuousOn (q hF) J := fun t ht =>
    (q_continuousAt hF ht).continuousWithinAt
  have hi : IntervalIntegrable (q hF) volume (1/2 : ℝ) r := by
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    intro t ht
    change min (1/2 : ℝ) r ≤ t ∧ t ≤ max (1/2 : ℝ) r at ht
    exact ⟨lt_of_lt_of_le (lt_min h0.1 hr.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt h0.2 hr.2)⟩
  exact intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter (s := J) isOpen_Ioo hc r hr)
    (q_continuousAt hF hr)

theorem cubic_er_vertical {r : ℝ} (hr : r ∈ J) :
    cubic (sectionFunction ν F) (graphPoint hF r) (er hF r) ez ez =
      kp hF r - 2*p hF r*k hF r := by
  simp only [cubic_apply,cubicValue,section_stationary hF hr,er_first hF hr,
    zero_mul,mul_zero,sub_zero,add_zero,kp,k]

noncomputable def E1 (r : ℝ) : Base := (q hF r)⁻¹ • er hF r
noncomputable def E2 (r : ℝ) : Base := (Real.sqrt (k hF r))⁻¹ • ez

theorem orthonormal {r : ℝ} (hr : r ∈ J) :
    let G := metric (sectionFunction ν F) (graphPoint hF r)
    G (E1 hF r) (E1 hF r) = 1 ∧ G (E2 hF r) (E2 hF r) = 1 ∧
      G (E1 hF r) (E2 hF r) = 0 ∧ G (E2 hF r) (E1 hF r) = 0 := by
  dsimp only
  have hq := q_sq hF hr
  have hk := Real.sq_sqrt (k_pos hF hr).le
  refine ⟨?_,?_,?_,?_⟩
  · simp only [E1,map_smul,LinearMap.smul_apply,smul_eq_mul]
    change (q hF r)⁻¹*((q hF r)⁻¹*qhat hF r) = 1
    calc
      _ = ((q hF r)^2)⁻¹*qhat hF r := by rw [pow_two,mul_inv]; ring
      _ = 1 := by rw [hq,inv_mul_cancel₀ (qhat_pos hF hr).ne']
  · simp only [E2,map_smul,LinearMap.smul_apply,smul_eq_mul,k_metric hF hr]
    calc
      _ = ((Real.sqrt (k hF r))^2)⁻¹*k hF r := by rw [pow_two,mul_inv]; ring
      _ = 1 := by rw [hk,inv_mul_cancel₀ (k_pos hF hr).ne']
  · simp [E1,E2,er_orthogonal hF hr]
  · rw [metric_symm (section_smooth hF (graphPoint_mem hF hr)) (E2 hF r) (E1 hF r)]
    simp [E1,E2,er_orthogonal hF hr]

theorem beta_actual {r : ℝ} (hr : r ∈ J) :
    cubic (sectionFunction ν F) (graphPoint hF r) (E1 hF r) (E2 hF r) (E2 hF r) =
      beta (p hF r) (k hF r) (kp hF r) (q hF r) := by
  have hsk := Real.sq_sqrt (k_pos hF hr).le
  have hi : (Real.sqrt (k hF r))⁻¹*(Real.sqrt (k hF r))⁻¹ = (k hF r)⁻¹ := by
    rw [← mul_inv,← pow_two,hsk]
  simp only [E1,E2,map_smul,LinearMap.smul_apply,smul_eq_mul,cubic_er_vertical hF hr]
  calc
    _ = ((q hF r)⁻¹*((Real.sqrt (k hF r))⁻¹*(Real.sqrt (k hF r))⁻¹))*
        (kp hF r-2*p hF r*k hF r) := by ring
    _ = ((q hF r)⁻¹*(k hF r)⁻¹)*(kp hF r-2*p hF r*k hF r) := by rw [hi]
    _ = _ := by
      unfold beta
      field_simp [(q_pos hF hr).ne',(k_pos hF hr).ne'] <;> ring

/-- Actual G-orthonormal radial/vertical vectors supply the mixed bound. -/
theorem beta_bound {s r : ℝ} (hr : r ∈ J) (hs : 1 ≤ s) (hν : ν = s^2+1) :
    |beta (p hF r) (k hF r) (kp hF r) (q hF r)| ≤ 2*(s^2-1)/s := by
  have hf := section_smooth hF (graphPoint_mem hF hr)
  obtain ⟨h11,h22,h12,h21⟩ := orthonormal hF hr
  rw [← beta_actual hF hr]
  exact mixed_trilinear_bound (metric (sectionFunction ν F) (graphPoint hF r))
    (cubic (sectionFunction ν F) (graphPoint hF r))
    (cubic_symm12 hf) (cubic_symm23 hf) (E1 hF r) (E2 hF r)
    h11 h22 h12 h21 (2*(s^2-1)/s)
    (section_cubic_bound hF (graphPoint_mem hF hr) hs hν)

theorem parameter_two_actual : 2 ≤ ν := by
  have hr : (1/2 : ℝ) ∈ J := by norm_num [J]
  have hv := graphPoint_mem hF hr
  exact parameter_two hF hv (sectionLinear ez)
    (projective_pos hF hv _ (section_nonradial (v := graphPoint hF (1/2))
      (by simp [ez])))

end D5.S3.Analytic.ConvexBarrier.Actual
