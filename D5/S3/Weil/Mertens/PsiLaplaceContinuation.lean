/- GID: D5/S3/Weil/Mertens/PsiLaplaceContinuation
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/PsiLaplaceContinuation
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Actual psi-tail continuation and Euler forcing. -/

import D5.S3.Analytic.Laplace.EulerPoleObstruction
import D5.S3.Weil.ZeroSum
import D5.S3.Weil.Mertens.ThetaLaplaceContinuation
import D5.S3.Weil.Mertens.WeightedPrimeLimit
import D5.S3.Weil.Mertens.CriticalThetaTailPeak

/-! The actual psi-error Laplace integral on Re s > 0 and its normalized-zeta meromorphic continuation. -/

namespace D5.S3.Weil.Mertens.PsiLaplaceContinuation

open Real Set MeasureTheory Filter Asymptotics Complex
open scoped BigOperators Topology
open D5.S3.Analytic.Laplace.EulerPoleObstruction

noncomputable section

def qpsi (u : ℝ) : ℝ :=
  Real.exp (-u) * (Chebyshev.psi (Real.exp u) - Real.exp u)

def Qpsi (U : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) * (qpsi u : ℂ)

def Apsi (U : ℝ) (s : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..U, Complex.exp (-s * (u : ℂ)) * (qpsi u : ℂ)

def Mpsi (U : ℝ) (s : ℂ) : ℂ :=
  -(1 + logDeriv riemannZeta₁ (1 + s)) / (1 + s) - Apsi U s

def Dpsi : Set ℂ := {s | (-1 : ℝ) < s.re}

theorem qpsi_measurable : Measurable qpsi := by
  unfold qpsi
  exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (-u))).mul
    ((Chebyshev.psi_mono.measurable.comp (by fun_prop)).sub (by fun_prop))

private lemma qpsi_bound (u : ℝ) : ‖qpsi u‖ ≤ Real.log 4 + 4 + 1 := by
  have he := (Real.exp_pos u).le
  have hp := Chebyshev.psi_nonneg (Real.exp u)
  have hb := Chebyshev.psi_le_const_mul_self he
  rw [qpsi, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  calc
    Real.exp (-u) * |Chebyshev.psi (Real.exp u) - Real.exp u|
        ≤ Real.exp (-u) * (Chebyshev.psi (Real.exp u) + Real.exp u) := by
      gcongr
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg hp, abs_of_nonneg he])
    _ ≤ Real.exp (-u) * ((Real.log 4 + 4) * Real.exp u + Real.exp u) := by gcongr
    _ = Real.log 4 + 4 + 1 := by
      rw [← add_one_mul, mul_left_comm, ← Real.exp_add]
      simp

/-- Original psi error integrability, transported by t = exp u. -/
theorem qpsi_integrable : IntegrableOn qpsi (Ioi (Real.log 2)) := by
  have ht := WeightedPrimeLimit.chebyshev_error_kernel_integrable.mono_set
    (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 2))
  have he := (integrableOn_comp_exp_Ioi
    (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Real.log 2)).mpr
    (by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using ht)
  refine he.congr_fun ?_ measurableSet_Ioi
  intro u _
  dsimp [qpsi]
  rw [Real.exp_neg]
  field_simp

private theorem source_integrable (U : ℝ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (qpsi u : ℂ))
      (Ioi U) := by
  exact (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) U).mul_bdd
    qpsi_measurable.complex_ofReal.aestronglyMeasurable.restrict
    (Eventually.of_forall fun u => by simpa using qpsi_bound u)

theorem Apsi_entire (U : ℝ) : Differentiable ℂ (Apsi U) := by
  have hlocal (a b : ℝ) : IntegrableOn qpsi (Ioc a b) :=
    Measure.integrableOn_of_bounded (by simp) qpsi_measurable.aestronglyMeasurable
      (Eventually.of_forall qpsi_bound)
  by_cases hU : (0 : ℝ) ≤ U
  · have he : Apsi U = finiteHead qpsi 0 U := by
      funext s
      exact intervalIntegral.integral_of_le hU
    rw [he]
    exact finiteHead_entire (hlocal 0 U)
  · have he : Apsi U = -finiteHead qpsi U 0 := by
      funext s
      exact intervalIntegral.integral_of_ge (le_of_not_ge hU)
    rw [he]
    exact (finiteHead_entire (hlocal U 0)).neg

private lemma Qpsi_cutoff (U : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Qpsi U s = Qpsi 0 s - Apsi U s := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi'
    (source_integrable 0 hs) (source_integrable U hs)
  change Qpsi 0 s - Qpsi U s = Apsi U s at h
  linear_combination -h

/-- The actual von Mangoldt Mellin identity in its absolute-convergence region. -/
private theorem psi_mellin {z : ℂ} (hz : 1 < z.re) :
    -logDeriv riemannZeta z = z * ∫ x in Ioi (1 : ℝ),
      (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(z + 1)) := by
  have h := LSeries_eq_mul_integral_of_nonneg
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (by norm_num : (0 : ℝ) ≤ 1) hz CompleteChebyshevTailIdentity.mangoldt_prefix_bigO
    (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
  have he : LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) z =
      -logDeriv riemannZeta z := by
    simpa only [logDeriv_apply, neg_div, ArithmeticFunction.natCoe_apply] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
  rw [he] at h
  have hprefix (x : ℝ) :
      (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k) = Chebyshev.psi x := rfl
  simpa only [← Complex.ofReal_sum, hprefix] using h

private lemma kernel_eq (s : ℂ) (u : ℝ) :
    kernel qpsi s u = Complex.exp (-(s + 1) * (u : ℂ)) *
      ((Chebyshev.psi (Real.exp u) - Real.exp u : ℝ) : ℂ) := by
  unfold kernel qpsi
  rw [Complex.ofReal_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma psi_exp_point (s : ℂ) (u : ℝ) :
    Real.exp u • ((Chebyshev.psi (Real.exp u) : ℂ) *
      (Real.exp u : ℂ) ^ (-((1 + s) + 1))) =
      kernel qpsi s u + Complex.exp (-s * (u : ℂ)) := by
  rw [ThetaLaplaceContinuation.cpow_exp, kernel_eq, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_exp]
  have he : Complex.exp (-(s + 1) * (u : ℂ)) * Complex.exp (u : ℂ) =
      Complex.exp (-s * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hprod : Complex.exp (u : ℂ) *
      Complex.exp ((u : ℂ) * (-((1 + s) + 1))) =
      Complex.exp (-(s + 1) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [mul_left_comm, hprod]
  linear_combination he

private lemma Qpsi_zero_raw {s : ℂ} (hs : 0 < s.re) :
    Qpsi 0 s = -logDeriv riemannZeta (1 + s) / (1 + s) - 1 / s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hz0 : 1 + s ≠ 0 := Complex.ne_zero_of_re_pos (by simp; linarith)
  have hm := psi_mellin (z := 1 + s) (by simp; linarith)
  have he := integral_comp_exp_Ioi
    (fun x : ℝ => (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-((1 + s) + 1))) 0
  simp only [Real.exp_zero] at he
  have hpt : (fun u : ℝ => Real.exp u • ((Chebyshev.psi (Real.exp u) : ℂ) *
      (Real.exp u : ℂ) ^ (-((1 + s) + 1)))) =
      (fun u => kernel qpsi s u + Complex.exp (-s * (u : ℂ))) :=
    funext (psi_exp_point s)
  rw [hpt] at he
  have hi : IntegrableOn (kernel qpsi s) (Ioi 0) := source_integrable 0 hs
  rw [integral_add hi
    (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0)] at he
  have hem : (∫ u in Ioi (0 : ℝ), Complex.exp (-s * (u : ℂ))) = 1 / s := by
    simpa using integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  rw [hem] at he
  change Qpsi 0 s + 1 / s = _ at he
  rw [← he] at hm
  have hd : -logDeriv riemannZeta (1 + s) / (1 + s) = Qpsi 0 s + 1 / s := by
    rw [hm]
    field_simp
  linear_combination -hd

private lemma normalized_zeta_ne_zero_right {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₁ (1 + s) ≠ 0 := by
  have hz1 : 1 + s ≠ 1 := by simpa using Complex.ne_zero_of_re_pos hs
  intro hn
  have he := riemannZeta_eq_inv_sub_mul hz1
  rw [hn, mul_zero] at he
  exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith) he

/-- The finite cutoff is subtracted. No prime-power correction occurs. -/
theorem Qpsi_eq_Mpsi (U : ℝ) {s : ℂ} (hs : 0 < s.re) : Qpsi U s = Mpsi U s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hz0 : 1 + s ≠ 0 := Complex.ne_zero_of_re_pos (by simp; linarith)
  have hz1 : 1 + s ≠ 1 := by simpa using hs0
  rw [Qpsi_cutoff U hs, Qpsi_zero_raw hs,
    ThetaLaplaceContinuation.normalized_logDeriv hz1 (normalized_zeta_ne_zero_right hs)]
  unfold Mpsi
  field_simp [hs0, hz0]
  ring

private lemma Mpsi_analytic_of_ne_zero (U : ℝ) {s : ℂ}
    (hn : riemannZeta₁ (1 + s) ≠ 0) (hd : 1 + s ≠ 0) :
    AnalyticAt ℂ (Mpsi U) s := by
  have hz : AnalyticAt ℂ (logDeriv riemannZeta₁) (1 + s) :=
    (differentiable_riemannZeta₁.analyticAt _).deriv.div
      (differentiable_riemannZeta₁.analyticAt _) hn
  unfold Mpsi
  exact ((analyticAt_const.add (hz.comp (by fun_prop))).neg.div (by fun_prop) hd).sub
    (Apsi_entire U |>.analyticAt s)

/-- Analyticity includes the real point zero, using the normalized zeta value. -/
theorem Mpsi_real_analytic (U : ℝ) {x : ℝ} (hx : (-1 : ℝ) < x) :
    AnalyticAt ℂ (Mpsi U) (x : ℂ) := by
  have hn : riemannZeta₁ (1 + (x : ℂ)) ≠ 0 := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using
      (CriticalThetaTailPeak.normalized_zeta_real_ne_zero (x := 1 + x) (by linarith))
  exact Mpsi_analytic_of_ne_zero U hn (by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith)

/-- Actual strip zeros give a simple source pole with the complete multiplicity.
The local regular part uses the zeta factor at rho, never a value at 2*rho. -/
theorem actual_source_poles (U : ℝ) {ρ : ℂ} (hρ : D5.S3.Weil.ZeroSum.IsNontrivialZero ρ) :
    let a := ρ - 1
    let m := analyticOrderNatAt riemannZeta ρ
    let Λ := -(m : ℂ) / ρ
    a ∈ Dpsi ∧ a ≠ 0 ∧ a.im ≠ 0 ∧
    0 < m ∧ analyticOrderAt riemannZeta ρ ≠ ⊤ ∧ Λ ≠ 0 ∧
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧
      Mpsi U =ᶠ[𝓝[≠] a] (fun s => Λ / (s - a) + H s) ∧
      (fun s => -deriv (Mpsi U) s + Mpsi U s) =ᶠ[𝓝[≠] a]
        (fun s => Λ / (s - a) ^ 2 + Λ / (s - a) + H s - deriv H s) ∧
      meromorphicOrderAt (Mpsi U) a = (-1 : ℤ) ∧
      meromorphicOrderAt (fun s => -deriv (Mpsi U) s + Mpsi U s) a = (-2 : ℤ) := by
  change riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 at hρ
  let a := ρ - 1
  let m := analyticOrderNatAt riemannZeta ρ
  let Λ := -(m : ℂ) / ρ
  change a ∈ Dpsi ∧ a ≠ 0 ∧ a.im ≠ 0 ∧ 0 < m ∧ _ ∧ Λ ≠ 0 ∧ _
  have hρ0 : ρ ≠ 0 := Complex.ne_zero_of_re_pos hρ.2.1
  have hρ1 : ρ ≠ 1 := by
    intro he
    have hr := hρ.2.2
    simpa only [he, Complex.one_re, lt_self_iff_false] using hr
  have hf : AnalyticAt ℂ riemannZeta ρ := Zeta23.riemannZeta_analyticOnNhd_compl_one ρ hρ1
  have hfin := Zeta23.analyticOrderAt_riemannZeta_ne_top hρ1
  have hmpos : 0 < m := ENat.toNat_pos (hf.analyticOrderAt_ne_zero.mpr hρ.1) hfin
  have hΛ : Λ ≠ 0 := div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hmpos.ne')) hρ0
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp hfin
  let g₁ : ℂ → ℂ := fun z => (z - 1) * g z
  have hg₁ : AnalyticAt ℂ g₁ ρ := (analyticAt_id.sub analyticAt_const).mul hg
  have hg₁0 : g₁ ρ ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hρ1) hg0
  have hf₁ : riemannZeta₁ =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ m * g₁ z := by
    filter_upwards [hfg, compl_singleton_mem_nhds hρ1] with z hz hz1
    have hn : z ≠ 1 := by simpa using hz1
    have he : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hn]
      field_simp
    rw [he, hz]
    simp only [smul_eq_mul]
    dsimp [g₁]
    ring
  obtain ⟨hR, hlog⟩ := ThetaLaplaceContinuation.factor_logDeriv hg₁ hg₁0 hf₁
  let R := logDeriv g₁
  let H : ℂ → ℂ := fun s =>
    (m : ℂ) / (ρ * (1 + s)) - (1 + R (1 + s)) / (1 + s) - Apsi U s
  have hlin : AnalyticAt ℂ (fun s : ℂ => 1 + s) a := by fun_prop
  have hpoint : 1 + a = ρ := by dsimp [a]; ring
  have hden : 1 + a ≠ 0 := hpoint ▸ hρ0
  have hRc : AnalyticAt ℂ (fun s => R (1 + s)) a := hR.comp_of_eq hlin hpoint
  have hH : AnalyticAt ℂ H a :=
    ((analyticAt_const.div (analyticAt_const.mul hlin) (mul_ne_zero hρ0 hden)).sub
      ((analyticAt_const.add hRc).div hlin hden)).sub (Apsi_entire U |>.analyticAt a)
  have ht : Tendsto (fun s : ℂ => 1 + s) (𝓝 a) (𝓝 ρ) := by
    rw [← hpoint]
    exact (continuous_const.add continuous_id).continuousAt.tendsto
  have hlogpull := ht.eventually (eventually_nhdsWithin_iff.mp hlog)
  have heq : Mpsi U =ᶠ[𝓝[≠] a] (fun s => Λ / (s - a) + H s) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hlogpull,
      mem_nhdsWithin_of_mem_nhds (hlin.continuousAt.eventually_ne hden)] with s hs hlogs hds
    have hsa : s - a ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
    have hsρ : 1 + s ≠ ρ := by
      intro h
      apply hsa
      dsimp [a]
      linear_combination h
    have hld : logDeriv riemannZeta₁ (1 + s) = (m : ℂ) / (s - a) + R (1 + s) := by
      convert hlogs hsρ using 1
      dsimp [a, R]
      congr 2
      ring
    dsimp [Mpsi, H, Λ]
    rw [hld]
    field_simp [hρ0, hds, hsa]
    ring
  have hp := ThetaLaplaceContinuation.pole_orders hH hΛ heq
  have hnonreal : ρ.im ≠ 0 := by
    intro him
    have he : a = ((ρ.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [a, him]
    have han := Mpsi_real_analytic U (x := ρ.re - 1) (by linarith [hρ.2.1])
    rw [← he] at han
    have hn := han.meromorphicOrderAt_nonneg
    rw [hp.2.1] at hn
    exact (not_le_of_gt (by exact_mod_cast (show (-1 : ℤ) < 0 by norm_num))) hn
  refine ⟨?_, sub_ne_zero.mpr hρ1, ?_, hmpos, hfin, hΛ,
    H, hH, heq, hp.1, hp.2.1, hp.2.2⟩
  · change (-1 : ℝ) < (ρ - 1).re
    simp only [Complex.sub_re, Complex.one_re]
    linarith [hρ.2.1]
  · simpa only [a, Complex.sub_im, Complex.one_im, sub_zero] using hnonreal

/-- Full complex punctured-neighbourhood source coefficient, not just a ray limit. -/
theorem source_normalized_limit (U : ℝ) {ρ : ℂ} (hρ : D5.S3.Weil.ZeroSum.IsNontrivialZero ρ) :
    Tendsto (fun s : ℂ => (s - (ρ - 1)) * Mpsi U s) (𝓝[≠] (ρ - 1))
      (𝓝 (-(analyticOrderNatAt riemannZeta ρ : ℂ) / ρ)) := by
  obtain ⟨_, _, _, _, _, _, H, hH, heq, _⟩ := actual_source_poles U hρ
  let a := ρ - 1
  let Λ := -(analyticOrderNatAt riemannZeta ρ : ℂ) / ρ
  have hc : ContinuousAt (fun s : ℂ => Λ + (s - a) * H s) a := by
    have hh := hH.continuousAt
    fun_prop
  have hp : Tendsto (fun s : ℂ => Λ + (s - a) * H s) (𝓝[≠] a) (𝓝 Λ) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hp.congr'
  filter_upwards [heq, self_mem_nhdsWithin] with s hs hsa
  have hn : s - a ≠ 0 := sub_ne_zero.mpr (by simpa using hsa)
  change Mpsi U s = Λ / (s - a) + H s at hs
  change Λ + (s - a) * H s = (s - a) * Mpsi U s
  rw [hs]
  field_simp [hn]
  <;> ring

end
end D5.S3.Weil.Mertens.PsiLaplaceContinuation
