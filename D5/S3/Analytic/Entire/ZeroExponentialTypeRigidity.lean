/- GID: D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/ZeroExponentialTypeRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real-axis boundedness and reflection yield zero exponential type rigidity. -/

import D5.S3.Analytic.Entire.ExponentialPolynomial
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


open Set Filter Asymptotics Complex Bornology
open scoped Topology Real

namespace D5.S3.Analytic.Entire

/-- An entire function of zero exponential type that is bounded on the real axis
is constant. The real bound need not be supplied with a positivity hypothesis. -/
theorem eq_at_zero_of_zero_exponential_type_of_bounded_real
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℂ,
      ‖f z‖ ≤ A * Real.exp (ε * ‖z‖))
    {B : ℝ} (hreal : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ B) :
    ∀ z : ℂ, f z = f 0 := by
  -- This local argument will be used for both f and w ↦ f (-w).
  have hright : ∀ (g : ℂ → ℂ), Differentiable ℂ g →
      (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ w : ℂ,
        ‖g w‖ ≤ A * Real.exp (ε * ‖w‖)) →
      (∀ x : ℝ, ‖g (x : ℂ)‖ ≤ B) →
      ∀ z : ℂ, 0 ≤ z.re → ‖g (I * z)‖ ≤ B := by
    intro g hg hggrowth hgreal z hz
    -- Remove the damping at this fixed point, approaching zero from above.
    suffices h : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ‖Complex.exp (-(ε : ℂ) * z) * g (I * z)‖ ≤ B by
      refine le_of_tendsto (Tendsto.mono_left ?_ nhdsWithin_le_nhds) h
      exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    obtain ⟨A, hA⟩ := hggrowth (ε / 2) (by linarith)
    let H : ℂ → ℂ := fun w => Complex.exp (-(ε : ℂ) * w) * g (I * w)
    have hdH : Differentiable ℂ H :=
      exponential_gauge_entire (ε : ℂ)
        (hg.comp (differentiable_id.const_mul I))
    have hHnorm (w : ℂ) :
        ‖H w‖ = Real.exp (-ε * w.re) * ‖g (I * w)‖ := by
      simp [H, norm_mul, Complex.norm_exp, Complex.mul_re]
    have hHO : ∃ c < (2 : ℝ), ∃ b : ℝ,
        H =O[cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}]
          (fun w => Real.exp (b * ‖w‖ ^ c)) := by
      refine ⟨1, by norm_num, ε / 2, Asymptotics.IsBigO.of_bound A ?_⟩
      refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
      simp only [Real.rpow_one, Real.norm_eq_abs, Real.abs_exp]
      calc
        ‖H w‖ = Real.exp (-ε * w.re) * ‖g (I * w)‖ := hHnorm w
        _ ≤ ‖g (I * w)‖ :=
          mul_le_of_le_one_left (norm_nonneg _)
            (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.2 hε.le) (le_of_lt hw)))
        _ ≤ A * Real.exp ((ε / 2) * ‖w‖) := by
          simpa only [norm_mul, Complex.norm_I, one_mul] using hA (I * w)
    have hHray : Tendsto (fun x : ℝ => H (x : ℂ)) atTop (𝓝 0) := by
      have hdecay : Tendsto (fun x : ℝ => Real.exp (-(ε / 2) * x))
          atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_const_nhds.neg_mul_atTop (by linarith : -(ε / 2) < 0)
            tendsto_id)
      have hmajorant : Tendsto (fun x : ℝ => A * Real.exp (-(ε / 2) * x))
          atTop (𝓝 0) := by
        simpa only [mul_zero] using hdecay.const_mul A
      refine squeeze_zero_norm' ?_ hmajorant
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      calc
        ‖H (x : ℂ)‖ = Real.exp (-ε * x) * ‖g (I * (x : ℂ))‖ := by
          simpa only [Complex.ofReal_re] using hHnorm (x : ℂ)
        _ ≤ Real.exp (-ε * x) * (A * Real.exp ((ε / 2) * x)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hx] using hA (I * (x : ℂ))
        _ = A * (Real.exp (-ε * x) * Real.exp ((ε / 2) * x)) := by ring
        _ = A * Real.exp (-(ε / 2) * x) := by
          rw [← Real.exp_add]
          congr 2 <;> ring
    have hHaxis : ∀ x : ℝ, ‖H ((x : ℂ) * I)‖ ≤ B := by
      intro x
      have hrot : I * ((x : ℂ) * I) = ((-x : ℝ) : ℂ) := by
        calc
          I * ((x : ℂ) * I) = (x : ℂ) * (I * I) := by ring
          _ = ((-x : ℝ) : ℂ) := by simp
      have hre : (((x : ℂ) * I).re) = 0 := by simp
      rw [hHnorm, hre, mul_zero, Real.exp_zero, one_mul, hrot]
      exact hgreal (-x)
    exact PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real
      (f := H) (z := z) hdH.diffContOnCl hHO hHray hHaxis hz
  have hnegdiff : Differentiable ℂ (fun w : ℂ => f (-w)) :=
    hf.comp differentiable_id.neg
  have hneggrowth : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ w : ℂ,
      ‖f (-w)‖ ≤ A * Real.exp (ε * ‖w‖) := by
    intro ε hε
    obtain ⟨A, hA⟩ := hgrowth ε hε
    exact ⟨A, fun w => by simpa only [norm_neg] using hA (-w)⟩
  have hnegreal : ∀ x : ℝ, ‖f (-(x : ℂ))‖ ≤ B := by
    intro x
    simpa only [Complex.ofReal_neg] using hreal (-x)
  have hplane : ∀ z : ℂ, ‖f z‖ ≤ B := by
    intro z
    by_cases hz : 0 ≤ z.im
    · have hre : 0 ≤ ((-I) * z).re := by
        simpa [Complex.mul_re] using hz
      have h := hright f hf hgrowth hreal ((-I) * z) hre
      simpa [← mul_assoc] using h
    · have hre : 0 ≤ (I * z).re := by
        simpa only [Complex.I_mul_re] using neg_nonneg.2 (le_of_not_ge hz)
      have h := hright (fun w : ℂ => f (-w)) hnegdiff hneggrowth hnegreal (I * z) hre
      simpa [← mul_assoc] using h
  have hb : Bornology.IsBounded (Set.range f) := by
    refine isBounded_iff_forall_norm_le.2 ⟨B, ?_⟩
    rintro w ⟨z, rfl⟩
    exact hplane z
  exact fun z => hf.apply_eq_apply_of_bounded hb z 0

/-- Reflection and a zero limit on the positive real ray supply real-axis
boundedness, so a zero exponential type entire function is identically zero. -/
theorem eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℂ,
      ‖f z‖ ≤ A * Real.exp (ε * ‖z‖))
    (hreflection : ∀ z : ℂ, f (1 - z) = f z)
    (hlimit : Tendsto (fun x : ℝ => f (x : ℂ)) atTop (𝓝 0)) :
    f = 0 := by
  have htail : ∀ᶠ x : ℝ in atTop, ‖f (x : ℂ)‖ ≤ 1 :=
    hlimit.norm.eventually (ge_mem_nhds (by simp))
  obtain ⟨R, hR⟩ := eventually_atTop.1 htail
  have hcontinuous : Continuous (fun x : ℝ => f (x : ℂ)) :=
    hf.continuous.comp Complex.continuous_ofReal
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (1 - R) R)).exists_bound_of_continuousOn
      hcontinuous.continuousOn
  have hreal : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ max 1 C := by
    intro x
    by_cases hx : R ≤ x
    · exact (hR x hx).trans (le_max_left _ _)
    · by_cases hx' : R ≤ 1 - x
      · have hfx : ‖f (x : ℂ)‖ ≤ 1 := by
          simpa only [Complex.ofReal_sub, Complex.ofReal_one, hreflection]
            using hR (1 - x) hx'
        exact hfx.trans (le_max_left _ _)
      · exact (hC x ⟨by linarith, le_of_not_ge hx⟩).trans (le_max_right _ _)
  have hconstant : ∀ z : ℂ, f z = f 0 :=
    eq_at_zero_of_zero_exponential_type_of_bounded_real hf hgrowth hreal
  have hconstant_limit : Tendsto (fun x : ℝ => f (x : ℂ)) atTop (𝓝 (f 0)) := by
    simpa only [hconstant] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => f 0) atTop (𝓝 (f 0)))
  have hzero : f 0 = 0 := tendsto_nhds_unique hconstant_limit hlimit
  funext z
  exact (hconstant z).trans hzero

end D5.S3.Analytic.Entire
