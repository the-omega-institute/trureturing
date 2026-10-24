/- GID: D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity
   generality: I
   mirror-B: D5/B/S3/Analytic/Zeta/ZetaLogDerivativeRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized zeta logarithmic derivatives are regular on the real axis. -/

import D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation
import D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite
import D5.S3.Weil.GoldenCriticalSpectrum.EulerPronyArithmeticRealization
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! The normalized zeta factor removes the pole at one and preserves the
local multiplicities of every nontrivial zero. -/

namespace D5.S3.Analytic.Zeta.ZetaLogDerivativeRegularity

open Filter Set
open scoped Topology
open ZetaAsymptotics
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.Convention
open D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation
open D5.S3.Weil.GoldenCriticalSpectrum.EulerPronyArithmeticRealization

noncomputable section

/-- The zeta principal term with the pole at one removed before translation. -/
def regularizedPrincipal (s : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * (deriv riemannZeta₁ (s + 1 / 2) / riemannZeta₁ (s + 1 / 2))

lemma normalized_zeta_ne_zero_real {x : ℝ} (hx : 0 < x) :
    riemannZeta₁ (x : ℂ) ≠ 0 := by
  by_cases hx1 : x = 1
  · simp [hx1]
  have hc1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx1
  have hζ : riemannZeta (x : ℂ) ≠ 0 := by
    rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · exact riemannZeta_ne_zero_of_real_mem_Ioo x hx hlt
    · exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hgt)
  intro h
  apply hζ
  rw [riemannZeta_eq_inv_sub_mul hc1, h, mul_zero]

/-- Away from the pole and the zeros, the normalized logarithmic derivative
equals the signed zeta logarithmic derivative with its density pole cancelled. -/
theorem regularizedPrincipal_eq {s : ℂ} (hs : s ≠ 1 / 2)
    (hζ : riemannZeta (s + 1 / 2) ≠ 0) :
    regularizedPrincipal s = -(1 / 2 : ℂ) *
      (deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2)) -
        1 / (2 * (s - 1 / 2)) := by
  have hs1 : s + (1 / 2 : ℂ) ≠ 1 := by
    intro h
    apply hs
    linear_combination h
  have hnormalized : riemannZeta₁ (s + 1 / 2) ≠ 0 := by
    intro h
    apply hζ
    rw [riemannZeta_eq_inv_sub_mul hs1, h, mul_zero]
  have hlog : deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2) =
      -(s + 1 / 2 - 1)⁻¹ +
        deriv riemannZeta₁ (s + 1 / 2) / riemannZeta₁ (s + 1 / 2) := by
    generalize heq : s + (1 / 2 : ℂ) = z at hs1 hnormalized ⊢
    rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1,
      riemannZeta_eq_inv_sub_mul hs1]
    field_simp [hnormalized, sub_ne_zero.mpr hs1]
  unfold regularizedPrincipal
  rw [hlog, show s + (1 / 2 : ℂ) - 1 = s - 1 / 2 by ring]
  field_simp [sub_ne_zero.mpr hs]
  ring

/-- The cancelled principal term is analytic at every nonnegative real point. -/
theorem regularizedPrincipal_analyticAt_real {σ : ℝ} (hσ : 0 ≤ σ) :
    AnalyticAt ℂ regularizedPrincipal (σ : ℂ) := by
  have hne : riemannZeta₁ ((σ : ℂ) + 1 / 2) ≠ 0 := by
    have h := normalized_zeta_ne_zero_real (x := σ + 1 / 2) (by linarith)
    convert h using 1 <;> push_cast <;> ring
  have ha := differentiable_riemannZeta₁.analyticAt ((σ : ℂ) + 1 / 2)
  have hshift : AnalyticAt ℂ (fun s : ℂ => s + 1 / 2) (σ : ℂ) := by fun_prop
  exact analyticAt_const.mul
    (AnalyticAt.comp (f := fun s : ℂ => s + 1 / 2) (ha.deriv.div ha hne) hshift)

private lemma shift_half_tendsto (rho : ℂ) :
    Tendsto (fun s : ℂ => s + 1 / 2)
      (𝓝[≠] (rho - 1 / 2)) (𝓝[≠] rho) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hc : Continuous (fun s : ℂ => s + (1 / 2 : ℂ)) := by fun_prop
    simpa only [sub_add_cancel] using
      (hc.tendsto (rho - (1 / 2 : ℂ))).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change s + (1 / 2 : ℂ) ≠ rho
    intro heq
    have heq' : s = rho - 1 / 2 := by linear_combination heq
    exact hs heq'

/-- A translated nontrivial zero is isolated for the normalized zeta factor. -/
theorem normalized_zeta_eventually_ne_zero {rho : ℂ} (hρ : IsNontrivialZero rho) :
    ∀ᶠ s in 𝓝[≠] (rho - 1 / 2), riemannZeta₁ (s + 1 / 2) ≠ 0 := by
  obtain ⟨m, hm⟩ :=
    D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite.exists_multiplicity hρ
  have hζne : ∀ᶠ z in 𝓝[≠] rho, riemannZeta z ≠ 0 := by
    obtain ⟨v, hv, hv0, hfactor⟩ := hm.2
    filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (hv.continuousAt.eventually_ne hv0),
      self_mem_nhdsWithin] with z hz hvz hzne
    rw [show riemannZeta z = (z - rho) ^ m * v z from hz]
    exact mul_ne_zero (pow_ne_zero m (sub_ne_zero.mpr hzne)) hvz
  have hρ1 : rho ≠ 1 := by
    intro heq
    have h := hρ.2.2
    simp [heq] at h
  have hne1 : ∀ᶠ z in 𝓝 rho, z ≠ 1 := compl_singleton_mem_nhds hρ1
  filter_upwards [(shift_half_tendsto rho).eventually hζne,
    (shift_half_tendsto rho).eventually (Filter.Eventually.filter_mono nhdsWithin_le_nhds hne1)]
      with s hζs hs1
  intro h
  apply hζs
  rw [riemannZeta_eq_inv_sub_mul hs1, h, mul_zero]

/-- At every nontrivial zero, the translated principal term has residue equal
to minus one half of its positive integer multiplicity. -/
theorem regularizedPrincipal_zero_residue {rho : ℂ} (hρ : IsNontrivialZero rho) :
    ∃ m : ℕ, 0 < m ∧
      Tendsto (fun s : ℂ => (s - (rho - 1 / 2)) * regularizedPrincipal s)
        (𝓝[≠] (rho - 1 / 2)) (𝓝 (-(m : ℂ) / 2)) := by
  obtain ⟨m, hm⟩ :=
    D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite.exists_multiplicity hρ
  obtain ⟨u, hu, hu0, hpart⟩ := continued_euler_trace_principal_part hm
  have hcont : ContinuousAt (logDeriv u) rho :=
    hu.deriv.continuousAt.div hu.continuousAt hu0
  have hregular : Tendsto (fun z : ℂ => (z - rho) * logDeriv u z)
      (𝓝[≠] rho) (𝓝 0) := by
    have hid : Tendsto (fun z : ℂ => z - rho) (𝓝 rho) (𝓝 0) := by
      simpa using ((tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 rho) (𝓝 rho)).sub_const rho)
    simpa only [zero_mul] using (hid.mul hcont.tendsto).mono_left nhdsWithin_le_nhds
  have htrace : Tendsto (fun z : ℂ => (z - rho) * continuedEulerTrace z)
      (𝓝[≠] rho) (𝓝 (-(m : ℂ))) := by
    have hconstant : Tendsto (fun _ : ℂ => -(m : ℂ))
        (𝓝[≠] rho) (𝓝 (-(m : ℂ))) := tendsto_const_nhds
    have hlim := hconstant.sub hregular
    simp only [sub_zero] at hlim
    apply hlim.congr'
    filter_upwards [hpart, self_mem_nhdsWithin] with z hz hzne
    rw [hz]
    field_simp [sub_ne_zero.mpr hzne]
    <;> ring
  have hρ1 : rho ≠ 1 := by
    intro heq
    have h := hρ.2.2
    simp [heq] at h
  have hhalf : rho - (1 / 2 : ℂ) ≠ 1 / 2 := by
    intro heq
    apply hρ1
    linear_combination heq
  have hscalar : Tendsto (fun s : ℂ =>
      (s - (rho - 1 / 2)) * (1 / (2 * (s - 1 / 2))))
      (𝓝[≠] (rho - 1 / 2)) (𝓝 0) := by
    have hden : (2 : ℂ) * (rho - 1 / 2 - 1 / 2) ≠ 0 :=
      mul_ne_zero two_ne_zero (sub_ne_zero.mpr hhalf)
    have hc : ContinuousAt (fun s : ℂ => 1 / (2 * (s - 1 / 2))) (rho - 1 / 2) := by
      fun_prop (disch := exact hden)
    have hid : Tendsto (fun s : ℂ => s - (rho - 1 / 2))
        (𝓝 (rho - 1 / 2)) (𝓝 0) := by
      simpa using ((tendsto_id : Tendsto (fun s : ℂ => s)
        (𝓝 (rho - 1 / 2)) (𝓝 (rho - 1 / 2))).sub_const (rho - 1 / 2))
    simpa only [zero_mul] using (hid.mul hc.tendsto).mono_left nhdsWithin_le_nhds
  have hlim := ((htrace.comp (shift_half_tendsto rho)).const_mul (1 / 2 : ℂ)).sub hscalar
  refine ⟨m, hm.1, ?_⟩
  have hlim' : Tendsto (fun s : ℂ =>
      (1 / 2 : ℂ) * ((s + 1 / 2 - rho) * continuedEulerTrace (s + 1 / 2)) -
        (s - (rho - 1 / 2)) * (1 / (2 * (s - 1 / 2))))
      (𝓝[≠] (rho - 1 / 2)) (𝓝 (-(m : ℂ) / 2)) := by
    convert hlim using 1 <;> congr 1 <;> ring
  apply hlim'.congr'
  have hnehalf : ∀ᶠ s in 𝓝 (rho - 1 / 2), s ≠ 1 / 2 :=
    compl_singleton_mem_nhds hhalf
  filter_upwards [normalized_zeta_eventually_ne_zero hρ,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hnehalf] with s hnormalized hs
  have hs1 : s + (1 / 2 : ℂ) ≠ 1 := by
    intro heq
    apply hs
    linear_combination heq
  have hζs : riemannZeta (s + 1 / 2) ≠ 0 := by
    rw [riemannZeta_eq_inv_sub_mul hs1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs1)) hnormalized
  rw [regularizedPrincipal_eq hs hζs]
  unfold continuedEulerTrace logDeriv classicalZeta
  simp only [Pi.div_apply]
  ring

#print axioms regularizedPrincipal_eq
#print axioms normalized_zeta_ne_zero_real
#print axioms regularizedPrincipal_analyticAt_real
#print axioms normalized_zeta_eventually_ne_zero
#print axioms regularizedPrincipal_zero_residue

end
end D5.S3.Analytic.Zeta.ZetaLogDerivativeRegularity
