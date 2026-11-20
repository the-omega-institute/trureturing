/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The analytic expression for the complete Mangoldt transform has a simple pole at each zeta zero with residue its full multiplicity divided by rho times one minus rho. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Residues

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes

namespace D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent

/-- The explicit analytic side of the arithmetic Laplace transform. -/
def transform (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) -
    1 / (s - 1)^2 + ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) / (s - 1)

/-- One function represents the convergent integral on the original half-plane
and has the indicated Laurent principal part at every actual zeta zero. -/
theorem transform_integral_and_zero_germs :
    let Φ := transform
    (∀ s : ℂ, 1 < s.re →
      IntegrableOn (fun y : ℝ => Complex.exp (-s*y) * (U (Real.exp y) : ℂ)) (Ioi 0) ∧
      (∫ y : ℝ in Ioi 0, Complex.exp (-s*y) * (U (Real.exp y) : ℂ)) = Φ s) ∧
    ∀ ρ : ℂ, riemannZeta ρ = 0 →
      analyticOrderNatAt riemannZeta ρ ≠ 0 ∧
      (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ)) ≠ 0 ∧
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, Φ s =
          ((analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))) / (s - ρ) + H s := by
  refine ⟨fun _ hs => CompleteMangoldtHalfPlane.u_laplace_half_plane hs, ?_⟩
  intro ρ hζ
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp [riemannZeta_zero] at hζ
  have hρ1 : ρ ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hζ
  let m := analyticOrderNatAt riemannZeta ρ
  have hm : m ≠ 0 := analyticOrderNatAt_riemannZeta_ne_zero hζ hρ1
  have hdρ : ρ * (1-ρ) ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1.symm)
  refine ⟨hm, div_ne_zero (Nat.cast_ne_zero.mpr hm) hdρ, ?_⟩
  obtain ⟨u, hu, hu0, heq⟩ := (_root_.analyticAt_riemannZeta hρ1).analyticOrderAt_ne_top.mp
    (analyticOrderAt_riemannZeta_ne_top hρ1)
  have hlog := eventually_logDeriv_riemannZeta_eq_near_zero hm hu hu0 heq
  let H := fun s : ℂ =>
    (m : ℂ) * (s + ρ - 1) / ((s*(1-s))*(ρ*(1-ρ))) +
    (deriv u s / u s) / (s*(1-s)) -
    1/(s-1)^2 + ((1+Real.eulerMascheroniConstant : ℝ) : ℂ)/(s-1)
  refine ⟨H, ?_, ?_⟩
  · have hden : AnalyticAt ℂ (fun s : ℂ => s*(1-s)) ρ :=
      analyticAt_id.mul (analyticAt_const.sub analyticAt_id)
    have hmterm : AnalyticAt ℂ (fun s : ℂ =>
        (m : ℂ) * (s + ρ - 1) / ((s*(1-s))*(ρ*(1-ρ)))) ρ :=
      (analyticAt_const.mul ((analyticAt_id.add analyticAt_const).sub analyticAt_const)).div
        (hden.mul analyticAt_const) (mul_ne_zero hdρ hdρ)
    have hulog := (hu.deriv.div hu hu0).div hden hdρ
    have hshift : AnalyticAt ℂ (fun s : ℂ => s-1) ρ := analyticAt_id.sub analyticAt_const
    have hs1 := sub_ne_zero.mpr hρ1
    exact (((hmterm.add hulog).sub (analyticAt_const.div (hshift.pow 2) (pow_ne_zero 2 hs1))).add
      (analyticAt_const.div hshift hs1))
  · have havoid : ∀ᶠ s in 𝓝 ρ, s ≠ 0 ∧ s ≠ 1 :=
      (continuousAt_id.eventually_ne hρ0).and (continuousAt_id.eventually_ne hρ1)
    filter_upwards [hlog, nhdsWithin_le_nhds havoid, self_mem_nhdsWithin] with s hlogS hs hsr
    have hsr' : s - ρ ≠ 0 := sub_ne_zero.mpr hsr
    have hs1 := sub_ne_zero.mpr hs.2
    unfold transform
    rw [neg_div, hlogS]
    dsimp only [H]
    field_simp [hs.1, hρ0, sub_ne_zero.mpr hρ1.symm, sub_ne_zero.mpr hs.2.symm, hs1, hsr',
      sub_ne_zero.mpr hρ1]
    ring

end D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
