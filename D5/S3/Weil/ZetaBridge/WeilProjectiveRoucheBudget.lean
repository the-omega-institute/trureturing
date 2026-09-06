/- GID: D5/S3/Weil/ZetaBridge/WeilProjectiveRoucheBudget
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilProjectiveRoucheBudget
   mirror-E: none(waiver:variational-to-analytic-boundary-transport)
   anchors: []
   digest: Transport the complex projective Rayleigh enclosure through bounded linear observations and a finite boundary mesh to the existing rectangle Rouche zero-count theorem. -/

import D5.S3.Weil.ZetaBridge.WeilProjectiveRayleighCapture
import D5.S3.Weil.ZetaAnalytic.RoucheZeroCount
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# A squared variational budget for rectangle zero counts

The readout is a family of actual continuous linear functionals on H.
The eigenmode error is derived from the preceding operator-domain theorem.
A finite mesh and a certified modulus of variation give the boundary floor.
The acceptance inequality uses only products and squares:

  K^2 * (upper-lower) < (sampleFloor-lip*mesh)^2 * (threshold-lower).

Analyticity of the actual readouts, their norm bound, the mesh cover and its
variation certificate are explicit hypotheses. They are not inferred from
finite sampling or from a citation. A concrete Fourier/L2 implementation
must discharge those obligations separately.

The zero-count theorem is the existing RoucheZeroCount owner. No new
zero-count definition or Riemann-hypothesis premise is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilProjectiveRoucheBudget

open Complex Set
open D5.S3.Weil.ZetaBridge.WeilProjectiveRayleighCapture
open D5.S3.Weil.ZetaAnalytic.RoucheZeroCount
open scoped InnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem norm_readout_lt_of_square_budget
    (L : H →L[ℂ] ℂ) (x : H) (K gap width eta : ℝ)
    (hL : ‖L‖ ≤ K) (hgap : 0 < gap) (heta : 0 < eta)
    (hx : gap * ‖x‖ ^ 2 ≤ width)
    (hbudget : K ^ 2 * width < eta ^ 2 * gap) :
    ‖L x‖ < eta := by
  have hnorm : ‖L x‖ ≤ K * ‖x‖ :=
    (L.le_opNorm x).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg x))
  have hsq : ‖L x‖ ^ 2 ≤ (K * ‖x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have h1 := mul_le_mul_of_nonneg_left hsq hgap.le
  have h2 := mul_le_mul_of_nonneg_left hx (sq_nonneg K)
  have h3 : gap * ‖L x‖ ^ 2 < gap * eta ^ 2 := by nlinarith
  have h4 : ‖L x‖ ^ 2 < eta ^ 2 := (mul_lt_mul_left hgap).mp h3
  nlinarith [norm_nonneg (L x)]

/-- Certified mesh coverage and variation transport the finite sampled floor
to every boundary point. Sampling alone is insufficient. -/
theorem finite_mesh_modulus_floor
    (g : ℂ → ℂ) (boundary : Set ℂ) (samples : Finset ℂ)
    (mesh lip sampleFloor : ℝ) (hlip : 0 ≤ lip)
    (hcover : ∀ z ∈ boundary, ∃ t ∈ samples, dist z t ≤ mesh)
    (hsamples : ∀ t ∈ samples, sampleFloor ≤ ‖g t‖)
    (hvariation : ∀ z ∈ boundary, ∀ t ∈ samples,
      ‖g z - g t‖ ≤ lip * dist z t) :
    ∀ z ∈ boundary, sampleFloor - lip * mesh ≤ ‖g z‖ := by
  intro z hz
  obtain ⟨t, ht, hdist⟩ := hcover z hz
  have hv := (hvariation z hz t ht).trans
    (mul_le_mul_of_nonneg_left hdist hlip)
  have hn := norm_sub_norm_le (g t) (g z)
  rw [norm_sub_rev] at hn
  have hm := hsamples t ht
  linarith

/-- A Hilbert-space error budget and finite sampled boundary certificate
produce the strict Rouche inequality for the actual linear readouts. -/
theorem variational_mesh_rouche_boundary
    (readout : ℂ → H →L[ℂ] ℂ) (v k : H) (boundary : Set ℂ)
    (samples : Finset ℂ) (gap width K mesh lip sampleFloor : ℝ)
    (hgap : 0 < gap) (hlip : 0 ≤ lip)
    (hfloor : 0 < sampleFloor - lip * mesh)
    (herror : gap * ‖v - k‖ ^ 2 ≤ width)
    (hreadout : ∀ z ∈ boundary, ‖readout z‖ ≤ K)
    (hcover : ∀ z ∈ boundary, ∃ t ∈ samples, dist z t ≤ mesh)
    (hsamples : ∀ t ∈ samples, sampleFloor ≤ ‖readout t k‖)
    (hvariation : ∀ z ∈ boundary, ∀ t ∈ samples,
      ‖readout z k - readout t k‖ ≤ lip * dist z t)
    (hbudget : K ^ 2 * width < (sampleFloor - lip * mesh) ^ 2 * gap) :
    ∀ z ∈ boundary, ‖readout z v - readout z k‖ < ‖readout z k‖ := by
  have hmodulus := finite_mesh_modulus_floor (fun z => readout z k)
    boundary samples mesh lip sampleFloor hlip hcover hsamples hvariation
  intro z hz
  have herr := norm_readout_lt_of_square_budget (readout z) (v - k)
    K gap width (sampleFloor - lip * mesh) (hreadout z hz) hgap hfloor herror hbudget
  rw [map_sub] at herr
  exact herr.trans_le (hmodulus z hz)

/-- Compose the derived complex eigenmode enclosure with the finite mesh and
the existing rectangle Rouche theorem. The actual readout functions and their
analytic multiplicities occur in the conclusion; no target-only replacement
of the eigenmode is used. -/
theorem rectangle_zero_count_eq_of_projective_rayleigh
    {D : Type*} [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] H) (k u : D)
    (lower upper threshold lam : ℝ)
    (hsymmetric : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0)
    (heigen : A u = (lam : ℂ) • ι u)
    (hlower : lower ≤ lam) (hlam : lam < threshold)
    (hupper : (⟪ι k, A k⟫_ℂ).re ≤ upper)
    (hthreshold : upper < threshold)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re)
    (readout : ℂ → H →L[ℂ] ℂ)
    (z w : ℂ) (hre : z.re < w.re) (him : z.im < w.im)
    (samples : Finset ℂ) (K mesh lip sampleFloor : ℝ)
    (hlip : 0 ≤ lip) (hfloor : 0 < sampleFloor - lip * mesh)
    (hreadout : ∀ s ∈ RectangleBorder z w, ‖readout s‖ ≤ K)
    (hcover : ∀ s ∈ RectangleBorder z w, ∃ t ∈ samples, dist s t ≤ mesh)
    (hsamples : ∀ t ∈ samples, sampleFloor ≤ ‖readout t (ι k)‖)
    (hvariation : ∀ s ∈ RectangleBorder z w, ∀ t ∈ samples,
      ‖readout s (ι k) - readout t (ι k)‖ ≤ lip * dist s t)
    (hbudget : K ^ 2 * (upper - lower) <
      (sampleFloor - lip * mesh) ^ 2 * (threshold - lower))
    (hf : AnalyticOnNhd ℂ
      (fun s => readout s (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u))) (Rectangle z w))
    (hg : AnalyticOnNhd ℂ (fun s => readout s (ι k)) (Rectangle z w))
    (Zf Zg : Finset ℂ)
    (hZf : ∀ s ∈ Rectangle z w,
      (readout s (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u)) = 0 ↔ s ∈ Zf))
    (hZfsub : (Zf : Set ℂ) ⊆ Rectangle z w)
    (hZg : ∀ s ∈ Rectangle z w, (readout s (ι k) = 0 ↔ s ∈ Zg))
    (hZgsub : (Zg : Set ℂ) ⊆ Rectangle z w) :
    ∑ rho ∈ Zf, analyticOrderNatAt
        (fun s => readout s (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u))) rho =
      ∑ rho ∈ Zg, analyticOrderNatAt (fun s => readout s (ι k)) rho := by
  obtain ⟨_, _, _, herror, _, _, _⟩ :=
    projective_rayleigh_enclosure ι A k u lower upper threshold lam
      hsymmetric hk hu heigen hlower hlam hupper hthreshold hcoercive
  have hgap : 0 < threshold - lower := by linarith
  have herror' : (threshold - lower) *
      ‖ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u) - ι k‖ ^ 2 ≤ upper - lower := by
    simpa only [map_sub] using herror
  have hboundary := variational_mesh_rouche_boundary readout
    (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u)) (ι k) (RectangleBorder z w) samples
    (threshold - lower) (upper - lower) K mesh lip sampleFloor
    hgap hlip hfloor herror' hreadout hcover hsamples hvariation hbudget
  exact rectangle_zero_count_eq_of_norm_sub_lt hre him hf hg hboundary
    Zf Zg hZf hZfsub hZg hZgsub

#print axioms finite_mesh_modulus_floor
#print axioms variational_mesh_rouche_boundary
#print axioms rectangle_zero_count_eq_of_projective_rayleigh

end D5.S3.Weil.ZetaBridge.WeilProjectiveRoucheBudget

end
