/- GID: D5/S3/Weil/ZetaBridge/WeilPrime3ProjectiveReadout
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilPrime3ProjectiveReadout
   mirror-E: none(waiver:conditional-analytic-certificate-consumer)
   anchors: []
   digest: Consume the exact prime-three Rayleigh certificate constants in a complex projective readout theorem. -/

import D5.S3.Observer.Hankel.ProjectiveReadoutSharpness
import Mathlib.Tactic.NormNum

/-!
Input constants are read from PR #5602 at
4ddc8bf4cc75b3c7581ec5c2a1dccca7f91007a3,
research/weil_ground_mode/prime3_refined_certificate.json,
Git blob d55cfc86e16019d22aa7c4e4ca758c01236f7b72.

This file proves the arithmetic and analytic CONSUMPTION of those constants.
It does not import the JSON as an axiom, re-run its interval verifier, prove
the full-space Fourier/domain bridge, or assert the arithmetic Weil operator
satisfies the input inequalities. Those hypotheses remain explicit below.
The fixed scale is a=log(3)/2; no increasing-scale estimate is inferred.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilPrime3ProjectiveReadout

open D5.S3.Observer.Hankel.ProjectiveRayleighReadout
open D5.S3.Observer.Hankel.ProjectiveReadoutSharpness
open scoped ComplexInnerProductSpace

/-- Exact numerical budget and a strict rational radius from the existing
fixed-window certificate. -/
theorem prime3_budget_arithmetic :
    ((560909 / 10000000000000 : ℝ) - 103 / 2000000000) /
        (1 / 200000 - 103 / 2000000000) = 15303 / 16495000 ∧
      (15303 / 16495000 : ℝ) < (61 / 2000) ^ 2 ∧
      (61 / 2000 : ℝ) < 1 := by
  norm_num

/-- Sharp closed-ball readout condition for the certificate's exact budget.
It is a single integer-coefficient inequality in two squared norms. -/
theorem prime3_error_ball_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (k g : H) (hk : ‖k‖ = 1) :
    (∀ w : H, ⟪k, w⟫_ℂ = 0 → ‖w‖ ^ 2 ≤ (15303 / 16495000 : ℝ) →
      ⟪g, k + w⟫_ℂ ≠ 0) ↔
        15303 * ‖g‖ ^ 2 < 16510303 * ‖⟪g, k⟫_ℂ‖ ^ 2 := by
  rw [robust_readout_angle_iff k g (15303 / 16495000) hk (by norm_num)]
  constructor <;> intro h <;> nlinarith

/-- Conditional consumer for the actual prime-three enclosure values. Once
the stated full operator-domain bounds are supplied, obtain a nonzero overlap,
a projective radius below 61/2000, goal-oriented errors for all readouts, and
nonzero actual eigenvector readouts under an explicit integer margin. -/
theorem prime3_capture_and_readouts
    {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] H) (k u : D) (lam : ℝ)
    (hsym : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0) (hAu : A u = (lam : ℂ) • ι u)
    (hlower : (103 / 2000000000 : ℝ) ≤ lam)
    (hlam : lam < (1 / 200000 : ℝ))
    (hupper : (⟪ι k, A k⟫_ℂ).re ≤ (560909 / 10000000000000 : ℝ))
    (hgap : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      (1 / 200000 : ℝ) * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    let alpha := ⟪ι k, ι u⟫_ℂ
    let w := ι (alpha⁻¹ • u - k)
    alpha ≠ 0 ∧ ⟪ι k, w⟫_ℂ = 0 ∧
      ‖w‖ ^ 2 ≤ (15303 / 16495000 : ℝ) ∧ ‖w‖ < (61 / 2000 : ℝ) ∧
      ∀ g : H,
        ‖⟪g, alpha⁻¹ • ι u⟫_ℂ - ⟪g, ι k⟫_ℂ‖ ^ 2 ≤
          (‖g‖ ^ 2 - ‖⟪g, ι k⟫_ℂ‖ ^ 2) * (15303 / 16495000 : ℝ) ∧
        (15303 * ‖g‖ ^ 2 < 16510303 * ‖⟪g, ι k⟫_ℂ‖ ^ 2 → ⟪g, ι u⟫_ℂ ≠ 0) := by
  obtain ⟨ha, ho, he, _, _⟩ := rayleigh_projective_enclosure ι A k u
    (103 / 2000000000) (560909 / 10000000000000) (1 / 200000) lam
    hsym hk hu hAu hlower hlam hupper (by norm_num) hgap
  rw [prime3_budget_arithmetic.1] at he
  let alpha := ⟪ι k, ι u⟫_ℂ
  let w := ι (alpha⁻¹ • u - k)
  have himage : ι k + w = alpha⁻¹ • ι u := by
    dsimp only [w]
    rw [map_sub, map_smul]
    abel
  have hradius : ‖w‖ < (61 / 2000 : ℝ) := by
    have hb := prime3_budget_arithmetic.2.1
    change ‖w‖ ^ 2 ≤ (15303 / 16495000 : ℝ) at he
    nlinarith [norm_nonneg w]
  refine ⟨ha, ho, he, hradius, ?_⟩
  intro g
  have herr := centered_readout_error_bound (ι k) g w (15303 / 16495000) hk ho he
  rw [himage] at herr
  refine ⟨herr, ?_⟩
  intro hmargin
  have hrob := (prime3_error_ball_iff (ι k) g hk).mpr hmargin
  have hn := hrob w ho he
  intro hz
  rw [himage, inner_smul_right, hz, mul_zero] at hn
  exact hn rfl

#print axioms prime3_budget_arithmetic
#print axioms prime3_capture_and_readouts

end D5.S3.Weil.ZetaBridge.WeilPrime3ProjectiveReadout
