/- GID: D5/S3/Weil/ZetaCore/CertifiedStickyMatrix
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaCore/CertifiedStickyMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A conservative finite lower form certifies Schur and full block positivity. -/

import D5.S3.Weil.ZetaLinear.ExactStickyReduction

/-!
# Certified sticky matrix

The conservative finite form subtracts the explicit gap-controlled coupling
bound.  Cauchy-Schwarz promotes its positivity to Schur positivity, after which
the exact sticky reduction gives positivity of the full block energy.
-/

noncomputable section

namespace D5.S3.Weil.ZetaCore.CertifiedStickyMatrix

open D5.S3.Weil.ZetaLinear.ExactStickyReduction

/-- Positivity of the conservative finite lower form implies positivity of the
Schur complement, and Schur positivity implies positivity of the full block. -/
theorem certified_sticky_matrix
    {HP HQ : Type*}
    [NormedAddCommGroup HP] [InnerProductSpace ℝ HP]
    [NormedAddCommGroup HQ] [InnerProductSpace ℝ HQ]
    (APP : HP →ₗ[ℝ] HP) (AQP : HP →ₗ[ℝ] HQ)
    (AQQ : HQ →ₗ[ℝ] HQ) (AQQInv : HQ →ₗ[ℝ] HQ)
    (delta : ℝ) (hDelta : 0 < delta)
    (hQQGap : ∀ q, delta * ‖q‖ ^ 2 <= inner ℝ (AQQ q) q)
    (hQQSymm : ∀ x y, inner ℝ (AQQ x) y = inner ℝ x (AQQ y))
    (hQQInv : AQQ.comp AQQInv = LinearMap.id) :
    ((∀ p, 0 <= inner ℝ (APP p) p - delta⁻¹ * ‖AQP p‖ ^ 2) ->
        ∀ p, 0 <= schurEnergy APP AQP AQQ AQQInv p) ∧
      ((∀ p, 0 <= schurEnergy APP AQP AQQ AQQInv p) ->
        ∀ z, 0 <= blockEnergy APP AQP AQQ z) := by
  constructor
  · intro hG p
    let r : HQ := AQQInv (AQP p)
    have hInv : AQQ r = AQP p := by
      unfold r
      exact DFunLike.congr_fun hQQInv (AQP p)
    have hGapR := hQQGap r
    have hCauchy : inner ℝ (AQP p) r <= ‖AQP p‖ * ‖r‖ :=
      real_inner_le_norm (AQP p) r
    have hDeltaNorm : delta * ‖r‖ <= ‖AQP p‖ := by
      by_cases hr : ‖r‖ = 0
      · simp [hr]
      · have hrPositive : 0 < ‖r‖ :=
          lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr)
        rw [hInv] at hGapR
        nlinarith
    have hScaledInner :
        delta * inner ℝ (AQQ r) r <= ‖AQP p‖ ^ 2 := by
      calc
        delta * inner ℝ (AQQ r) r =
            delta * inner ℝ (AQP p) r := by rw [hInv]
        _ <= delta * (‖AQP p‖ * ‖r‖) :=
          mul_le_mul_of_nonneg_left hCauchy hDelta.le
        _ = ‖AQP p‖ * (delta * ‖r‖) := by ring
        _ <= ‖AQP p‖ * ‖AQP p‖ :=
          mul_le_mul_of_nonneg_left hDeltaNorm (norm_nonneg _)
        _ = ‖AQP p‖ ^ 2 := by ring
    have hSelfBound :
        inner ℝ (AQQ r) r <= delta⁻¹ * ‖AQP p‖ ^ 2 := by
      have hDiv : inner ℝ (AQQ r) r <= ‖AQP p‖ ^ 2 / delta :=
        (le_div_iff₀ hDelta).2 (by
          simpa only [mul_comm] using hScaledInner)
      simpa only [div_eq_mul_inv, mul_comm] using hDiv
    have hGp := hG p
    change 0 <= inner ℝ (APP p) p - inner ℝ (AQQ r) r
    linarith
  · intro hF
    have hQQNonneg : ∀ q, 0 <= inner ℝ (AQQ q) q := by
      intro q
      exact (mul_nonneg hDelta.le (sq_nonneg ‖q‖)).trans (hQQGap q)
    exact (exact_sticky_reduction APP AQP AQQ AQQInv
      hQQNonneg hQQSymm hQQInv).1.mpr hF

end D5.S3.Weil.ZetaCore.CertifiedStickyMatrix
