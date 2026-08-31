/- GID: D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stable swap curvature is linear-quadratic in residual local factors. -/

import Mathlib.Tactic

/-!
# Stable residual swap-curvature bound

In one stable memory eigenchannel, write a residual local factor as `1 + r`
and its memory injection as `r * v`. Exchanging two such local updates produces
a curvature that splits into a term linear in the residuals and a term
quadratic in them.

If both channel vectors have norm at most one, the curvature is bounded by the
linear residual envelope plus a quadratic correction. A common residual bound
`epsilon` then gives the explicit estimate

`2 * ‖stable - 1‖ * epsilon + 2 * epsilon ^ 2`.

This is a finite norm estimate. It does not construct an all-order extraction
tower, prove that the residual envelope tends to zero, or make a statement
about the location of zeta zeros.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.StableResidualSwapCurvatureBound

universe u

variable {K : Type u} [NormedField K]

/-- The stable-channel adjacent-swap defect after writing local factors as
`1 + residual` and memory injections as `residual * channel`. -/
def stableResidualSwapCurvature
    (stable residualP residualQ channelP channelQ : K) : K :=
  (stable - (1 + residualQ)) * (residualP * channelP) -
    (stable - (1 + residualP)) * (residualQ * channelQ)

/--
Stable residual swap curvature has an exact linear-quadratic decomposition.
Unit-bounded channels give a direct norm bound, and a common residual envelope
gives a uniform quadratic estimate.
-/
theorem stable_residual_swap_curvature_bound
    (stable residualP residualQ channelP channelQ : K)
    (hChannelP : ‖channelP‖ ≤ 1)
    (hChannelQ : ‖channelQ‖ ≤ 1) :
    stableResidualSwapCurvature
        stable residualP residualQ channelP channelQ =
      (stable - 1) *
          (residualP * channelP - residualQ * channelQ) +
        residualP * residualQ * (channelQ - channelP) ∧
    ‖stableResidualSwapCurvature
        stable residualP residualQ channelP channelQ‖ ≤
      ‖stable - 1‖ * (‖residualP‖ + ‖residualQ‖) +
        2 * (‖residualP‖ * ‖residualQ‖) ∧
    ∀ envelope : ℝ,
      0 ≤ envelope →
      ‖residualP‖ ≤ envelope →
      ‖residualQ‖ ≤ envelope →
      ‖stableResidualSwapCurvature
          stable residualP residualQ channelP channelQ‖ ≤
        2 * ‖stable - 1‖ * envelope + 2 * envelope ^ 2 := by
  have hExact :
      stableResidualSwapCurvature
          stable residualP residualQ channelP channelQ =
        (stable - 1) *
            (residualP * channelP - residualQ * channelQ) +
          residualP * residualQ * (channelQ - channelP) := by
    unfold stableResidualSwapCurvature
    ring
  have hInjectionBound :
      ‖residualP * channelP - residualQ * channelQ‖ ≤
        ‖residualP‖ + ‖residualQ‖ := by
    calc
      ‖residualP * channelP - residualQ * channelQ‖ ≤
          ‖residualP * channelP‖ + ‖residualQ * channelQ‖ :=
        norm_sub_le _ _
      _ = ‖residualP‖ * ‖channelP‖ +
          ‖residualQ‖ * ‖channelQ‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ ‖residualP‖ * 1 + ‖residualQ‖ * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hChannelP (norm_nonneg residualP))
          (mul_le_mul_of_nonneg_left hChannelQ (norm_nonneg residualQ))
      _ = ‖residualP‖ + ‖residualQ‖ := by ring
  have hChannelDifference :
      ‖channelQ - channelP‖ ≤ 2 := by
    calc
      ‖channelQ - channelP‖ ≤ ‖channelQ‖ + ‖channelP‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hChannelQ hChannelP
      _ = 2 := by norm_num
  have hBound :
      ‖stableResidualSwapCurvature
          stable residualP residualQ channelP channelQ‖ ≤
        ‖stable - 1‖ * (‖residualP‖ + ‖residualQ‖) +
          2 * (‖residualP‖ * ‖residualQ‖) := by
    rw [hExact]
    calc
      ‖(stable - 1) *
            (residualP * channelP - residualQ * channelQ) +
          residualP * residualQ * (channelQ - channelP)‖ ≤
          ‖(stable - 1) *
            (residualP * channelP - residualQ * channelQ)‖ +
          ‖residualP * residualQ * (channelQ - channelP)‖ :=
        norm_add_le _ _
      _ = ‖stable - 1‖ *
            ‖residualP * channelP - residualQ * channelQ‖ +
          (‖residualP‖ * ‖residualQ‖) * ‖channelQ - channelP‖ := by
        simp only [norm_mul]
      _ ≤ ‖stable - 1‖ * (‖residualP‖ + ‖residualQ‖) +
          (‖residualP‖ * ‖residualQ‖) * 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hInjectionBound
            (norm_nonneg (stable - 1)))
          (mul_le_mul_of_nonneg_left hChannelDifference
            (mul_nonneg (norm_nonneg residualP) (norm_nonneg residualQ)))
      _ = ‖stable - 1‖ * (‖residualP‖ + ‖residualQ‖) +
          2 * (‖residualP‖ * ‖residualQ‖) := by ring
  have hEnvelope :
      ∀ envelope : ℝ,
        0 ≤ envelope →
        ‖residualP‖ ≤ envelope →
        ‖residualQ‖ ≤ envelope →
        ‖stableResidualSwapCurvature
            stable residualP residualQ channelP channelQ‖ ≤
          2 * ‖stable - 1‖ * envelope + 2 * envelope ^ 2 := by
    intro envelope hEnvelopeNonnegative hResidualP hResidualQ
    have hSum :
        ‖residualP‖ + ‖residualQ‖ ≤ 2 * envelope := by
      linarith
    have hProduct :
        ‖residualP‖ * ‖residualQ‖ ≤ envelope ^ 2 := by
      calc
        ‖residualP‖ * ‖residualQ‖ ≤ envelope * envelope :=
          mul_le_mul hResidualP hResidualQ
            (norm_nonneg residualQ) hEnvelopeNonnegative
        _ = envelope ^ 2 := by ring
    calc
      ‖stableResidualSwapCurvature
          stable residualP residualQ channelP channelQ‖ ≤
          ‖stable - 1‖ * (‖residualP‖ + ‖residualQ‖) +
            2 * (‖residualP‖ * ‖residualQ‖) := hBound
      _ ≤ ‖stable - 1‖ * (2 * envelope) +
          2 * envelope ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hSum (norm_nonneg (stable - 1)))
          (mul_le_mul_of_nonneg_left hProduct (by norm_num))
      _ = 2 * ‖stable - 1‖ * envelope + 2 * envelope ^ 2 := by ring
  exact ⟨hExact, hBound, hEnvelope⟩

#print axioms stable_residual_swap_curvature_bound

end D5.S3.Observer.AgencyHolonomy.StableResidualSwapCurvatureBound
