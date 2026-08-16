/- GID: D5/S3/ResourceOrder/LiquidityReserveBound
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/LiquidityReserveBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonincreasing price curve has nonnegative liquidity reserve. -/

/- Library-search audit trail (2026-08-16):
   * Pinned Mathlib and Loogle both return `intervalIntegral.integral_mono_on`
     as the exact interval-integral comparison theorem used below.
   * Pinned Mathlib also supplies `Antitone.intervalIntegrable`,
     `intervalIntegral.integral_const`, and `intervalIntegral.integral_sub`.
   * Repository searches found no D5 theorem about a nonincreasing price curve's
     liquidity reserve. The LeanSearch API request failed, so it is not counted
     as a negative search result.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace D5.S3.ResourceOrder.LiquidityReserveBound

/-- The accumulated cost under a nonincreasing price curve is at most the
initial price times the traded quantity. Its shortfall from that rectangle is
the integral of the pointwise price drop and is therefore nonnegative. -/
theorem liquidity_reserve_nonnegative
    (P : Real -> Real) (hP : Antitone P) (Q : Real) (hQ : 0 <= Q) :
    (∫ x in (0 : Real)..Q, P x) <= P 0 * Q ∧
      P 0 * Q - (∫ x in (0 : Real)..Q, P x) =
        ∫ x in (0 : Real)..Q, (P 0 - P x) ∧
      0 <= P 0 * Q - (∫ x in (0 : Real)..Q, P x) := by
  have hPint : IntervalIntegrable P volume 0 Q := hP.intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : Real => P 0) volume 0 Q :=
    intervalIntegrable_const
  have hbound : (∫ x in (0 : Real)..Q, P x) <= ∫ _ in (0 : Real)..Q, P 0 := by
    apply intervalIntegral.integral_mono_on hQ hPint hconst
    intro x hx
    exact hP hx.1
  have hcost : (∫ x in (0 : Real)..Q, P x) <= P 0 * Q := by
    simpa [mul_comm] using hbound
  refine ⟨hcost, ?_, sub_nonneg.mpr hcost⟩
  calc
    P 0 * Q - (∫ x in (0 : Real)..Q, P x) =
        (∫ _ in (0 : Real)..Q, P 0) - ∫ x in (0 : Real)..Q, P x := by
          simp [mul_comm]
    _ = ∫ x in (0 : Real)..Q, (P 0 - P x) := by
      rw [intervalIntegral.integral_sub hconst hPint]

#print axioms liquidity_reserve_nonnegative

end D5.S3.ResourceOrder.LiquidityReserveBound
