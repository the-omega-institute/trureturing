/- GID: D5/S0/Tower/NonPisotFrontier/EscapeIteration
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/EscapeIteration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Past the threshold the excess multiplies by the conjugate modulus. -/

import D5.S0.Tower.NonPisotFrontier.EscapeThreshold

/- Library-search audit trail (2026-08-18):
   * Repository search found the threshold and its defining identity; nothing
     iterates the escape step.
   * The multiplier identity below is exactly the threshold identity rearranged,
     so no new arithmetic about the base is needed. -/

namespace D5.S0.Tower.NonPisotFrontier.EscapeIteration

open D5.S0.Tower.NonPisotFrontier.BetaThirteen
open D5.S0.Tower.NonPisotFrontier.EscapeThreshold

local notation "β'" => betaThirteenConjugate
local notation "K" => escapeThreshold

/-- The threshold identity, rearranged: the conjugate modulus carries the
threshold to the threshold plus two. -/
theorem modulus_times_threshold : |β'| * K - 2 = K := by
  have h := escapeThreshold_spec
  nlinarith [h]

/-- One step past the threshold multiplies the excess by the conjugate modulus.
Stated with the excess named, this is the whole content of the escape: distance
above the threshold cannot shrink, and grows by a fixed factor above one. -/
theorem excess_multiplies {x d : Real} (hx : K < |x|) (hd0 : 0 ≤ d)
    (hd2 : d ≤ 2) : K + |β'| * (|x| - K) ≤ |β' * x - d| := by
  have hmt := modulus_times_threshold
  have hstep : |β'| * |x| - 2 ≤ |β' * x - d| := by
    have h1 : |β' * x| - |d| ≤ |β' * x - d| := by
      simpa using abs_sub_abs_le_abs_sub (β' * x) d
    rw [abs_mul, abs_of_nonneg hd0] at h1
    linarith
  have hexpand : |β'| * |x| - 2 = K + |β'| * (|x| - K) := by
    have : |β'| * |x| - 2 = (|β'| * K - 2) + |β'| * (|x| - K) := by ring
    rw [this, hmt]
  linarith [hexpand, hstep]

/-- The excess is positive past the threshold, so the multiplier is applied to
something strictly positive. -/
theorem excess_pos {x : Real} (hx : K < |x|) : 0 < |x| - K := by linarith

/-- The image is still past the threshold, so the step can be applied again. -/
theorem stays_past {x d : Real} (hx : K < |x|) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    K < |β' * x - d| := by
  have hmul := excess_multiplies hx hd0 hd2
  have hpos := excess_pos hx
  have hgt := one_lt_abs_betaThirteenConjugate
  nlinarith [hmul, hpos, hgt]

/-- The escape, packaged: past the threshold every admissible digit leaves the
image past the threshold, with the excess multiplied by at least the conjugate
modulus, which exceeds one. -/
theorem escape_iterates :
    1 < |β'| ∧
      ∀ x d : Real, K < |x| → 0 ≤ d → d ≤ 2 →
        K < |β' * x - d| ∧ K + |β'| * (|x| - K) ≤ |β' * x - d| :=
  ⟨one_lt_abs_betaThirteenConjugate,
    fun _ _ hx hd0 hd2 => ⟨stays_past hx hd0 hd2, excess_multiplies hx hd0 hd2⟩⟩

end D5.S0.Tower.NonPisotFrontier.EscapeIteration
