/- GID: D5/S3/Axis/AxisRecurrencePair
   generality: I
   mirror-B: D5/B/S3/Axis/AxisRecurrencePair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The partial sum and the weight satisfy their two recurrences together. -/

import D5.S3.Axis.AxisPartialSum

namespace D5.S3.Axis.AxisRecurrencePair

open D5.S3.Axis.AxisTraceRecurrence
open D5.S3.Axis.AxisPartialSum

/-- The closed recurrence the source states as one clause: the partial sum steps by adding
the previous sum weighted by the next weight, and the weights themselves compose. Neither
half is restated; both were already proved, and what was missing is the statement that they
hold of the same pair of sequences at the same depth. -/
theorem axis_recurrence_pair (x y : ℝ) :
    (∀ K : ℕ, axisPartialSum x y (K + 2) =
        axisPartialSum x y (K + 1) + axisWeight x y (K + 2) * axisPartialSum x y K) ∧
      ∀ K : ℕ, axisWeight x y (K + 2) = axisWeight x y (K + 1) * axisWeight x y K :=
  ⟨axisPartialSum_succ_succ x y, axisWeight_succ_succ x y⟩

end D5.S3.Axis.AxisRecurrencePair
