/- GID: D5/S3/Axis/TraceMap/AxisWeightCompatibility
   generality: I
   mirror-B: D5/B/S3/Axis/TraceMap/AxisWeightCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two axis weights introduced in this repository denote the same function. -/

import D5.S1.Recurrence.TraceMap
import D5.S3.Axis.AxisTraceRecurrence

/- Library-search audit trail (2026-08-21):
   * The search key is the source atom and the containing directory, not a guessed Lean name.
     `theorem/6.35` carries a formalization receipt at
     `Meta/Digestion/formalizations/pzg-residual-033694bc….v1.json` naming
     `D5/S1/Recurrence/TraceMap.trace_map_recursion`; that receipt is what identifies the
     earlier weight. Searching by invented names is what produced the duplication this module
     reconciles (issue #2602).
   * `git grep -n "axisWeight" -- 'D5/**'` returns exactly two definitions: the S1 one landed
     2026-08-11, the S3 one 2026-08-19. No third definition exists.
   * `git grep -n "TraceMap.axisWeight" -- 'D5/**'` outside this file returns nothing, so no
     proof relating the two weights existed before this module.
   * `D5/S3/Axis/TraceMap/PartialSumBridge.lean` (2026-08-21) already relates the two *sums*.
     It is a different statement and is not restated here; see the note below. -/

namespace D5.S3.Axis.TraceMap.AxisWeightCompatibility

/-- The axis weight introduced on the S3 side and the one introduced eight days earlier on the
S1 side are the same function of the face pair and the index.

Both transcribe the same source formula `t_K = exp(−x·φ^(K+1) + y·ψ^(K+1))`; they differ only
in where the negation sits — `-(x * φ^(K+1))` against `-x * φ^(K+1)` — so the identity is
`neg_mul` under the exponential, discharged here by `ring` on the exponent.

**What this does not claim.** The two partial sums are not equal as written:
`TraceMap.tracePartial` weights bit `i` at index `i + 1`, while `AxisPartialSum.axisPartialSum`
runs over `Nat.zeckendorf`, whose indices start at `2`. Their exact relation is a separate
result, already proved in `D5/S3/Axis/TraceMap/PartialSumBridge.wordSum_eq_axisPartialSum`,
and it carries **two** shifts, not one: that theorem reindexes the weight by `j + 2` *and*
raises the depth by one. Because `tracePartial` uses the `i + 1` reindexing rather than
`i + 2`, this identity and that bridge still do not compose into a naked equality between
`tracePartial` and `axisPartialSum`, and none is asserted anywhere. -/
theorem axisWeight_eq (x y : ℝ) (K : ℕ) :
    D5.S3.Axis.AxisTraceRecurrence.axisWeight x y K
      = D5.S1.Recurrence.TraceMap.axisWeight x y K := by
  unfold D5.S3.Axis.AxisTraceRecurrence.axisWeight D5.S1.Recurrence.TraceMap.axisWeight
  congr 1
  ring

/-- The multiplicative Fibonacci law transported across the identification: the S1 weight
satisfies the recurrence proved on the S3 side, so the two recorded recurrences are one fact
about one object rather than two independent facts about two. -/
theorem axisWeight_succ_succ_transported (x y : ℝ) (K : ℕ) :
    D5.S1.Recurrence.TraceMap.axisWeight x y (K + 2)
      = D5.S1.Recurrence.TraceMap.axisWeight x y (K + 1)
        * D5.S1.Recurrence.TraceMap.axisWeight x y K := by
  rw [← axisWeight_eq x y (K + 2), ← axisWeight_eq x y (K + 1), ← axisWeight_eq x y K]
  exact D5.S3.Axis.AxisTraceRecurrence.axisWeight_succ_succ x y K

#print axioms axisWeight_eq

end D5.S3.Axis.TraceMap.AxisWeightCompatibility
