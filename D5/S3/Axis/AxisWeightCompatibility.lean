/- GID: D5/S3/Axis/AxisWeightCompatibility
   generality: I
   mirror-B: D5/B/S3/Axis/AxisWeightCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two axis weights introduced in this repository denote the same function. -/

import D5.S1.Recurrence.TraceMap
import D5.S3.Axis.AxisTraceRecurrence

/- Library-search audit trail (2026-08-21):
   * The search key here is the source atom, not a guessed Lean name. `theorem/6.35` carries a
     formalization receipt at `Meta/Digestion/formalizations/pzg-residual-033694bc….v1.json`
     naming `D5/S1/Recurrence/TraceMap.trace_map_recursion`; that receipt is what identifies the
     earlier weight. Searching by invented names is what produced the duplicate this module
     reconciles (issue #2602).
   * `git grep -n "axisWeight" -- 'D5/**'` returns both definitions: the S1 one landed
     2026-08-11, the S3 one 2026-08-19. No third definition exists.
   * The identity itself needs no library lemma beyond `neg_mul`, which `ring` applies. -/

namespace D5.S3.Axis.AxisWeightCompatibility

/-- The axis weight introduced on the S3 side and the one introduced eight days earlier on the
S1 side are the same function of the face pair and the index.

Both transcribe the same source formula `t_K = exp(−x·φ^(K+1) + y·ψ^(K+1))`; they differ only
in where the negation sits — `-(x * φ^(K+1))` against `-x * φ^(K+1)` — so the identity is
`neg_mul` under the exponential, discharged here by `ring` on the exponent.

**What this does not claim.** The two partial sums built on these weights are *not* equal.
`TraceMap.tracePartial` weights bit `i` by the index `i + 1`, so its words carry the indices
`1, …, K`; `AxisPartialSum.axisPartialSum` runs over `Nat.zeckendorf`, whose indices start at
`2`. The two sums range over the same combinatorial family under a shift of the index base, and
the source text pins no smallest index, so both readings are faithful — but they are different
Lean objects, and no equality between them is asserted anywhere in this repository. -/
theorem axisWeight_eq (x y : ℝ) (K : ℕ) :
    D5.S3.Axis.AxisTraceRecurrence.axisWeight x y K
      = D5.S1.Recurrence.TraceMap.axisWeight x y K := by
  unfold D5.S3.Axis.AxisTraceRecurrence.axisWeight D5.S1.Recurrence.TraceMap.axisWeight
  congr 1
  ring

/-- The multiplicative Fibonacci law transported across the identification: the S1 weight
satisfies the S3 recurrence and conversely, so neither module's recurrence is a second,
independent fact about a second, independent object. -/
theorem axisWeight_succ_succ_transported (x y : ℝ) (K : ℕ) :
    D5.S1.Recurrence.TraceMap.axisWeight x y (K + 2)
      = D5.S1.Recurrence.TraceMap.axisWeight x y (K + 1)
        * D5.S1.Recurrence.TraceMap.axisWeight x y K := by
  rw [← axisWeight_eq x y (K + 2), ← axisWeight_eq x y (K + 1), ← axisWeight_eq x y K]
  exact D5.S3.Axis.AxisTraceRecurrence.axisWeight_succ_succ x y K

#print axioms axisWeight_eq

end D5.S3.Axis.AxisWeightCompatibility
