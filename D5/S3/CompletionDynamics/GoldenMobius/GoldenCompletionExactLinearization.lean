/- GID: D5/S3/CompletionDynamics/GoldenMobius/GoldenCompletionExactLinearization
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/GoldenMobius/GoldenCompletionExactLinearization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden cross-ratio linearization extends exactly through every defined finite iterate. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenCrossRatioLinearization

/-!
The canonical GoldenMobius family already owns the Mobius map, its cross-ratio
coordinate, the projective multiplier, and the one-step linearization. The
existing iterate theorem uses the positive chart. Here the orbit-domain premise
retains the full real affine chart and records exactly when every one-step
application used by a finite iterate is defined geometrically.

Repository body-shape searches for `1 + 1 / x`, the golden cross-ratio quotient,
and iterated cross-ratio linearization found those canonical owners and no
whole-statement conjunction. Pinned Mathlib searches found generic iteration
and Chebyshev infrastructure but no golden Mobius linearization theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.GoldenMobius.GoldenCompletionExactLinearization

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
open D5.S3.CompletionDynamics.GoldenMobius.GoldenCrossRatioLinearization

/-- The golden cross-ratio obeys the exact one-step multiplier law, and every
finite iterate obeys its corresponding power law whenever all earlier points
remain in the affine-chart domain. -/
theorem golden_completion_exact_linearization :
    (forall x : Real, x ≠ 0 -> x ≠ Real.goldenConj ->
      goldenCrossRatio (goldenMobius x) =
        goldenProjectiveMultiplier * goldenCrossRatio x) ∧
    (forall (n : Nat) (x : Real),
      (forall k : Nat, k < n ->
        (goldenMobius^[k]) x ≠ 0 ∧
          (goldenMobius^[k]) x ≠ Real.goldenConj) ->
      goldenCrossRatio ((goldenMobius^[n]) x) =
        goldenProjectiveMultiplier ^ n * goldenCrossRatio x) := by
  constructor
  · intro x hx hConj
    exact golden_cross_ratio_linearization hx hConj
  · intro n
    induction n with
    | zero =>
        intro x _
        simp
    | succ n ih =>
        intro x hDomain
        rw [Function.iterate_succ_apply']
        have hAtN := hDomain n (Nat.lt_succ_self n)
        rw [golden_cross_ratio_linearization hAtN.1 hAtN.2]
        rw [ih x (fun k hk => hDomain k (hk.trans (Nat.lt_succ_self n)))]
        rw [pow_succ]
        ring

#print axioms golden_completion_exact_linearization

end D5.S3.CompletionDynamics.GoldenMobius.GoldenCompletionExactLinearization
