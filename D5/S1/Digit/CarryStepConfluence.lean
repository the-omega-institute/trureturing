/- GID: D5/S1/Digit/CarryStepConfluence
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   digest: Arbitrary raw Zeckendorf carry paths preserve value and are globally confluent. -/

import D5.S1.Digit.Normalize

/-!
# Confluence of raw Zeckendorf carries

This module upgrades the deterministic normalizer contract to arbitrary finite
`CarryStep` paths. It proves pathwise value and normalization invariance,
identifies every reachable canonical endpoint with `normalize`, and establishes
global confluence for the raw relation used by the paper's central theorem.

The repository and pinned Mathlib were searched first. No existing declaration
specialized confluence or path invariance to `CarryStep`; the proof reuses the
frozen one-step value law, normalizer reachability, and canonical uniqueness,
while Mathlib supplies `Relation.ReflTransGen` and `Relation.Join`.
-/

namespace D5.S1.Digit

/-- Every finite raw carry path preserves the represented natural number. -/
theorem rawValue_reflTransGen {r s : RawDigits}
    (h : Relation.ReflTransGen CarryStep r s) :
    rawValue r = rawValue s := by
  induction h with
  | refl => rfl
  | tail h step ih => exact ih.trans (rawValue_carryStep step)

/-- The deterministic normal form is invariant along every finite raw carry path. -/
theorem normalize_eq_of_reflTransGen {r s : RawDigits}
    (h : Relation.ReflTransGen CarryStep r s) :
    normalize r = normalize s := by
  apply canonicalRaw_unique (normalize_canonical r) (normalize_canonical s)
  rw [rawValue_normalize, rawValue_normalize]
  exact rawValue_reflTransGen h

/-- Every canonical endpoint reachable by raw carries is exactly the fixed normalizer output. -/
theorem reachable_canonical_eq_normalize {r s : RawDigits}
    (hrs : Relation.ReflTransGen CarryStep r s)
    (hs : CanonicalRaw s) :
    s = normalize r := by
  calc
    s = normalize s := (normalize_eq_of_canonical hs).symm
    _ = normalize r := (normalize_eq_of_reflTransGen hrs).symm

/-- Arbitrary finite `CarryStep` reductions from a common raw source are joinable. -/
theorem carryStep_confluent :
    ∀ ⦃r s t : RawDigits⦄,
      Relation.ReflTransGen CarryStep r s →
      Relation.ReflTransGen CarryStep r t →
      Relation.Join (Relation.ReflTransGen CarryStep) s t := by
  intro r s t hrs hrt
  refine ⟨normalize r, ?_, ?_⟩
  · rw [normalize_eq_of_reflTransGen hrs]
    exact normalize_reachable s
  · rw [normalize_eq_of_reflTransGen hrt]
    exact normalize_reachable t

end D5.S1.Digit
