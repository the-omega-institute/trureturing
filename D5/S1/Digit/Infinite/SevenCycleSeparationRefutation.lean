/- GID: D5/S1/Digit/Infinite/SevenCycleSeparationRefutation
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCycleSeparationRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unconditional finite-future separation assertion for actual singleton rivals. -/

import D5.S1.Digit.Infinite.SevenCycleCollisionData

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCycleSeparationRefutation

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open private source phaseGuard firstLabel rivalLabel phaseColor lowerEntry upperEntry referenceTail referenceEnd reduction budget firstEntry rivalEntry feedingEntry phase from D5.S1.Digit.Infinite.SevenCycleCollisionData

/-- The finite future test uses the same rival address, all original guards and all branches. -/
noncomputable def horizon (b : ℝ) (eta : LegalDigits) (r : ℕ) (s : Bool) : ℕ → Set ℝ
  | 0 => stateInterval s
  | n + 1 => {x | (∃ c : Fin 6,
      kappa (bitShift eta (3 * r)) ∈ observation b c ∧ x ∈ observation b c) ∧
      ∃ l : Label, ∃ s' : Bool, lawful s l s' ∧
        ∃ y ∈ horizon b eta (r + 1) s' n, x = branch l y}

/-- Two different first labels can use different first colors against the same rival. -/
noncomputable def entrySet (b : ℝ) (l m : Label) (c d : Fin 6) (s : Bool) : Set ℝ :=
  stateInterval s ∩ branch l ⁻¹' observation b c ∩ branch m ⁻¹' observation b d

/-- No conditioning on a shared first-color history is imposed. -/
noncomputable def separates (b : ℝ) (eta : LegalDigits) : Prop :=
  ∃ n : ℕ, ∀ (s : Bool) (l m : Label) (c d : Fin 6),
    lawful false l s → lawful false m s → l ≠ m →
    kappa eta ∈ observation b c → kappa eta ∈ observation b d →
    entrySet b l m c d s ∩ horizon b eta 1 s n = ∅

/-- Primitive period is measured in actual three-bit windows. -/
def primitiveWindowPeriod (eta : LegalDigits) (p : ℕ) : Prop :=
  0 < p ∧ Function.Periodic (window eta) p ∧
    ∀ k : ℕ, 0 < k → Function.Periodic (window eta) k → p ≤ k

/-- The rival's actual periodic orbit consists of original singleton vertices and edges. -/
def singletonRival (q : ℕ) (R : ℝ) (eta : LegalDigits) : Prop :=
  ∃ p : ℕ, Odd p ∧ primitiveWindowPeriod eta p ∧
    ∃ v : ℕ → Vertex q R,
      (∀ j, (v j).val.1 = actualGuard false eta j ∧
        piece (v j) = {kappa (bitShift eta (3 * j))}) ∧
      (∀ j, edge (v j) (window eta j) (v (j + 1))) ∧
      (∀ j, v (j + p) = v j)

/-- Every actual odd primitive singleton rival is claimed to admit unconditional finite separation. -/
def claim : Prop :=
  ∀ (b : ℝ) (q : ℕ) (R : ℝ), 0 < b → b < lambda → endpointParameters b q R →
    ∀ eta : LegalDigits, singletonRival q R eta → separates b eta

end D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
