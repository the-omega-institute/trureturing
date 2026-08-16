/- GID: D5/S1/Deficit/Carry/GoldenCarryDeficitBridge
   generality: I
   mirror-B: D5/B/S1/Deficit/Carry/GoldenCarryDeficitBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Frozen carry and deficit theorems imply a shared hidden integer account. -/

import D5.S1.Deficit.GoldenCarryLedger
import D5.S1.Deficit.DeficitInteger

namespace D5.S1.Deficit.Carry.GoldenCarryDeficitBridge

open D5.S0.Conventions
open D5.S1.Digit
open D5.S1.Deficit
open D5.S1.Deficit.GoldenCarryLedger
open Real

/-- The two frozen sides of the golden carry ledger form one addressable certificate:
internal carries preserve both golden faces, while normalization leaves the same signed
integer deficit on those faces, so their difference decoder cannot observe it. -/
theorem golden_carry_deficit_bridge (k v₁ v₂ : ℕ) :
    ((goldenRatio ^ (k + 1) + goldenRatio ^ (k + 2) = goldenRatio ^ (k + 3) ∧
        2 * goldenRatio ^ (k + 2) = goldenRatio ^ (k + 3) + goldenRatio ^ k) ∧
      (goldenConj ^ (k + 1) + goldenConj ^ (k + 2) = goldenConj ^ (k + 3) ∧
        2 * goldenConj ^ (k + 2) = goldenConj ^ (k + 3) + goldenConj ^ k)) ∧
    (deficit v₁ v₂ = deficitContraction v₁ v₂ ∧
      (∃ z : ℤ, deficit v₁ v₂ = (z : ℝ)) ∧
      deficit v₁ v₂ =
        (carrySignedCount (toRaw (Z v₁) + toRaw (Z v₂)) : ℝ)) ∧
    (deficit v₁ v₂ - deficitContraction v₁ v₂) / Real.sqrt 5 = 0 := by
  have hcarry := carry_rewrite_face_invariant k
  have hdeficit := deficit_integer v₁ v₂
  refine ⟨hcarry, hdeficit, ?_⟩
  rw [hdeficit.1, sub_self, zero_div]

end D5.S1.Deficit.Carry.GoldenCarryDeficitBridge
