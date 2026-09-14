/- GID: D5/S0/Certificates/BoxCover/BoxCoverExamples
   generality: I
   mirror-B: D5/B/S0/Certificates/BoxCover/BoxCoverExamples
   mirror-E: none(waiver:kernel-checked-rational-forest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/BoxCover/BoxCoverExamples.escapedSublevelClaim; result=D5/S0/Certificates/BoxCover/BoxCoverExamples.no_escaped_sublevel; claim=D5/S0/Certificates/BoxCover/BoxCoverExamples.escapedSublevelClaim
   digest: A five-node rational forest confines the squared-residual sublevel in [-2,2] to [-1,1]. -/

import D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

/-!
The concrete question is whether a point of [-2,2] with |x²| ≤ 1/4 can
escape [-1,1]. Two excluded leaves bound x² in [1,4], a covered leaf
retains [-1,1], and two postordered splits cover the entire root interval.
The sublevel is nonempty (it contains zero); no finite sampling is assumed.

Library search: the BoxCover modules supply the general enclosure and cover
theorems. This instance applies their existing soundness proof directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.BoxCover.BoxCoverExamples

open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

/-- Postordered boxes: two outer leaves, the center, the right subtree, and root. -/
def squareBoxes (i : Fin 5) : Fin 1 → ℚ × ℚ := fun _ ↦
  match i.val with
  | 0 => (-2, -1)
  | 1 => (1, 2)
  | 2 => (-1, 1)
  | 3 => (-1, 2)
  | _ => (-2, 2)

/-- The single target interval is [-1,1]. -/
def squareTargets : Fin 1 → Fin 1 → ℚ × ℚ := fun _ _ ↦ (-1, 1)

/-- The authoritative residual is the square of the sole real coordinate. -/
def squareResidual : Fin 1 → Expr 1 := fun _ ↦ .square 0 4 (.input 0 (-2) 2)

/-- Exclude both outer leaves, cover the center, then split at 1 and at -1. -/
def squareForest (i : Fin 5) : Step 1 1 1 5 :=
  match i.val with
  | 0 => .excluded 0 (.square 1 4 (.input 0 (-2) (-1)))
  | 1 => .excluded 0 (.square 1 4 (.input 0 1 2))
  | 2 => .covered 0
  | 3 => .split 0 1 2 1
  | _ => .split 0 (-1) 0 3

/-- All five nodes pass the rational checker at tolerance 1/4. -/
theorem square_forest_accepted :
    checkForest squareBoxes squareTargets squareResidual (1 / 4) squareForest = true := by
  decide +kernel

/-- Every real point in the root with squared residual at most 1/4 is in the target. -/
theorem square_sublevel_covered :
    {x : ℝ | x ∈ Set.Icc (-2) 2 ∧ |x ^ 2| ≤ 1 / 4} ⊆ Set.Icc (-1) 1 := by
  intro x hx
  obtain ⟨k, hk⟩ := checked_forest_covers_sublevel
    squareBoxes squareTargets squareResidual (1 / 4) squareForest
    square_forest_accepted 4 (fun _ ↦ x)
    (by intro j; simpa [squareBoxes] using hx.1)
    (by intro a; simpa [squareResidual, value] using hx.2)
  simpa [squareTargets] using hk 0

/-- The claim that a small squared residual in the root can escape the target. -/
def escapedSublevelClaim : Prop :=
  ∃ x : ℝ, x ∈ Set.Icc (-2) 2 ∧ |x ^ 2| ≤ 1 / 4 ∧ x ∉ Set.Icc (-1) 1

/-- The accepted forest rules out every proposed escaping point. -/
theorem no_escaped_sublevel : ¬ escapedSublevelClaim := by
  rintro ⟨x, hx, hr, hout⟩
  exact hout (square_sublevel_covered ⟨hx, hr⟩)

#print axioms square_forest_accepted
#print axioms square_sublevel_covered
#print axioms no_escaped_sublevel

end D5.S0.Certificates.BoxCover.BoxCoverExamples
