/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFourCTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFourCTree
   mirror-E: none(waiver:c-disjoint-path-enumeration)
   anchors: [mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Recursive disjoint T/S/U/V paths retain the distinct C branching edges. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFourCTree

inductive Label
  | T
  | S
  | U
  | V

def Paths : ℕ → Label → Type
  | 0, _ => Unit
  | depth + 1, .T => Paths depth .T ⊕ Paths depth .S
  | depth + 1, .S => (Paths depth .T ⊕ Paths depth .S) ⊕ Paths depth .U
  | depth + 1, .U => (Paths depth .V ⊕ Paths depth .U) ⊕ Paths depth .U
  | depth + 1, .V => Paths depth .V

def nextLabel : (label : Label) → Paths 1 label → Label
  | .T, .inl _ => .T
  | .T, .inr _ => .S
  | .S, .inl (.inl _) => .T
  | .S, .inl (.inr _) => .S
  | .S, .inr _ => .U
  | .U, .inl (.inl _) => .V
  | .U, .inl (.inr _) => .U
  | .U, .inr _ => .U
  | .V, _ => .V


end D5.S3.Combinatorics.Fishburn.FishburnTenFourCTree
