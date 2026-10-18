/- GID: D5/S0/Certificates/FiniteSymmetryBoundReplay
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteSymmetryBoundReplay
   mirror-E: none(waiver:finite-symbolic-certificate-replay)
   anchors: []
   utility: none
   digest: Complete and partial events carry exact compatibility for the checked local row DAGs. -/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Sort
import Mathlib.Order.PiLex
import Mathlib.Tactic

/-! The local row and cache proofs use complete events, partial assignments
and exact compatibility on every assigned coordinate. These definitions
assert neither global replay acceptance nor a positive score margin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteSymmetryBoundReplay

variable {Coord Value : Type*}

abbrev Event (Coord Value : Type*) := Coord → Value
abbrev Partial (Coord Value : Type*) := Coord → Option Value

/-- Every assigned coordinate must agree with the actual event. -/
def Compatible (p : Partial Coord Value) (e : Event Coord Value) : Prop :=
  ∀ i a, p i = some a → e i = a

/-- A complete partial event supplies every observed coordinate. -/
def completed (e : Event Coord Value) : Partial Coord Value := fun i => some (e i)

end D5.S0.Certificates.FiniteSymmetryBoundReplay
