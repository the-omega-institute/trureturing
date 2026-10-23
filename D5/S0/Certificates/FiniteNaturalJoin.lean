/- GID: D5/S0/Certificates/FiniteNaturalJoin
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteNaturalJoin
   mirror-E: none(waiver:finite-relation-join)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportConflict.result; instance=D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportConflict.result
   digest: Natural joins preserve every compatible total event, so an empty checked join refutes simultaneous support membership. -/

import Mathlib.Data.List.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteNaturalJoin

variable {Coord Value : Type*}

/-- A finite row lists its assigned coordinates; repeated entries are allowed. -/
abbrev Row (Coord Value : Type*) := List (Coord × Value)

/-- All entries of a row agree with the same actual total event. -/
def RowCompatible (p : Row Coord Value) (e : Coord → Value) : Prop :=
  ∀ cv ∈ p, e cv.1 = cv.2

/-- The event has a compatible row in the relation. -/
def Covers (rows : List (Row Coord Value)) (e : Coord → Value) : Prop :=
  ∃ p ∈ rows, RowCompatible p e

variable [DecidableEq Coord] [DecidableEq Value]

/-- Exact agreement on overlapping coordinates, with no distinguished coordinate. -/
def agree (p q : Row Coord Value) : Bool :=
  p.all fun a => q.all fun b => decide (a.1 ≠ b.1 ∨ a.2 = b.2)

/-- The finite natural join retains precisely the compatible input pairs. -/
def join (left right : List (Row Coord Value)) : List (Row Coord Value) :=
  left.flatMap fun p => (right.filter (agree p)).map fun q => p ++ q

/-- A shared total event survives the computed natural join. This theorem does
not assume join acceptance, a global support witness, or a score margin. -/
theorem join_covers (left right : List (Row Coord Value))
    (e : Coord → Value) (hl : Covers left e) (hr : Covers right e) :
    Covers (join left right) e := by
  rcases hl with ⟨p, hp, heP⟩
  rcases hr with ⟨q, hq, heQ⟩
  have ha : agree p q = true := by
    simp only [agree, List.all_eq_true, decide_eq_true_eq]
    intro a hpa b hqb
    by_cases h : a.1 = b.1
    · exact Or.inr ((heP a hpa).symm.trans ((congrArg e h).trans (heQ b hqb)))
    · exact Or.inl h
  refine ⟨p ++ q, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨p, hp, List.mem_map.mpr ?_⟩
    exact ⟨q, List.mem_filter.mpr ⟨hq, ha⟩, rfl⟩
  · intro cv hcv
    rcases List.mem_append.mp hcv with hcv | hcv
    · exact heP cv hcv
    · exact heQ cv hcv

end D5.S0.Certificates.FiniteNaturalJoin
