import Reg.Support.DependentFamily

/-! Universe-polymorphic support for a single dependent observation with no anchors. -/

namespace Reg.Support.UniverseSingleReadout
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe t s o

/-- A single observation whose parameters, states and outputs may live in different universes. -/
abbrev signature (P : Type t) (S : P → Type s) (O : P → Type o) :
    Signature.{t,s,0,o,0} where
  Params := P
  State := S
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := O
  Anchor := Empty
  finiteAnchor := inferInstance

/-- A rejected readout family supplies every sensitivity obligation for the single role. -/
theorem sensitivity {P : Type t} {S : P → Type s} {O : P → Type o}
    (law : Realization (signature P S O) → Prop)
    (actual bad : Realization (signature P S O)) (hbad : ¬ law bad) :
    Sensitivity ⟨signature P S O, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

end Reg.Support.UniverseSingleReadout
