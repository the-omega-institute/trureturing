import Reg.Support.DependentFamily

namespace Reg.Support.SingleDependentReadout
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- A single observation with parameter-dependent states and outputs. -/
abbrev signature (P : Type) (X Y : P → Type) : Signature where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := Y
  Anchor := Empty
  finiteAnchor := inferInstance

/-- With one role and no anchors, a rejected family witnesses all sensitivity obligations. -/
theorem sensitivity {P : Type} {X Y : P → Type}
    (law : Realization (signature P X Y) → Prop)
    (actual bad : Realization (signature P X Y)) (hbad : ¬ law bad) :
    Sensitivity ⟨signature P X Y, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

end Reg.Support.SingleDependentReadout
