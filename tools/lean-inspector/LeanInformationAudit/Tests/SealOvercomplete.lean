import LeanInformationAudit.SealCommand

/-! T-005: the fst, snd, and product identity kernels are overcomplete. The
seal reports the first sorted zero-marginal member; three count assertions
cover every member. -/

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.CIRPT

namespace LeanInformationAudit.Tests.SealOvercomplete

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Bool × Bool)
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool × Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def fstRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => (state.1, false)
  anchor := Fin.elim0

def sndRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => (state.2, false)
  anchor := Fin.elim0

def idRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

information_theorem fstTheorem
  in arena
  primitives fstRealization
  : arena.Law fstRealization := by trivial

information_theorem sndTheorem
  in arena
  primitives sndRealization
  : arena.Law sndRealization := by trivial

information_theorem idTheorem
  in arena
  primitives idRealization
  : arena.Law idRealization := by trivial

example : ∀ x y : arena.State,
    fstRealization.toPrimitiveBundle.agrees x y ↔
      (cutKernel Prod.fst).relation x y := by
  intro x y
  rw [PrimitiveRealization.toPrimitiveBundle_agrees_iff]
  constructor
  · rintro ⟨agreement, _⟩
    change x.1 = y.1
    have coordinateAgreement := agreement (0 : Fin 1)
    change (x.1, false) = (y.1, false) at coordinateAgreement
    exact (Prod.ext_iff.mp coordinateAgreement).1
  · intro agreement
    constructor
    · intro _
      change (x.1, false) = (y.1, false)
      change x.1 = y.1 at agreement
      exact Prod.ext agreement rfl
    · intro impossible
      exact Fin.elim0 impossible

example : ∀ x y : arena.State,
    sndRealization.toPrimitiveBundle.agrees x y ↔
      (cutKernel Prod.snd).relation x y := by
  intro x y
  rw [PrimitiveRealization.toPrimitiveBundle_agrees_iff]
  constructor
  · rintro ⟨agreement, _⟩
    change x.2 = y.2
    have coordinateAgreement := agreement (0 : Fin 1)
    change (x.2, false) = (y.2, false) at coordinateAgreement
    exact (Prod.ext_iff.mp coordinateAgreement).1
  · intro agreement
    constructor
    · intro _
      change (x.2, false) = (y.2, false)
      change x.2 = y.2 at agreement
      exact Prod.ext agreement rfl
    · intro impossible
      exact Fin.elim0 impossible

example : ∀ x y : arena.State,
    idRealization.toPrimitiveBundle.agrees x y ↔
      (cutKernel (id : Bool × Bool -> Bool × Bool)).relation x y := by
  intro x y
  rw [PrimitiveRealization.toPrimitiveBundle_agrees_iff]
  constructor
  · rintro ⟨agreement, _⟩
    change x = y
    have identityAgreement := agreement (0 : Fin 1)
    change x = y at identityAgreement
    exact identityAgreement
  · intro agreement
    constructor
    · intro _
      change x = y
      change x = y at agreement
      exact agreement
    · intro impossible
      exact Fin.elim0 impossible

private def fixtureCatalog : Catalog arena.toArena :=
  Catalog.ofVector ![
    fstTheorem.__information_unit,
    sndTheorem.__information_unit,
    idTheorem.__information_unit]

example : fixtureCatalog.uniqueCaptureCount (0 : Fin 3) = 0 := by decide
example : fixtureCatalog.uniqueCaptureCount (1 : Fin 3) = 0 := by decide
example : fixtureCatalog.uniqueCaptureCount (2 : Fin 3) = 0 := by decide

/-- error: IE-C007 ZeroUniqueCapture: theorem
LeanInformationAudit.Tests.SealOvercomplete.fstTheorem arena
LeanInformationAudit.Tests.SealOvercomplete.arena full 0 without 0 -/
#guard_msgs (error) in
#seal_information_theory

/-- error: Invalid field `__lowers_escape`: The environment does not contain
`True.__lowers_escape`, so it is not possible to project the field `__lowers_escape` from an
expression
  idTheorem
of type `True` -/
#guard_msgs (error) in
#check @LeanInformationAudit.Tests.SealOvercomplete.idTheorem.__lowers_escape

end LeanInformationAudit.Tests.SealOvercomplete
