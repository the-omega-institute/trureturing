import LeanInformationAudit.SealCommand

/-! T-017 empty-state companion: `Fin 0` is constructible as an arena, but
the seal rejects it as degenerate before publishing any generated declaration. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealEmptyState

def arena : PrimitiveLawArena.{0, 0, 0} where
  toArena := Arena.ofFintype (Fin 0)
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => PUnit
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

private def emptyReadout : Fin 1 -> Fin 0 -> PUnit :=
  fun _ state => Fin.elim0 state

def emptyRealization : PrimitiveRealization arena.signature where
  readout := emptyReadout
  anchor := Fin.elim0

information_theorem emptyTheorem
  in arena
  primitives emptyRealization
  : arena.Law emptyRealization := by trivial

/-- error: IE-C004 DegenerateArena:
LeanInformationAudit.Tests.SealEmptyState.arena -/
#guard_msgs (error) in
#seal_information_theory

/-- error: Invalid field `__information_catalog`: The environment does not contain
`D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.__information_catalog`, so it is
not possible to project the field `__information_catalog` from an expression
  arena
of type `PrimitiveLawArena` -/
#guard_msgs (error) in
#check @LeanInformationAudit.Tests.SealEmptyState.arena.__information_catalog

/-- error: Invalid field `__lowers_escape`: The environment does not contain
`True.__lowers_escape`, so it is not possible to project the field `__lowers_escape` from an
expression
  emptyTheorem
of type `True` -/
#guard_msgs (error) in
#check @LeanInformationAudit.Tests.SealEmptyState.emptyTheorem.__lowers_escape

end LeanInformationAudit.Tests.SealEmptyState
