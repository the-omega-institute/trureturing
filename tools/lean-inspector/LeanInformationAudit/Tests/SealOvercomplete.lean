import LeanInformationAudit.SealCommand

/-! T-005: the fst, snd, and combined coordinate kernels are overcomplete.
The seal reads no JSON: `SealCommand` prepares and kernel-checks declarations
before its optional output-only write, and never reads that artifact back. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealOvercomplete

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Bool × Bool)
  signature :=
    { Index := Fin 2
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def fstRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state.1
  anchor := Fin.elim0

def sndRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state.2
  anchor := Fin.elim0

private def identityReadout : Fin 2 → (Bool × Bool) → Bool :=
  ![Prod.fst, Prod.snd]

def idRealization : PrimitiveRealization arena.signature where
  readout := identityReadout
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
