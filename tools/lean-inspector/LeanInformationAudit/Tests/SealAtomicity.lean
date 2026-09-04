import LeanInformationAudit.SealCommand

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealAtomicity

private def signature : PrimitiveSignature Bool where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def goodArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := signature
  Law := fun _ => True

def zeroArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := signature
  Law := fun _ => True

local instance : DecidableEq goodArena.State := goodArena.toArena.stateDecidableEq
local instance : DecidableEq zeroArena.State := zeroArena.toArena.stateDecidableEq

def goodRealization : PrimitiveRealization goodArena.signature where
  readout := fun _ state => !state
  anchor := Fin.elim0

def zeroRealization : PrimitiveRealization zeroArena.signature where
  readout := fun _ _ => false
  anchor := Fin.elim0

information_theorem goodTheorem
  in goodArena
  primitives goodRealization
  : goodArena.Law goodRealization := by trivial

information_theorem zeroTheorem
  in zeroArena
  primitives zeroRealization
  : zeroArena.Law zeroRealization := by trivial

/-- error: IE-C007 ZeroUniqueCapture: theorem
LeanInformationAudit.Tests.SealAtomicity.zeroTheorem arena
LeanInformationAudit.Tests.SealAtomicity.zeroArena full 2 without 2 -/
#guard_msgs (error) in
#seal_information_theory

/-- error: Invalid field `__information_catalog`: The environment does not contain
`D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.__information_catalog`, so it is
not possible to project the field `__information_catalog` from an expression
  goodArena
of type `PrimitiveLawArena` -/
#guard_msgs (error) in
#check @LeanInformationAudit.Tests.SealAtomicity.goodArena.__information_catalog

/-- error: Invalid field `__lowers_escape`: The environment does not contain
`True.__lowers_escape`, so it is not possible to project the field `__lowers_escape` from an
expression
  goodTheorem
of type `True` -/
#guard_msgs (error) in
#check @LeanInformationAudit.Tests.SealAtomicity.goodTheorem.__lowers_escape

/-- error: Invalid field `__escape_enriched`: The environment does not contain
`True.__escape_enriched`, so it is not possible to project the field `__escape_enriched` from an
expression
  goodTheorem
of type `True` -/
#guard_msgs (error) in
#check @LeanInformationAudit.Tests.SealAtomicity.goodTheorem.__escape_enriched

/-- error: Invalid field `__catalog_irredundant`: The environment does not contain
`D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.__catalog_irredundant`, so it is not
possible to project the field `__catalog_irredundant` from an expression
  goodArena
of type `PrimitiveLawArena` -/
#guard_msgs (error) in
#check @LeanInformationAudit.Tests.SealAtomicity.goodArena.__catalog_irredundant

end LeanInformationAudit.Tests.SealAtomicity
