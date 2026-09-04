import LeanInformationAudit.SealCommand

/-! T-013: the engine's own finite unique-capture characterization is
registered and sealed by the same leave-one-out rule as every other theorem. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealSystemTheorem

abbrev SystemStatement : Prop :=
  ∀ {candidateArena : Arena.{0}} (catalog : Catalog.{0, 0, 0} candidateArena)
      (index : catalog.Index) (_nondegenerate : candidateArena.Nondegenerate),
    catalog.LowersEscape index ↔ 0 < catalog.uniqueCaptureCount index

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
  Law := fun _ => SystemStatement

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

private def identityReadout : Fin 2 → (Bool × Bool) → Bool :=
  ![Prod.fst, Prod.snd]

def systemRealization : PrimitiveRealization arena.signature where
  readout := identityReadout
  anchor := Fin.elim0

theorem systemLegacyRealization :
    LegacyPrimitiveRealization arena SystemStatement systemRealization :=
  ⟨Iff.rfl⟩

theorem systemTheorem : SystemStatement := by
  intro candidateArena catalog index nondegenerate
  exact Catalog.lowersEscape_iff_uniqueCaptureCount_pos
    catalog index nondegenerate

register_information_theorem systemTheorem
  in arena
  primitives systemRealization.toPrimitiveBundle
  realization systemLegacyRealization

#seal_information_theory

#check systemTheorem.__lowers_escape

#print axioms systemTheorem.__lowers_escape

example :
    arena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 12 := by
  decide

end LeanInformationAudit.Tests.SealSystemTheorem
