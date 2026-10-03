import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S0.Tower.GoldenGapZeckendorf

namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.SealedCatalog
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

noncomputable def source0 : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add) DependentFamily.Arena DependentFamily.Arena
    (DependentFamily.Realization _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature) Unit Unit Unit Unit Unit := {
  targetName := `D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add
  unitName := `ContractTests.source0.unit
  realizationName := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration
  realizationSource := none
  generated := false
  arena := ⟨`Reg.D5.S0.Tower.GoldenGapZeckendorf.arena, _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩
  objectArena := ⟨`Reg.D5.S0.Tower.GoldenGapZeckendorf.arena, _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩
  catalog := `Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
  localNames := false
  realization := .source _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
    ⟨`Reg.D5.S0.Tower.GoldenGapZeckendorf.registration, _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration⟩
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature
    _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration.actual.readout _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration.actual.anchor)
  variation := none
  sensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Tower.GoldenGapZeckendorf
    definition := none, coordinates := #[], readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

end LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.SealedCatalog
