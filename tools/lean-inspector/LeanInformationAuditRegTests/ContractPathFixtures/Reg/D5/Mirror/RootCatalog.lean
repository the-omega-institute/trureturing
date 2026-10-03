import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S0.Tower.GoldenGapZeckendorf

namespace LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.RootCatalog
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

noncomputable def sourceUnit := _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration

noncomputable def source0 : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add) DependentFamily.Arena DependentFamily.Arena
    (DependentFamily.Realization _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature) Unit Unit Unit Unit Unit := {
  unitName := `LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.RootCatalog.sourceUnit
  realizationName := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration
  realizationSource := none
  generated := false
  arena := ⟨_root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩
  objectArena := ⟨_root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩
  catalog := `Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
  localNames := false
  realization := .source _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
    ⟨_root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration⟩
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature
    (fun _ (Q : Nat) (j : Fin (Nat.fib (Q + 2))) =>
      _root_.D5.S0.Conventions.wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e))
  variation := none
  sensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Tower.GoldenGapZeckendorf
    definition := none, coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

end LeanInformationAuditRegTests.ContractPathFixtures.Reg.D5.Mirror.RootCatalog
