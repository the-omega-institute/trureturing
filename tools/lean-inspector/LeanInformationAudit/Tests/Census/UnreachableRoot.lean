import LeanInformationAudit.Tests.Census.UnreachableProofs
import LeanInformationAudit.Tests.Census.CommandRejection

open Lean LeanInformationAudit DispositionCensus
open Lean.Elab.Command
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.UnreachableRoot

theorem failedReadout : UnfaithfulPrimitiveObligation ``Evidence.structuralTheorem
    Evidence.structuralLawArena UnreachableProofs.identityReadouts
    (∀ n : Nat, n % 2 < 2) := by
  constructor
  intro bridge
  exact Nat.lt_irrefl 2 (bridge.mp Evidence.structuralTheorem 2)

def noRealization : UnreachableElaborationEvidence (∀ n : Nat, n % 2 < 2) where
  reason := .noFaithfulPrimitiveRealization
  candidateArena := some ``Evidence.infiniteArena
  explanation := "Identity readouts fail this candidate parity-law presentation."
  failedObligation := some ``failedReadout

def inventory : DispositionInventory := ⟨"fixture-head", #[
  ⟨⟨``Evidence.structuralTheorem, "structural-id"⟩,
    .unreachable ⟨.noFaithfulPrimitiveRealization, ``noRealization⟩⟩]⟩

/--
info: IE-C037 DispositionClassMismatch theorem=LeanInformationAudit.Tests.Census.Evidence.structuralTheorem class=unreachable invalid=registered_structural_realization
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedCensus `LeanInformationAudit.Tests.Census.Evidence ``inventory
    `correctRootCoverage inventory
    (classError ``Evidence.structuralTheorem "unreachable" "registered_structural_realization")

/--
info: IE-C044 DispositionCensusMismatch head=fixture-head component=root expected=import-closure-containing:LeanInformationAudit.Tests.Census.Evidence.structuralTheorem actual=LeanInformationAudit.Tests.SealSuccess
---
info: rejected=true output-absent=true certificate-absent=true
-/
#guard_msgs in
run_cmd do
  expectRejectedCensus `LeanInformationAudit.Tests.SealSuccess ``inventory
    `wrongRootCoverage inventory
    (censusError inventory.headSha "root"
      "import-closure-containing:LeanInformationAudit.Tests.Census.Evidence.structuralTheorem"
      "LeanInformationAudit.Tests.SealSuccess")

#print axioms failedReadout

end LeanInformationAudit.Tests.Census.UnreachableRoot
