import LeanInformationAudit.Census.Query
open Lean Meta Lean.Elab.Command LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape
namespace LeanInformationAudit.Tests.Census.StructuralTrivial
def arena : StructuralArena := ⟨Nat⟩
def law : StructuralPrimitiveLawArena arena where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law readouts := ∀ n, readouts.readout () n = 0
def readouts : StructuralPrimitiveRealization arena law.signature := ⟨fun _ _ => (0 : Nat)⟩
theorem nondegenerate : law.Nondegenerate := by
  exact ⟨readouts, ⟨fun _ _ => (1 : Nat)⟩, fun _ => rfl, fun h => Nat.one_ne_zero (h (0 : Nat))⟩
structural_theorem member in law realization readouts nondegeneracy nondegenerate := fun _ => rfl
def catalogValue : StructuralCatalog arena := ⟨Fin 1, inferInstance, inferInstance,
  fun _ => member.__structural_unit⟩
theorem registration : StructuralRegistrationEvidence ``member arena member.__structural_unit
    catalogValue (0 : Fin 1) (∀ _ : Nat, (0 : Nat) = 0) := ⟨rfl, rfl⟩
theorem triviality : StructuralCatalog.TrivialInCatalog catalogValue (0 : Fin 1) :=
  fun h => h.2 (fun _ _ _ _ _ _ => rfl)
def catalogSeal : StructuralCatalogSeal catalogValue := ⟨fun _ => .isFalse
  (fun h => h.2 (fun _ _ _ _ _ _ => rfl))⟩
/-- info: structural trivial member certified -/
#guard_msgs (info, error) in
run_cmd liftTermElabM do
  let env ← getEnv
  let key : StatementKey := ⟨``member, theoremStatementIdentity env ``member⟩
  let row ← CensusQuery.assess (← CensusQuery.indexScope env.header.mainModule) "fixture-head" key
  unless row.className == "trivial_in_catalog" do throwError "structural trivial classification"
  let json := dispositionRowJson ⟨key, row⟩
  let payload ← ofExcept <| json.getObjVal? "payload"
  let fields ← ofExcept <| payload.getObj?
  unless fields.size == 9 && ["root", "canonical_arena", "catalog", "index", "registration",
      "realization", "catalog_seal", "triviality_certificate", "context"].all fields.contains do
    throwError "structural wire fields"
  let context ← ofExcept <| (← ofExcept <| payload.getObjVal? "context").getObj?
  unless context.size == 1 && context.contains "kind" do throwError "structural wire counts"
  unless (parseRow json).toOption == some ⟨key, row⟩ do throwError "structural wire roundtrip"
  logInfo "structural trivial member certified"
end LeanInformationAudit.Tests.Census.StructuralTrivial
