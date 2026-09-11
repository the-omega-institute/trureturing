import LeanInformationAudit.Census.Query

open Lean Meta Lean.Elab.Command LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Census.StructuralPositiveMissingPeer

abbrev arena : StructuralArena := ⟨Nat⟩
def law : StructuralPrimitiveLawArena arena where
  signature := ⟨Unit, inferInstance, fun _ => Nat⟩
  Law readouts := ∀ n, readouts.readout () n < 2
def readouts : StructuralPrimitiveRealization arena law.signature := ⟨fun _ n => n % 2⟩
theorem nondegenerate : law.Nondegenerate := by
  exact ⟨readouts, ⟨fun _ _ => (2 : Nat)⟩, fun n => Nat.mod_lt n (by decide),
    fun h => (Nat.lt_irrefl 2) (h 0)⟩

structural_theorem member in law realization readouts nondegeneracy nondegenerate :=
  fun n => Nat.mod_lt n (by decide)

-- Stage the old singleton evidence, then discard that snapshot for the complete reseal.
set_option hygiene false in
run_cmd do
  let original ← getEnv
  try
    elabCommand (← `(command| def oldCatalog : StructuralCatalog arena :=
      ⟨Unit, inferInstance, inferInstance, fun _ => member.__structural_unit⟩))
    elabCommand (← `(command| theorem oldRegistration : StructuralRegistrationEvidence
        ``member arena member.__structural_unit oldCatalog () (∀ n : Nat, n % 2 < 2) := ⟨rfl, rfl⟩))
    elabCommand (← `(command| def oldWitness : StructuralStrictnessCertificate oldCatalog () where
      inclusion := by intro _ _ _ candidate ne; exact (ne rfl).elim
      left := 0
      right := 1
      without_agrees := by intro candidate ne; exact (ne rfl).elim
      full_separates := by
        intro full
        exact Nat.zero_ne_one (full () (Set.mem_univ ()) ())))
    elabCommand (← `(command| theorem oldStrictness : oldCatalog.StructurallyLowersEscape () :=
      oldCatalog.structurallyLowersEscape_of_certificate () oldWitness))
    liftTermElabM do
      let env ← getEnv
      let key : StatementKey := ⟨``member, theoremStatementIdentity env ``member⟩
      let index ← CensusQuery.indexScope env.header.mainModule
      let row ← CensusQuery.assess index "fixture-head" key
      unless row.className == "structural_occurrence" do
        throwError "StructuralPositiveMissingPeer: complete singleton is not positive"
    elabCommand (← `(command| structural_theorem peer in law realization readouts
      nondegeneracy nondegenerate := fun n => Nat.mod_lt n (by decide)))
    liftTermElabM do
      let env ← getEnv
      let key : StatementKey := ⟨``member, theoremStatementIdentity env ``member⟩
      let mut rejected := false
      try
        let index ← CensusQuery.indexScope env.header.mainModule
        discard <| CensusQuery.assess index "fixture-head" key
      catch error =>
        rejected := (← error.toMessageData.toString).endsWith "invalid=maximal_catalog_membership"
      unless rejected do
        throwError "StructuralPositiveMissingPeer: stale singleton positive evidence accepted"
  finally
    setEnv original

structural_theorem peer in law realization readouts nondegeneracy nondegenerate :=
  fun n => Nat.mod_lt n (by decide)
def catalogValue : StructuralCatalog arena :=
  ⟨Fin 2, inferInstance, inferInstance, fun _ => member.__structural_unit⟩
theorem registration : StructuralRegistrationEvidence ``member arena member.__structural_unit
    catalogValue (0 : Fin 2) (∀ n : Nat, n % 2 < 2) := ⟨rfl, rfl⟩
theorem peerRegistration : StructuralRegistrationEvidence ``peer arena peer.__structural_unit
    catalogValue (1 : Fin 2) (∀ n : Nat, n % 2 < 2) := ⟨rfl, rfl⟩
theorem allTrivial (i : Fin 2) : catalogValue.TrivialInCatalog i := by
  intro strict
  apply strict.2
  intro s t without index _ primitive
  have other : ∃ j : Fin 2, j ≠ i := by
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  obtain ⟨j, different⟩ := other
  exact without j different primitive
theorem triviality : catalogValue.TrivialInCatalog (0 : Fin 2) := allTrivial 0
theorem peerTriviality : catalogValue.TrivialInCatalog (1 : Fin 2) := allTrivial 1
def catalogSeal : StructuralCatalogSeal catalogValue := ⟨fun i => .isFalse (allTrivial i)⟩

run_cmd liftTermElabM do
  let env ← getEnv
  for name in [``member, ``peer] do
    let key : StatementKey := ⟨name, theoremStatementIdentity env name⟩
    let row ← CensusQuery.assess (← CensusQuery.indexScope env.header.mainModule) "fixture-head" key
    unless row.className == "trivial_in_catalog" do
      throwError "StructuralPositiveMissingPeer: complete reseal does not certify {name} as trivial"

end LeanInformationAudit.Tests.Census.StructuralPositiveMissingPeer
