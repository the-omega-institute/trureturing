import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.Coexistence
universe u
variable (A : Type u)
def identity (a : A) : A := a
private theorem identity_apply (a : A) : identity A a = a := rfl
protected theorem arithmetic : 2 + 3 = (5 : Nat) := by decide

noncomputable def ordinaryValue : Nat := 0
mutual
def mathematicalValue : Nat := by_elab pure (Lean.mkNatLit 7)
def entry : Contract.Seal := { rootId := `root, options := #[] }
end
def catalog : Contract.RootCatalog := {
  data := {
    rootId := `root
    expected := #[{
      statement := _
      proof := entry.eq_1
      theoremName := `ContractReferenceFixtures.Coexistence.entry.eq_1
      objectArenaName := `Nat
      statementIdentity := none
      registrationModuleName := `LeanInformationAuditRegTests.ContractReferenceFixtures.Coexistence }]
    source := #[{
      statement := _
      proof := entry.eq_def
      theoremName := `ContractReferenceFixtures.Coexistence.entry.eq_def
      objectArenaName := `Nat
      statementIdentity := none
      registrationModuleName := `LeanInformationAuditRegTests.ContractReferenceFixtures.Coexistence }]
    baseline := #[]
    companionPrefix := none } }
end ContractReferenceFixtures.Coexistence
