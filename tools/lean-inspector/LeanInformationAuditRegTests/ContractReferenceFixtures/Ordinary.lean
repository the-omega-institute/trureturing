import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.Ordinary
structure Box where
  T : Type
def box : Box := ⟨Nat⟩
def stored : box.T := (3 : Nat)
def typeLet : (let T := Nat; T) := 1
def typeLambda : (fun T : Type => T) Nat := 2
def funValue (n : Nat) : Nat := n + 1
theorem ordinary (n : Nat) : funValue n = n + 1 := rfl
end ContractReferenceFixtures.Ordinary
