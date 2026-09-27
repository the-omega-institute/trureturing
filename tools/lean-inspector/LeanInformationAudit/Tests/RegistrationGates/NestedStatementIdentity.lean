import LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries

open Lean LeanInformationAudit.RegistrationGates
namespace NestedStatementIdentity

def computed : Prop := Bool.rec (motive := fun _ => Prop) False ((137 : Nat) = 137) true
def aliasStatement : Prop := (137 : Nat) = 137

theorem quantifiedTarget : ∀ _ : Unit, computed := by intro; rfl
theorem quantifiedAliasTarget : ∀ _ : Unit, aliasStatement := by intro; rfl
theorem conjoinedTarget : computed ∧ True := ⟨rfl, trivial⟩
theorem disjoinedTarget : computed ∨ False := Or.inl rfl
theorem existentialTarget : ∃ _ : Unit, computed := ⟨(), rfl⟩
theorem quantifiedProof : ∀ _ : Unit, (137 : Nat) = 137 := by intro; rfl
theorem conjoinedProof : ((137 : Nat) = 137) ∧ True := ⟨rfl, trivial⟩
theorem disjoinedProof : ((137 : Nat) = 137) ∨ False := Or.inl rfl
theorem existentialProof : ∃ _ : Unit, (137 : Nat) = 137 := ⟨(), rfl⟩
def quantifiedRead (_ : Unit) (state : Bool) := AllowlistBoundaries.keep quantifiedProof state
def conjoinedRead (_ : Unit) (state : Bool) := AllowlistBoundaries.keep conjoinedProof state
def disjoinedRead (_ : Unit) (state : Bool) := AllowlistBoundaries.keep disjoinedProof state
def existentialRead (_ : Unit) (state : Bool) := AllowlistBoundaries.keep existentialProof state

run_cmd Elab.Command.liftCoreM do
  for (label, statement, readout) in [
      ("QuantifiedComputedIdentity", ``quantifiedTarget, ``quantifiedRead),
      ("QuantifiedAliasIdentity", ``quantifiedAliasTarget, ``quantifiedRead),
      ("ConjoinedComputedIdentity", ``conjoinedTarget, ``conjoinedRead),
      ("DisjoinedComputedIdentity", ``disjoinedTarget, ``disjoinedRead),
      ("ExistentialComputedIdentity", ``existentialTarget, ``existentialRead)] do
    let actual ← readoutClosure (← getEnv) statement (mkConst readout)
    if actual.1 && actual.2.isSome then logInfo m!"[PASS] {label}: {actual}"
    else logError m!"[FAIL] {label}: expected completed identity rejection; actual={actual}"
end NestedStatementIdentity
