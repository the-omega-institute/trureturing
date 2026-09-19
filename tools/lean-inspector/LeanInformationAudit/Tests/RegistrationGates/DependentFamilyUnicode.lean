import LeanInformationAudit.Tests.RegistrationGates.DependentFamily

namespace LeanInformationAudit.Tests.DependentFamilyUnicode
open Lean Meta Elab Command
open _root_.LeanInformationAudit.DependentFamily
universe 𝒰 𝒱
noncomputable section

theorem 𝒜 (_α : Type 𝒰) (_β : Type 𝒱) : ∀ x : Bool, x = x := fun _ => rfl

def signature : Signature where
  Θ := Σ _ : Type 𝒰, Type 𝒱
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{𝒰,𝒱}
  Law r := ∀ α β x, r.readout () ⟨α, β⟩ x = x

def bad : Realization signature.{𝒰,𝒱} where
  readout _ _ _ := false
  anchor := Empty.elim

def registration : Registration arena.{𝒰,𝒱} (∀ α : Type 𝒰, ∀ β : Type 𝒱, ∀ x : Bool, x = x) where
  realization := DependentFamily.template signature (fun _ _ x => x) Empty.elim
  bridge := fun h => h
  variation := ⟨DependentFamily.template signature (fun _ _ x => x) Empty.elim, bad,
    𝒜, fun h => Bool.false_ne_true (h PUnit PUnit true)⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨DependentFamily.template signature (fun _ _ x => x) Empty.elim, bad, ?_, rfl, ?_⟩
      · intro j h
        exact False.elim (h (@Subsingleton.elim Unit inferInstance j i))
      · exact ⟨fun _ h => Bool.false_ne_true (h PUnit PUnit true), fun _ => 𝒜⟩
    · intro i
      exact Empty.elim i

register_information_family 𝒜 in arena
  readout via (DependentFamily.template signature (fun _ _ x => x) Empty.elim)
  realization registration
  escape from coordinates [0, 1]
  state ["body", "body", "domain"] output ["body", "body", "domain"]
  escape continues (open)

run_cmd do
  let some row := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``𝒜) | throwError "missing Unicode family"
  match row.result with
  | .declaredValidated _ => logInfo "[PASS] unicode_family_source_and_rigid_levels"
  | .declaredUnresolved diagnostic => throwError diagnostic
  | _ => throwError "Unicode family undeclared"

end
end LeanInformationAudit.Tests.DependentFamilyUnicode
