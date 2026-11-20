import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.Coding.FiniteCodeDefect
import Reg.Support.UniverseSingleReadout

/-! The full labelled-word telescope, observing the reconstruction's flatMap operand. -/

namespace Reg.D5.S0.Computability.Coding.FiniteCodeDefect

open _root_.D5.S0.Computability.Coding.FiniteCodeDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature
    (Σ α : Type u, Σ m : ℕ, Fin m → List α)
    (fun p => List (Fin p.2.1)) (fun p => List p.1)

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => s.flatMap p.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} {n : ℕ} (f : Fin n → List α),
    (¬ Function.Injective (fun s : List (Fin n) => s.flatMap f)) →
    ∃ m : ℕ, m < n ∧ ∃ g : Fin m → List α,
      ∃ c : Fin n → List (Fin m), ∀ i,
        f i = R.readout () ⟨α, m, g⟩ (c i)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let f : Fin 2 → List (ULift.{u} Unit) := fun _ => [⟨()⟩]
  have ha : ¬ Function.Injective (fun s : List (Fin 2) => s.flatMap f) := by
    intro hi
    have he : ([0] : List (Fin 2)) = [1] := hi (by simp [f])
    have hv := congrArg (fun s : List (Fin 2) => s.map Fin.val) he
    norm_num at hv
  obtain ⟨m, hm, g, c, hc⟩ := @h (ULift.{u} Unit) 2 f ha
  have hz := hc 0
  change ([⟨()⟩] : List (ULift.{u} Unit)) = [] at hz
  simp at hz

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, 1, fun _ => [⟨()⟩]⟩, [], [0], ?_⟩
  simp [actual, realize]

def source_registration : Registration arena.{u}
    (type_of% @finite_code_defect.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_code_defect, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_code_defect.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S0.Computability.Coding.FiniteCodeDefect.finite_code_defect.__information_unit
  realizationName := `Reg.D5.S0.Computability.Coding.FiniteCodeDefect.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p s => s.flatMap p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.Coding.FiniteCodeDefect
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "arg", "body", "arg", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S0.Computability.Coding.FiniteCodeDefect
