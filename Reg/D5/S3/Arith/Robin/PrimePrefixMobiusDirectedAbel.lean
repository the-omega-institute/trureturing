import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel
import Reg.Support.DependentFamily
namespace Reg.D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel
open Finset
open _root_.D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Steps
abbrev signature : Signature where
  Params := ℕ → ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D M : ℕ}, D < M → ∀ b : ℕ → ℝ,
    (∑ n ∈ Ioc D (M-1), R.readout () b n) = b (D+1)-b M
def actual : Realization signature :=
  realize signature (fun _ b n => b n-b (n+1)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (D := 0) (M := 2) (by omega) (fun n => n)
  norm_num [rejected, realize] at hh

def registration : Registration arena (type_of% @step_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@step_sum, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨(fun n => (n : ℝ)^2), 0, 1, ?_⟩
    norm_num [actual, realize]
noncomputable def registration_1 :
    Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@step_sum) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel.stepsUnit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel.Steps.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨registration⟩⟩
  options := #[] }
end Steps
namespace Abel
abbrev signature : Signature where
  Params := (ℕ → ℝ) × (ℕ → ℝ)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D M : ℕ}, D < M → ∀ a b : ℕ → ℝ,
    (∑ n ∈ Ioc D M, R.readout () (a,b) n) =
      b M*((∑ n ∈ range (M+1), a n)-(∑ n ∈ range (D+1), a n)) +
        ∑ n ∈ Ioc D (M-1), (b n-b (n+1))*
          ((∑ k ∈ range (n+1), a k)-(∑ k ∈ range (D+1), a k))
def actual : Realization signature :=
  realize signature (fun _ p n => p.1 n*p.2 n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (D := 0) (M := 1) (by omega) (fun _ => 1) (fun _ => 1)
  norm_num [rejected, realize, sum_const] at hh

def registration : Registration arena (type_of% @anchored_sum_by_parts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@anchored_sum_by_parts, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨((fun n => (n : ℝ)), (fun _ => 1)), 0, 1, ?_⟩
    norm_num [actual, realize]
noncomputable def registration_1 :
    Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@anchored_sum_by_parts) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel.abelUnit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel.Abel.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨registration⟩⟩
  options := #[] }
end Abel
#print axioms Steps.registration
#print axioms Abel.registration
end
end Reg.D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel
