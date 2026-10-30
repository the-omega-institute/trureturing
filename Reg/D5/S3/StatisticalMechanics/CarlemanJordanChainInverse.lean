import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CarlemanJordanChainInverse
import Reg.Support.DependentFamily

/-! Source-bound audit of the inverse of a normalized Carleman Jordan chain. -/

namespace Reg.D5.S3.StatisticalMechanics.CarlemanJordanChainInverse

open _root_.D5.S3.StatisticalMechanics.CarlemanJordanChainInverse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the inverse matrix in each truncation size. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n) (Fin n) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => w⁻¹) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain every coefficient hypothesis, existence, invertibility, and inverse entry. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ α : ℕ → ℝ, α 0 = 0 → α 1 = 1 → α 2 ≠ 0 →
    ∀ n : ℕ, 0 < n → (∃ w, IsJordanChain α n w) ∧
      ∀ w, IsJordanChain α n w → IsUnit w.det ∧
        ∀ k j : Fin n, k ≤ j → r.readout () n w k j = sigma α n k.val j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let α : ℕ → ℝ := fun i => if i = 0 then 0 else 1
  have hα0 : α 0 = 0 := by norm_num [α]
  have hα1 : α 1 = 1 := by norm_num [α]
  have hα2 : α 2 ≠ 0 := by norm_num [α]
  obtain ⟨⟨w, hw⟩, hall⟩ := h α hα0 hα1 hα2 1 (by decide)
  have hbad := (hall w hw).2 0 0 (le_refl _)
  change (0 : ℝ) = sigma α 1 0 0 at hbad
  norm_num [sigma] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change (0 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ ≠ 1⁻¹
  simp

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w⁻¹) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CarlemanJordanChainInverse
    definition := some {
      owner := `D5.S3.StatisticalMechanics.CarlemanJordanChainInverse
      name := `D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.claim
      path := #[] }
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "body",
        "arg", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.CarlemanJordanChainInverse
