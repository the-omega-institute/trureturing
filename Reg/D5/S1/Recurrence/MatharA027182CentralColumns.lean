import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.MatharA027182CentralColumns
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection

/-! Source-bound audits of the two middle-column recurrences. -/

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Recurrence.MatharA027182CentralColumns
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.MatharA027182CentralColumns
noncomputable section

private lemma u_varies : u 0 ≠ u 1 := by decide

private lemma v_varies : v 1 ≠ v 2 := by decide

namespace u_recurrence
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Output _ _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ n => u n) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ n : ℕ, 2 ≤ n →
  2 * ((n : ℤ) + 1) * u n - (7 * (n : ℤ) + 5) * u (n - 1)
    + 2 * (3 - 2 * (n : ℤ)) * u (n - 2) + 12 * (1 - 3 * (n : ℤ)) = 0
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n →
    2 * ((n : ℤ) + 1) * R.readout () () n - (7 * (n : ℤ) + 5) * R.readout () () (n - 1)
      + 2 * (3 - 2 * (n : ℤ)) * R.readout () () (n - 2) + 12 * (1 - 3 * (n : ℤ)) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 (by norm_num)
  norm_num [rejected, realize] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Recurrence.MatharA027182CentralColumns.u_recurrence, rejected,
    rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, u_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.MatharA027182CentralColumns.u_recurrence)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => u n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S1.Recurrence.MatharA027182CentralColumns.u_recurrence.__information_unit,
  realizationName := `Reg.D5.S1.Recurrence.MatharA027182CentralColumns.u_recurrence.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => u n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Recurrence.MatharA027182CentralColumns, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end u_recurrence

namespace v_recurrence
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Output _ _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ n => v n) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ n : ℕ, 3 ≤ n →
  2 * ((n : ℤ) + 1) * v n - (7 * (n : ℤ) + 5) * v (n - 1)
    + 2 * (3 - 2 * (n : ℤ)) * v (n - 2) + 12 * (1 - 3 * (n : ℤ)) = 0
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 3 ≤ n →
    2 * ((n : ℤ) + 1) * R.readout () () n - (7 * (n : ℤ) + 5) * R.readout () () (n - 1)
      + 2 * (3 - 2 * (n : ℤ)) * R.readout () () (n - 2) + 12 * (1 - 3 * (n : ℤ)) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 3 (by norm_num)
  norm_num [rejected, realize] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Recurrence.MatharA027182CentralColumns.v_recurrence, rejected,
    rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 1, 2, v_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.MatharA027182CentralColumns.v_recurrence)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => v n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S1.Recurrence.MatharA027182CentralColumns.v_recurrence.__information_unit,
  realizationName := `Reg.D5.S1.Recurrence.MatharA027182CentralColumns.v_recurrence.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => v n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Recurrence.MatharA027182CentralColumns, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end v_recurrence

end
end Reg.D5.S1.Recurrence.MatharA027182CentralColumns
