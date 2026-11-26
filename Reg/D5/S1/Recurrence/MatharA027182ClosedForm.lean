import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.MatharA027182ClosedForm
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection

/-! Source-bound audits of the all-index closed form. -/

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Recurrence.MatharA027182SelfConvolution
open D5.S1.Recurrence.MatharA027182ClosedForm
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.MatharA027182ClosedForm
noncomputable section

private lemma a_varies : (a 0 : ℤ) ≠ (a 1 : ℤ) := by
  rw [closed_form 0, closed_form 1]
  decide

namespace closed_form
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
  (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ n : ℕ,
  (a n : ℤ) = 4 * ((2 * n + 4).choose (n + 2) : ℤ) + 4 * ((2 * n + 2).choose (n + 1) : ℤ)
    + ((2 * n).choose n : ℤ) - 72 * 2 ^ n + 16 * n + 40
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    R.readout () () n = 4 * ((2 * n + 4).choose (n + 2) : ℤ)
      + 4 * ((2 * n + 2).choose (n + 1) : ℤ) + ((2 * n).choose n : ℤ) - 72 * 2 ^ n + 16 * n + 40
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected, realize, Nat.choose] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Recurrence.MatharA027182ClosedForm.closed_form, rejected,
    rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, a_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.MatharA027182ClosedForm.closed_form)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S1.Recurrence.MatharA027182ClosedForm.closed_form.__information_unit,
  realizationName := `Reg.D5.S1.Recurrence.MatharA027182ClosedForm.closed_form.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Recurrence.MatharA027182ClosedForm, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end closed_form

end
end Reg.D5.S1.Recurrence.MatharA027182ClosedForm
