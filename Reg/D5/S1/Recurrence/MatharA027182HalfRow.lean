import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.MatharA027182HalfRow
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection

/-! Source-bound audits of the half-row recurrence. -/

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Recurrence.MatharA027182HalfRow
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.MatharA027182HalfRow
noncomputable section

private lemma b_varies : b 0 ≠ b 1 := by decide

namespace half_row_recurrence
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
  (fun _ _ n => b n) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ n : ℕ, 6 ≤ n →
    -((n : ℤ) + 2) * (3 * (n : ℤ) - 20) * b n
      - ((n : ℤ) + 1) * (3 * (n : ℤ) - 11) * b (n - 1)
      + (33 * (n : ℤ) ^ 2 - 180 * (n : ℤ) - 100) * b (n - 2)
      + (15 * (n : ℤ) ^ 2 - 56 * (n : ℤ) + 1) * b (n - 3)
      + 2 * (-51 * (n : ℤ) ^ 2 + 313 * (n : ℤ) - 208) * b (n - 4)
      - 12 * ((n : ℤ) - 1) * ((n : ℤ) - 4) * b (n - 5)
      + 8 * (9 * (n : ℤ) - 11) * ((n : ℤ) - 5) * b (n - 6)
      + 4 * (-24 * (n : ℤ) ^ 2 + 196 * (n : ℤ) - 365) = 0
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 6 ≤ n →
    -((n : ℤ) + 2) * (3 * (n : ℤ) - 20) * R.readout () () n
      - ((n : ℤ) + 1) * (3 * (n : ℤ) - 11) * R.readout () () (n - 1)
      + (33 * (n : ℤ) ^ 2 - 180 * (n : ℤ) - 100) * R.readout () () (n - 2)
      + (15 * (n : ℤ) ^ 2 - 56 * (n : ℤ) + 1) * R.readout () () (n - 3)
      + 2 * (-51 * (n : ℤ) ^ 2 + 313 * (n : ℤ) - 208) * R.readout () () (n - 4)
      - 12 * ((n : ℤ) - 1) * ((n : ℤ) - 4) * R.readout () () (n - 5)
      + 8 * (9 * (n : ℤ) - 11) * ((n : ℤ) - 5) * R.readout () () (n - 6)
      + 4 * (-24 * (n : ℤ) ^ 2 + 196 * (n : ℤ) - 365) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 6 (by norm_num)
  norm_num [rejected, realize] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Recurrence.MatharA027182HalfRow.half_row_recurrence, rejected,
    rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, b_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.MatharA027182HalfRow.half_row_recurrence)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => b n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S1.Recurrence.MatharA027182HalfRow.half_row_recurrence.__information_unit,
  realizationName := `Reg.D5.S1.Recurrence.MatharA027182HalfRow.half_row_recurrence.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => b n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Recurrence.MatharA027182HalfRow, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg",
        "fn", "arg", "fn", "arg", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end half_row_recurrence

end
end Reg.D5.S1.Recurrence.MatharA027182HalfRow
