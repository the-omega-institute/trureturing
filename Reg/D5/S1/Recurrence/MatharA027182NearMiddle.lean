import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.MatharA027182NearMiddle
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection

/-! Source-bound audits of the near-middle column recurrence. -/

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Recurrence.MatharA027182NearMiddle
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.MatharA027182NearMiddle
noncomputable section

private lemma z_varies : z 2 ≠ z 3 := by decide

namespace z_recurrence
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
  (fun _ _ n => z n) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ n : ℕ, 4 ≤ n →
  -2 * ((n : ℤ) + 3) * (139 * (n : ℤ) - 175) * z n
    + (1279 * (n : ℤ) ^ 2 + 1334 * (n : ℤ) - 1089) * z (n - 1)
    - 2 * (167 * (n : ℤ) + 121) * (2 * (n : ℤ) - 3) * z (n - 2)
    + 12 * (111 * (n : ℤ) ^ 2 + 456 * (n : ℤ) + 229) = 0
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 4 ≤ n →
    -2 * ((n : ℤ) + 3) * (139 * (n : ℤ) - 175) * R.readout () () n
      + (1279 * (n : ℤ) ^ 2 + 1334 * (n : ℤ) - 1089) * R.readout () () (n - 1)
      - 2 * (167 * (n : ℤ) + 121) * (2 * (n : ℤ) - 3) * R.readout () () (n - 2)
      + 12 * (111 * (n : ℤ) ^ 2 + 456 * (n : ℤ) + 229) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 4 (by norm_num)
  norm_num [rejected, realize] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Recurrence.MatharA027182NearMiddle.z_recurrence, rejected,
    rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 2, 3, z_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.MatharA027182NearMiddle.z_recurrence)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => z n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S1.Recurrence.MatharA027182NearMiddle.z_recurrence.__information_unit,
  realizationName := `Reg.D5.S1.Recurrence.MatharA027182NearMiddle.z_recurrence.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => z n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Recurrence.MatharA027182NearMiddle, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end z_recurrence

end
end Reg.D5.S1.Recurrence.MatharA027182NearMiddle
