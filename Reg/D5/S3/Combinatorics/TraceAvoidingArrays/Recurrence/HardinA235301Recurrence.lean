import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound readout for the common ten-lag recurrence on rectangles. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence (hardin_a235301)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
  (C Grid Legal)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)

private def actual : Realization signature :=
  realize signature (fun _ h w => (C 3 3 h w : ℤ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ h w =>
    if h = 11 ∧ w = 1 then (C 3 3 h w : ℤ) + 1 else (C 3 3 h w : ℤ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k n : ℕ), 1 ≤ k → 11 ≤ n →
      R.readout () n k = 3 * R.readout () (n-1) k + 17 * R.readout () (n-2) k -
        57 * R.readout () (n-3) k - 86 * R.readout () (n-4) k +
        372 * R.readout () (n-5) k + 76 * R.readout () (n-6) k -
        972 * R.readout () (n-7) k + 360 * R.readout () (n-8) k +
        864 * R.readout () (n-9) k - 576 * R.readout () (n-10) k ∧
      R.readout () k n = 3 * R.readout () k (n-1) + 17 * R.readout () k (n-2) -
        57 * R.readout () k (n-3) - 86 * R.readout () k (n-4) +
        372 * R.readout () k (n-5) + 76 * R.readout () k (n-6) -
        972 * R.readout () k (n-7) + 360 * R.readout () k (n-8) +
        864 * R.readout () k (n-9) - 576 * R.readout () k (n-10)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 1 11 (by decide) (by decide)).1
  have good := (hardin_a235301 1 11 (by decide) (by decide)).1
  dsimp [rejected, realize] at bad
  norm_num at bad good
  omega

private def literalCard (h w : ℕ) : ℕ :=
  letI legal (g : Grid 3 h w) : Decidable (Legal 3 g) := by
    unfold Legal
    infer_instance
  (Finset.univ.filter (Legal (M := 3) (n := h) (k := w) 3)).card

private theorem count_eq_literalCard (h w : ℕ) : C 3 3 h w = literalCard h w := by
  let legal (g : Grid 3 h w) : Decidable (Legal 3 g) := by
    unfold Legal
    infer_instance
  unfold C literalCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 5000000 in
private theorem small_counts : C 3 3 1 1 = 40 ∧ C 3 3 1 2 = 108 := by
  rw [count_eq_literalCard, count_eq_literalCard]
  decide +kernel


private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change (C 3 3 1 1 : ℤ) ≠ (C 3 3 1 2 : ℤ)
  rw [small_counts.1, small_counts.2]
  decide

def family : Registration arena (type_of% @hardin_a235301) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hardin_a235301, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@hardin_a235301) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ h w => (C 3 3 h w : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence
