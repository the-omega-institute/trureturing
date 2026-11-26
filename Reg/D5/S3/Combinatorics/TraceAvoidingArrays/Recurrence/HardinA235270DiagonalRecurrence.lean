import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235270DiagonalRecurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound readout of the recurrence for the literal square count. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235270DiagonalRecurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235270DiagonalRecurrence (a235270_order11)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private Legal from D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => (C 4 5 n n : ℤ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ n =>
    if n = 12 then (C 4 5 n n : ℤ) + 1 else (C 4 5 n n : ℤ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 1 ≤ n →
    R.readout () () (n + 11) =
      R.readout () () (n + 10) + 23 * R.readout () () (n + 9)
      - 23 * R.readout () () (n + 8) - 200 * R.readout () () (n + 7)
      + 200 * R.readout () () (n + 6) + 820 * R.readout () () (n + 5)
      - 820 * R.readout () () (n + 4) - 1584 * R.readout () () (n + 3)
      + 1584 * R.readout () () (n + 2) + 1152 * R.readout () () (n + 1)
      - 1152 * R.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 1 (by decide)
  have good := a235270_order11 1 (by decide)
  dsimp [rejected, realize] at bad
  norm_num at bad good
  omega

private def literalCard (n : ℕ) : ℕ :=
  letI legal (g : Fin (n + 1) × Fin (n + 1) → Fin 5) : Decidable (Legal (M := 4) (n := n) (k := n) 5 g) := by
    unfold Legal
    infer_instance
  (Finset.univ.filter (Legal (M := 4) (n := n) (k := n) 5)).card

private theorem count_eq_literalCard (n : ℕ) : (C 4 5 n n : ℤ) = (literalCard n : ℤ) := by
  let legal (g : Fin (n + 1) × Fin (n + 1) → Fin 5) : Decidable (Legal (M := 4) (n := n) (k := n) 5 g) := by
    unfold Legal
    infer_instance
  unfold C literalCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 5000000 in
private theorem diagonal_counts : (C 4 5 0 0 : ℤ) = 5 ∧ (C 4 5 1 1 : ℤ) = 40 := by
  rw [count_eq_literalCard, count_eq_literalCard]
  decide +kernel

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change (C 4 5 0 0 : ℤ) ≠ (C 4 5 1 1 : ℤ)
  rw [diagonal_counts.1, diagonal_counts.2]
  decide

def family : Registration arena (type_of% @a235270_order11) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨a235270_order11, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@a235270_order11) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235270DiagonalRecurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235270DiagonalRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (C 4 5 n n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235270DiagonalRecurrence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235270DiagonalRecurrence
