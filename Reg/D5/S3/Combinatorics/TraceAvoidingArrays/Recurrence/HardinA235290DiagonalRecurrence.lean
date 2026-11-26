import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235290DiagonalRecurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! A source-bound readout of the literal integer counts along the square diagonal. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235290DiagonalRecurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235290DiagonalRecurrence
  (hardin_a235290)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
  (C Grid Legal)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option warningAsError true

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => (C 3 3 n n : ℤ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ n => if n = 12 then (C 3 3 n n : ℤ) + 1 else (C 3 3 n n : ℤ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 12 ≤ n →
    R.readout () () n =
      4 * R.readout () () (n-1) + 23 * R.readout () () (n-2) -
      92 * R.readout () () (n-3) - 200 * R.readout () () (n-4) +
      800 * R.readout () () (n-5) + 820 * R.readout () () (n-6) -
      3280 * R.readout () () (n-7) - 1584 * R.readout () () (n-8) +
      6336 * R.readout () () (n-9) + 1152 * R.readout () () (n-10) -
      4608 * R.readout () () (n-11)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 12 (by decide)
  have good := hardin_a235290 12 (by decide)
  dsimp [rejected, realize] at bad
  norm_num at bad good
  omega

private def legalDecidable (n : ℕ) (g : Grid 3 n n) : Decidable (Legal 3 g) := by
  unfold Legal
  infer_instance

private def literalCard (n : ℕ) : ℕ :=
  letI : DecidablePred (@Legal 3 n n 3) := legalDecidable n
  (Finset.univ.filter (@Legal 3 n n 3)).card

private theorem count_eq_literalCard (n : ℕ) : C 3 3 n n = literalCard n := by
  let _ : DecidablePred (@Legal 3 n n 3) := legalDecidable n
  unfold C literalCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem count_one : C 3 3 1 1 = 40 := by
  rw [count_eq_literalCard]
  decide +kernel

private theorem positive_counts_vary :
    ∃ n : ℕ, 1 ≤ n ∧ (C 3 3 1 1 : ℤ) ≠ (C 3 3 n n : ℤ) := by
  by_contra! constant
  have same (n : ℕ) (h : 1 ≤ n) : C 3 3 n n = 40 := by
    have hn := constant n h
    exact (Nat.cast_inj.mp hn).symm.trans count_one
  have recurrence := hardin_a235290 12 (by decide)
  norm_num at recurrence
  rw [same 12 (by decide), same 11 (by decide), same 10 (by decide),
    same 9 (by decide), same 8 (by decide), same 7 (by decide),
    same 6 (by decide), same 5 (by decide), same 4 (by decide),
    same 3 (by decide), same 2 (by decide), count_one] at recurrence
  norm_num at recurrence

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  obtain ⟨n, _, diff⟩ := positive_counts_vary
  exact ⟨(), 1, n, diff⟩

def family : Registration arena (type_of% @hardin_a235290) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hardin_a235290, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@hardin_a235290) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235290DiagonalRecurrence.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235290DiagonalRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (C 3 3 n n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235290DiagonalRecurrence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235290DiagonalRecurrence
