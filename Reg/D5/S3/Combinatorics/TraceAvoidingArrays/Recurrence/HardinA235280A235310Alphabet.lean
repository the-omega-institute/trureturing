import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Batteries.Tactic.OpenPrivate

/-! Source-bound readouts for the two literal alphabet comparisons. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C a235280 a235310)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private Grid Legal from D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

private def legalDecidable (M S n k : ℕ) (a : Grid M n k) : Decidable (Legal S a) := by
  unfold Legal
  infer_instance

private def literalCard (M S n k : ℕ) : ℕ :=
  letI : DecidablePred (Legal (M := M) (n := n) (k := k) S) := legalDecidable M S n k
  (Finset.univ.filter (Legal (M := M) (n := n) (k := k) S)).card

private theorem count_eq_literalCard (M S n k : ℕ) : C M S n k = literalCard M S n k := by
  let _ : DecidablePred (Legal (M := M) (n := n) (k := k) S) := legalDecidable M S n k
  unfold C literalCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

namespace A235280

private def actual : Realization signature :=
  realize signature (fun _ n k => C 4 5 n k) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ n k => if n = 1 ∧ k = 1 then C 4 5 n k + 1 else C 4 5 n k)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k →
    R.readout () n k = C 5 7 n k ∧ C 5 7 n k = C 6 9 n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 1 1 (by decide) (by decide)).1
  have good := (a235280 1 1 (by decide) (by decide)).1
  change C 4 5 1 1 + 1 = C 5 7 1 1 at bad
  omega

set_option maxRecDepth 64000 in
set_option maxHeartbeats 2000000 in
private theorem small_counts : C 4 5 1 0 = 25 ∧ C 4 5 1 1 = 40 := by
  rw [count_eq_literalCard, count_eq_literalCard]
  decide +kernel

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 0, 1, ?_⟩
  change C 4 5 1 0 ≠ C 4 5 1 1
  rw [small_counts.1, small_counts.2]
  decide

def family : Registration arena (type_of% @a235280) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨a235280, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@a235280) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet.A235280.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet.A235280.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => C 4 5 n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end A235280

namespace A235310

private def actual : Realization signature :=
  realize signature (fun _ n k => C 5 6 n k) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ n k => if n = 1 ∧ k = 1 then C 5 6 n k + 1 else C 5 6 n k)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k →
    R.readout () n k = C 6 8 n k ∧ C 6 8 n k = C 7 10 n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 1 1 (by decide) (by decide)).1
  have good := (a235310 1 1 (by decide) (by decide)).1
  change C 5 6 1 1 + 1 = C 6 8 1 1 at bad
  omega

set_option maxRecDepth 64000 in
set_option maxHeartbeats 2000000 in
private theorem small_counts : C 5 6 1 0 = 36 ∧ C 5 6 1 1 = 70 := by
  rw [count_eq_literalCard, count_eq_literalCard]
  decide +kernel

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 0, 1, ?_⟩
  change C 5 6 1 0 ≠ C 5 6 1 1
  rw [small_counts.1, small_counts.2]
  decide

def family : Registration arena (type_of% @a235310) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨a235310, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@a235310) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet.A235310.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet.A235310.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => C 5 6 n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end A235310

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
