import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235291Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound readout of the recurrence for the literal two-column count. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235291Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235291Recurrence (result)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
  (C Grid Legal)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option warningAsError true

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => (C 3 3 n 1 : ℤ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ n =>
    if n = 5 then (C 3 3 n 1 : ℤ) + 1 else (C 3 3 n 1 : ℤ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 5 ≤ n →
    R.readout () () n = 14 * R.readout () () (n - 2) - 48 * R.readout () () (n - 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 5 (by decide)
  have good := result 5 (by decide)
  dsimp [rejected, realize] at bad
  norm_num at bad good
  omega

private def legalDecidable (n : ℕ) (g : Grid 3 n 1) : Decidable (Legal 3 g) := by
  unfold Legal
  infer_instance

private def literalCard (n : ℕ) : ℕ :=
  letI : DecidablePred (Legal (M := 3) (n := n) (k := 1) 3) := legalDecidable n
  (Finset.univ.filter (Legal (M := 3) (n := n) (k := 1) 3)).card

private theorem count_eq_literalCard (n : ℕ) : (C 3 3 n 1 : ℤ) = (literalCard n : ℤ) := by
  let : DecidablePred (Legal (M := 3) (n := n) (k := 1) 3) := legalDecidable n
  unfold C literalCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 5000000 in
-- The dependence witness enumerates all indexed fillings at heights two and three.
private theorem dependence_counts : (C 3 3 1 1 : ℤ) = 40 ∧ (C 3 3 2 1 : ℤ) = 108 := by
  rw [count_eq_literalCard, count_eq_literalCard]
  decide +kernel

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change (C 3 3 1 1 : ℤ) ≠ (C 3 3 2 1 : ℤ)
  rw [dependence_counts.1, dependence_counts.2]
  decide

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235291Recurrence.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235291Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (C 3 3 n 1 : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235291Recurrence
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235291Recurrence
