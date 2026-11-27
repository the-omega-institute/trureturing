import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound readout of literal stress-three counts. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C Grid Legal)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ h w => C 3 3 h w) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ h w =>
    if h = 1 ∧ w = 1 then C 3 3 h w + 1 else C 3 3 h w) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h w : ℕ), 0 < h → 0 < w →
    R.readout () h w = Nat.card {rc : Word h × Word w // CodeOK rc.1 rc.2}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad := law 1 1 (by decide) (by decide)
  have good := count_codes 1 1 (by decide) (by decide)
  dsimp [rejected, realize] at bad
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
theorem small_counts : C 3 3 1 1 = 40 ∧ C 3 3 1 2 = 108 := by
  rw [count_eq_literalCard, count_eq_literalCard]
  decide +kernel

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change C 3 3 1 1 ≠ C 3 3 1 2
  rw [small_counts.1, small_counts.2]
  decide

def family : Registration arena (type_of% @count_codes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨count_codes, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_codes) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ h w => C 3 3 h w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding
