import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The native count as a source-bound observation in the full recurrence. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

private instance {n : ℕ} (A : Fin n × Fin 3 → Fin 2) : Decidable (Admissible A) :=
  inferInstanceAs (Decidable ((∀ i : Fin n, i.val = 0 → A (i,0) = 0) ∧
    ∀ p : Fin n × Fin 3,
    (Finset.univ.filter (fun q : Fin n × Fin 3 =>
      q ≠ p ∧ q.1.val ≤ p.1.val+1 ∧ p.1.val ≤ q.1.val+1 ∧
      q.2.val ≤ p.2.val+1 ∧ p.2.val ≤ q.2.val+1 ∧ A q ≠ A p)).card ∈
      ({0,1,2,5} : Finset ℕ)))

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 8 < n →
    R.readout () () n = a (n-1) + 2*a (n-2) +
      3*a (n-3) + 2*a (n-4) - 2*a (n-5) - 6*a (n-6) - 4*a (n-7)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn := h 9 (by decide)
  change a 9 + 1 = _ at hn
  have hr := result 9 (by decide)
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change a 2 ≠ a 3
  unfold a
  simp only [Nat.card_eq_fintype_card]
  decide +kernel

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip
    definition := some {
      owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip
      name := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip.claim
      path := #[] }
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA303956KingStrip
