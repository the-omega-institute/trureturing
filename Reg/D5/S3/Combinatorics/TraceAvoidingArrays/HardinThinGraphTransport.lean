import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ × ℕ × ℕ × ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ n =>
    (Nat.card ((stripGraph true n 1).Coloring (Fin 3)),
     Nat.card ((stripGraph false n 1).Coloring (Fin 3)),
     Nat.card ((stripGraph true n 2).Coloring (Fin 3)),
     Nat.card ((stripGraph false n 2).Coloring (Fin 3)))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 1, 0, 0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, (R.readout () () n).1 = (R.readout () () n).2.1 ∧
    (R.readout () () n).2.2.1 = (R.readout () () n).2.2.2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 0).1
  change (0 : ℕ) = 1 at h0
  omega

/-- Exact positive law and full-family intervention. -/
def variation : Variation arena actual := by
  exact ⟨result, rejected, rejected_law⟩

/-- Sensitivity of the selected complete count vector under a whole-family intervention. -/
def sensitivity : Sensitivity arena actual :=
  _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

/-- The raw count-vector law has the full original quantifier and both widths. -/
def bridge : (type_of% @result) ↔ arena.Law actual := Iff.rfl

private theorem small_counts :
    Nat.card ((stripGraph true 0 1).Coloring (Fin 3)) = 6 ∧
    Nat.card ((stripGraph true 1 1).Coloring (Fin 3)) = 18 := by
  constructor
  · rw [Nat.card_congr (colouringEquiv true 0 1), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_congr (colouringEquiv true 1 1), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    decide +kernel

/-- Actual observations differ at heights one and two, independently of interventions. -/
def dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro he
  have h := congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.1) he
  change Nat.card ((stripGraph true 0 1).Coloring (Fin 3)) =
    Nat.card ((stripGraph true 1 1).Coloring (Fin 3)) at h
  rw [small_counts.1,small_counts.2] at h
  omega

/-- Complete typed family obligations; the raw source occurrence binding is separate. -/
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

/-- The raw source has four count occurrences, rather than a count-vector occurrence.
Exact source selection is unresolved under the source-owner issue #30456. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n =>
    (Nat.card ((stripGraph true n 1).Coloring (Fin 3)),
     Nat.card ((stripGraph false n 1).Coloring (Fin 3)),
     Nat.card ((stripGraph true n 2).Coloring (Fin 3)),
     Nat.card ((stripGraph false n 2).Coloring (Fin 3)))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Normalized
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ × ℕ × ℕ × ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ n =>
    (Nat.card (literalStrip true n 1),
     _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip.a (n+1),
     Nat.card (literalStrip true n 2),
     _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip.a (n+1))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0,1,0,0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, (R.readout () () n).1 = (R.readout () () n).2.1 ∧
    (R.readout () () n).2.2.1 = (R.readout () () n).2.2.2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 0).1
  change (0 : ℕ) = 1 at h0
  omega
private theorem first_counts :
    _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip.a 1 = 1 ∧
    _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip.a 2 = 8 := by
  constructor <;>
    unfold _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip.a <;>
    decide +kernel

def family : Registration arena (type_of% @normalized_result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨normalized_result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    intro he
    have h := congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.1) he
    change Nat.card (literalStrip true 0 1) = Nat.card (literalStrip true 1 1) at h
    rw [(normalized_result 0).1,(normalized_result 1).1,first_counts.1,first_counts.2] at h
    omega

/-- The family obligations are proved; exact raw occurrence selection is unresolved. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@normalized_result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.Normalized.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.Normalized.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Normalized

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.TransitionCounts
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Row 2) (fun _ => Bool) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ p b => K (boundaryClass p) b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p b => K (boundaryClass p) b + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (d : Bool) (p : Row 1), proper p →
      (∑ q : Row 1, if proper q ∧ compatible d p q then 1 else 0) = 3) ∧
    (∀ (d : Bool) (p : Row 2), proper p → ∀ b : Bool,
      (∑ q : Row 2, if proper q ∧ compatible d p q ∧ boundaryClass q = b then 1 else 0)
        = R.readout () p b)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : proper (![0, 1, 0] : Row 2) := by decide +kernel
  have hb := h.2 true ![0, 1, 0] hp true
  have ha := transition_counts.2 true ![0, 1, 0] hp true
  change _ = K (boundaryClass ![0, 1, 0]) true + 1 at hb
  omega

def family : Registration arena (type_of% @transition_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨![0, 1, 0], true, false, ?_⟩
    change K true true ≠ K true false
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.TransitionCounts.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => K (boundaryClass p) b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.TransitionCounts
