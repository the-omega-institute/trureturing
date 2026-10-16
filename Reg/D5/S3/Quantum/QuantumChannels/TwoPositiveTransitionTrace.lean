import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
open _root_.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe the matrix paired with a rank-one operator. -/
abbrev signature : Signature where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (v : n → ℂ),
    (R.readout () n X * Matrix.vecMulVec v (star v)).trace =
      star v ⬝ᵥ (X *ᵥ v)

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have he := h (n := ULift.{u} Unit) 1 (fun _ => 1)
  norm_num [rejected, realize, Matrix.trace, dotProduct] at he
  change (0 : ℂ) = 1 at he
  exact zero_ne_one he

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨ULift.{u} Unit, 0, 1, ?_⟩
  intro he
  have hc := congrArg (fun X : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ =>
    X ⟨()⟩ ⟨()⟩) he
  change (0 : ℂ) = 1 at hc
  exact zero_ne_one hc

def source_registration : Registration arena.{u} (type_of% @trace_rank_one.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_rank_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_rank_one.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
