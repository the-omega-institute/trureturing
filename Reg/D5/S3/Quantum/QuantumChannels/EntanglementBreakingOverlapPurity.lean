import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the projector-product trace identity. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity

open _root_.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the trace coordinate of the product of the two projectors. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun d => Matrix (Fin d) (Fin d) ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ M => Matrix.trace M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)),
    R.readout () d (projector v * projector w) = (‖⟪v, w⟫_ℂ‖ ^ 2 : ℝ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (0 : EuclideanSpace ℂ (Fin 1)) 0
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change Matrix.trace (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠
    Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ)
  norm_num

def source_registration : Registration arena (type_of% @trace_projectors) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_projectors, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_projectors) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.trace_unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => Matrix.trace M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.trace_projectors
#print axioms source_registration
#print axioms registration

namespace ProjectorTrace

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the unit-vector hypothesis while observing its projector's trace. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) (_hv : ‖v‖ = 1),
    R.readout () d (projector v) = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ)))
    (by simp [EuclideanSpace.norm_eq])
  norm_num [rejected, realize] at hb

def family : Registration arena (type_of% @projector_trace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨projector_trace, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@projector_trace) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.projector_trace_unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.ProjectorTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => Matrix.trace M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.projector_trace
#print axioms family
#print axioms registration

end ProjectorTrace

namespace UnitRay

universe u_1

/-- Observe the outer projector as its generating vector varies. -/
abbrev signature : Signature where
  Params := Type u_1
  State n := n → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature (fun _ _ ψ => vecMulVec ψ (star ψ)) (fun e => nomatch e)

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain both normalization hypotheses and the equality on a common complex ray. -/
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {n : Type u_1} [Fintype n] {ψ χ : n → ℂ}
    (_hψ : star ψ ⬝ᵥ ψ = 1) (_hχ : star χ ⬝ᵥ χ = 1)
    (z : ℂ) (_hz : ψ = z • χ),
    R.readout () n ψ = vecMulVec χ (star χ)

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  have hh := @h (ULift.{u_1} Unit) inferInstance (fun _ => 1) (fun _ => 1)
    (by simp [dotProduct]) (by simp [dotProduct]) 1 (by simp)
  have he : (0 : ℂ) = 1 * star (1 : ℂ) :=
    congrArg (fun M => M (ULift.up ()) (ULift.up ())) hh
  norm_num at he

theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨ULift.{u_1} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrArg (fun M => M (ULift.up ()) (ULift.up ())) h
  simp [actual, realize, vecMulVec_apply] at he

def family : Registration arena.{u_1} (type_of% (@vecMulVec_eq_of_unit_ray.{u_1})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@vecMulVec_eq_of_unit_ray, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@vecMulVec_eq_of_unit_ray.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.unit_ray_unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.UnitRay.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print
  _root_.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity.vecMulVec_eq_of_unit_ray
#print axioms family
#print axioms registration

end UnitRay

end
end Reg.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity
