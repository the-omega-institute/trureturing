import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumChannels.ChannelTimeReversalNoGo
import Reg.Support.DependentFamily

/-! Source-bound registrations for the public channel time-reversal identities. -/

namespace Reg.D5.S3.QuantumChannels.ChannelTimeReversalNoGo

open _root_.D5.S3.QuantumChannels.ChannelTimeReversalNoGo
open _root_.D5.S3.Quantum.FiniteDimensional
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace PauliExpansion

abbrev signature : Signature where
  Params := Unit
  State _ := QubitMatrix
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := QubitMatrix → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ X Y => X ≠ Y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : QubitMatrix,
    R.readout () () X
      ((Matrix.trace X / 2) • (1 : QubitMatrix) +
        ∑ b : Fin 3, (Matrix.trace (pauli b * X) / 2) • pauli b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (Qubit.pauli_expansion 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : QubitMatrix), (1 : QubitMatrix), ?_⟩
  intro he
  have hbad : (1 : QubitMatrix) = 0 := Eq.mp (congrFun he 0) rfl
  have hentry := congrArg (fun X : QubitMatrix => X 0 0) hbad
  norm_num at hentry

def source_registration : Registration arena (type_of% @Qubit.pauli_expansion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Qubit.pauli_expansion, rejected, rejected_law⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j hj => (hj (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Qubit.pauli_expansion) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliExpansion.unit
  realizationName :=
    `Reg.D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliExpansion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.ChannelTimeReversalNoGo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end PauliExpansion

namespace QubitUnitalJApply

abbrev signature : Signature where
  Params := Unit
  State _ := QubitMatrix
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := QubitMatrix → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => QubitUnital.J X = Y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : QubitMatrix,
    R.readout () () X (Matrix.trace X • (1 : QubitMatrix) - X)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : QubitMatrix), (1 : QubitMatrix), ?_⟩
  intro he
  have hzero : QubitUnital.J (0 : QubitMatrix) = 0 := by
    rw [QubitUnital.J_apply]
    simp
  have hbad := Eq.mp (congrFun he 0) hzero
  have hentry := congrArg (fun X : QubitMatrix => X 0 0) hbad
  norm_num [QubitUnital.J_apply, Matrix.trace, Matrix.diag] at hentry

def source_registration : Registration arena (type_of% @QubitUnital.J_apply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@QubitUnital.J_apply, rejected, rejected_law⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j hj => (hj (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QubitUnital.J_apply) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumChannels.ChannelTimeReversalNoGo.QubitUnitalJApply.unit
  realizationName :=
    `Reg.D5.S3.QuantumChannels.ChannelTimeReversalNoGo.QubitUnitalJApply.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ X Y => QubitUnital.J X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.ChannelTimeReversalNoGo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end QubitUnitalJApply

namespace PauliChannelsSigmaTrace

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 3 ⊕ Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => match s with
    | Sum.inl a => Matrix.trace (pauli a)
    | Sum.inr b => if b then 1 else 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : Fin 3, R.readout () () (Sum.inl a) = 0

private theorem bridge :
    (type_of% @PauliChannels.sigma_trace) ↔ arena.Law actual := by
  constructor
  · intro h a
    simpa [actual, realize] using h a
  · intro h a
    simpa [actual, realize] using h a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  simp [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), Sum.inr false, Sum.inr true, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @PauliChannels.sigma_trace) where
  actual := actual
  bridge := bridge
  variation := ⟨@PauliChannels.sigma_trace, rejected, rejected_law⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j hj => (hj (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@PauliChannels.sigma_trace) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannelsSigmaTrace.unit
  realizationName :=
    `Reg.D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannelsSigmaTrace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.ChannelTimeReversalNoGo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end PauliChannelsSigmaTrace

end
end Reg.D5.S3.QuantumChannels.ChannelTimeReversalNoGo
