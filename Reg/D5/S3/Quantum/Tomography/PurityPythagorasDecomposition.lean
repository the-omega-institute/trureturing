import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
open _root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.checkUnivs false
noncomputable section

open _root_.D5.S3.Observer.Conditioning
open _root_.D5.S3.Quantum.Tomography.RankOneContextCommutator
open _root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection

private def oneContext : RankOneContext 1 where
  projector := fun _ => 1
  rankOne := by
    intro j
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro X
    ext i k
    fin_cases i
    fin_cases k
    simp [Matrix.trace, Matrix.mul_apply]
  resolvesIdentity := by simp

private theorem oneContext_record : IsRecordMeasurement oneContext.projector := by
  refine ⟨?_, ?_, ?_, oneContext.resolvesIdentity⟩
  · intro j
    simp [oneContext]
  · intro j
    simp [oneContext]
  · intro j k hjk
    exact (hjk (Subsingleton.elim _ _)).elim

attribute [local instance]
  _root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup
  _root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace
  _root_.D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixRealInnerProductSpace
universe u_1

namespace InnerTrace

abbrev signature : Signature where
  Params := ℕ
  State p := Matrix (Fin p) (Fin p) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (A C : Matrix (Fin d) (Fin d) ℂ),
    inner ℂ A C = R.readout () d (Aᴴ * C)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (d := 1) 0 0
  simp [rejected, realize] at he

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.matrix_inner_eq_trace_conjTranspose_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.matrix_inner_eq_trace_conjTranspose_mul), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.matrix_inner_eq_trace_conjTranspose_mul) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.InnerTrace.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.InnerTrace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end InnerTrace

namespace RealTrace

abbrev signature : Signature where
  Params := ℕ
  State p := Matrix (Fin p) (Fin p) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (A C : Matrix (Fin d) (Fin d) ℂ)
    (_hA : A.IsHermitian) (_hC : C.IsHermitian),
    R.readout () d (A * C) = ((Matrix.trace (A * C)).re : ℂ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (d := 1) 0 0 (by simp) (by simp)
  simp [rejected, realize] at he

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.RealTrace.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.RealTrace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end RealTrace

namespace CenteredNorm

abbrev signature : Signature where
  Params := ℕ
  State p := Matrix (Fin p) (Fin p) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] (H : Matrix (Fin d) (Fin d) ℂ) (_hH : H.IsHermitian),
    ‖H - (H.trace / (d : ℂ)) • 1‖ ^ 2 =
      (R.readout () d (H * H)).re - (H.trace.re) ^ 2 / (d : ℝ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (d := 1) 0 (by simp)
  norm_num [rejected, realize] at he

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.centered_hermitian_norm_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.centered_hermitian_norm_sq), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.centered_hermitian_norm_sq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.CenteredNorm.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.CenteredNorm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end CenteredNorm

namespace MeasurementNorm

abbrev signature : Signature where
  Params := ℕ
  State p := Matrix (Fin p) (Fin p) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] (context : RankOneContext d)
    (hRecord : IsRecordMeasurement context.projector) (X : traceZeroHermitian d),
    ‖(traceZeroBasisMeasurement context hRecord X).1.1‖ ^ 2 =
      ∑ j, ((R.readout () d (X.1.1 * context.projector j)).re) ^ 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h oneContext oneContext_record 0
  norm_num [rejected, realize] at he

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.traceZero_measurement_norm_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.traceZero_measurement_norm_sq), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.traceZero_measurement_norm_sq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.MeasurementNorm.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.MeasurementNorm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end MeasurementNorm

namespace Pythagoras

abbrev signature : Signature where
  Params := Σ d : ℕ, traceZeroHermitian d
  State p := traceZeroHermitian p.1 → Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p residual => residual p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} [NeZero d] {L : Type u_1} [Fintype L]
    (context : L → RankOneContext d)
    (hRecord : ∀ l, IsRecordMeasurement (context l).projector)
    (_hOrtho : PairwiseOrthogonalMeasurements context hRecord) (state : traceZeroHermitian d),
    ‖state.1.1‖ ^ 2 =
      (∑ l, ‖(traceZeroBasisMeasurement (context l) (hRecord l) state).1.1‖ ^ 2) +
        ‖R.readout () ⟨d, state⟩ (residualVector context hRecord)‖ ^ 2

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  let context : ULift.{u_1} Empty → RankOneContext 1 := fun l => nomatch l.down
  let hRecord : ∀ l, IsRecordMeasurement (context l).projector := fun l => nomatch l.down
  have hOrtho : PairwiseOrthogonalMeasurements context hRecord := by
    intro l
    exact nomatch l.down
  have he := h context hRecord hOrtho 0
  have hne : ‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr one_ne_zero
  simp only [rejected, realize, map_zero, Submodule.coe_zero, norm_zero, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Finset.sum_const_zero, zero_add] at he
  exact hne (sq_eq_zero_iff.mp he.symm)

def source_registration : Registration arena.{u_1} (type_of% @_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.traceZero_context_pythagoras.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.{u_1}.Law actual from (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.traceZero_context_pythagoras.{u_1}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have he := congrArg (fun M => M 0 0) h
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.traceZero_context_pythagoras.{u_1}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.Pythagoras.unit
  realizationName := `Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.Pythagoras.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p residual => residual p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
    definition := none
    coordinates := #[0, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Pythagoras

end
end Reg.D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
