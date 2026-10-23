import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ComplexOrder

namespace Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev BlochVector := EuclideanSpace ℝ (Fin 3)

def unitX : BlochVector := WithLp.toLp 2 ![1, 0, 0]

/-- The canonical matrix is observed over the full Bloch vector space at each trace. -/
abbrev matrixSignature : Signature where
  Params := ℝ
  State _ := BlochVector
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := QubitMatrix
  Anchor := Empty
  finiteAnchor := inferInstance

def matrixActual : Realization matrixSignature :=
  realize matrixSignature (fun _ a r => blochMatrix a r) (fun e => nomatch e)

def matrixRejected : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem matrixDependence : ObservationalDependence matrixSignature matrixActual := by
  intro i
  refine ⟨0, 0, unitX, ?_⟩
  intro h
  have hh := congrArg bloch h
  change bloch (blochMatrix 0 0) = bloch (blochMatrix 0 unitX) at hh
  rw [bloch_blochMatrix, bloch_blochMatrix] at hh
  have hx := congrArg (fun r : BlochVector => r 0) hh
  norm_num [unitX] at hx

abbrev traceArena : Arena where
  signature := matrixSignature
  Law R := ∀ (a : ℝ) (r : BlochVector), Matrix.trace (R.readout () a r) = (a : ℂ)

theorem traceRejectedLaw : ¬ traceArena.Law matrixRejected := by
  intro h
  have hh := h 1 0
  change Matrix.trace (0 : QubitMatrix) = (1 : ℂ) at hh
  simp at hh

def traceProof : Registration traceArena (traceArena.Law matrixActual) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨blochMatrix_trace, matrixRejected, traceRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨matrixRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, traceRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := matrixDependence

abbrev recoveryArena : Arena where
  signature := matrixSignature
  Law R := ∀ (a : ℝ) (r : BlochVector), bloch (R.readout () a r) = r

theorem recoveryRejectedLaw : ¬ recoveryArena.Law matrixRejected := by
  intro h
  have hh := congrArg (fun r : BlochVector => r 0) (h 0 unitX)
  change (bloch (0 : QubitMatrix)) 0 = unitX 0 at hh
  norm_num [bloch, unitX] at hh

def recoveryProof : Registration recoveryArena (recoveryArena.Law matrixActual) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨bloch_blochMatrix, matrixRejected, recoveryRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨matrixRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, recoveryRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := matrixDependence

abbrev geometrySignature : Signature where
  Params := Unit
  State _ := QubitMatrix
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := QubitMatrix
  Anchor := Empty
  finiteAnchor := inferInstance

def geometryActual : Realization geometrySignature :=
  realize geometrySignature (fun _ _ M => blochMatrix (Matrix.trace M).re (bloch M))
    (fun e => nomatch e)

def geometryRejected : Realization geometrySignature :=
  realize geometrySignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Both conclusions and all hypotheses of the original geometry theorem remain in the law. -/
abbrev geometryArena : Arena where
  signature := geometrySignature
  Law R := ∀ (M : QubitMatrix) (_hM : M.IsHermitian),
    M = R.readout () () M ∧
    (Matrix.trace M = 1 → M * M = M → ‖bloch M‖ = 1)

theorem geometryRejectedLaw : ¬ geometryArena.Law geometryRejected := by
  intro h
  have hh := congrArg (fun M : QubitMatrix => M 0 0)
    (h 1 Matrix.isHermitian_one).1
  change (1 : ℂ) = 0 at hh
  exact one_ne_zero hh

theorem geometryDependence : ObservationalDependence geometrySignature geometryActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrArg Matrix.trace h
  change Matrix.trace (blochMatrix (Matrix.trace (0 : QubitMatrix)).re (bloch 0)) =
    Matrix.trace (blochMatrix (Matrix.trace (1 : QubitMatrix)).re (bloch 1)) at hh
  rw [blochMatrix_trace, blochMatrix_trace] at hh
  norm_num [Matrix.trace, Fin.sum_univ_two] at hh

def geometryProof : Registration geometryArena (geometryArena.Law geometryActual) where
  actual := geometryActual
  bridge := Iff.rfl
  variation := ⟨bloch_geometry_of_isHermitian, geometryRejected, geometryRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨geometryRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, geometryRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := geometryDependence

abbrev boundSignature : Signature where
  Params := Unit
  State _ := QubitMatrix
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def boundActual : Realization boundSignature :=
  realize boundSignature (fun _ _ M => (Matrix.trace M).re) (fun e => nomatch e)

def boundRejected : Realization boundSignature :=
  realize boundSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev boundArena : Arena where
  signature := boundSignature
  Law R := ∀ (M : QubitMatrix) (_hM : M.PosSemidef), ‖bloch M‖ ≤ R.readout () () M

theorem boundRejectedLaw : ¬ boundArena.Law boundRejected := by
  intro h
  have hh := h 0 Matrix.PosSemidef.zero
  change ‖bloch (0 : QubitMatrix)‖ ≤ (-1 : ℝ) at hh
  exact (not_le_of_gt (by linarith [norm_nonneg (bloch (0 : QubitMatrix))])) hh

theorem boundDependence : ObservationalDependence boundSignature boundActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (Matrix.trace (0 : QubitMatrix)).re ≠ (Matrix.trace (1 : QubitMatrix)).re
  norm_num [Matrix.trace, Fin.sum_univ_two]

def boundProof : Registration boundArena (boundArena.Law boundActual) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨norm_bloch_le_trace_of_posSemidef, boundRejected, boundRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨boundRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, boundRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := boundDependence

noncomputable def traceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@blochMatrix_trace)
    (type_of% (realize matrixSignature matrixActual.readout matrixActual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry.traceUnit,
  realizationName := `Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry.traceProof,
  realizationSource := none, generated := false,
  arena := .source ⟨traceArena⟩, objectArena := .source ⟨traceArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source traceArena ⟨traceProof⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize matrixSignature matrixActual.readout matrixActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ActualPureQubitGeometry, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def recoveryRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bloch_blochMatrix)
    (type_of% (realize matrixSignature matrixActual.readout matrixActual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry.recoveryUnit,
  realizationName := `Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry.recoveryProof,
  realizationSource := none, generated := false,
  arena := .source ⟨recoveryArena⟩, objectArena := .source ⟨recoveryArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source recoveryArena ⟨recoveryProof⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize matrixSignature matrixActual.readout matrixActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ActualPureQubitGeometry, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def geometryRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bloch_geometry_of_isHermitian)
    (type_of% (realize geometrySignature geometryActual.readout geometryActual.anchor))
    Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry.geometryUnit,
  realizationName := `Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry.geometryProof,
  realizationSource := none, generated := false,
  arena := .source ⟨geometryArena⟩, objectArena := .source ⟨geometryArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source geometryArena ⟨geometryProof⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize geometrySignature geometryActual.readout geometryActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ActualPureQubitGeometry, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def boundRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_bloch_le_trace_of_posSemidef)
    (type_of% (realize boundSignature boundActual.readout boundActual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry.boundUnit,
  realizationName := `Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry.boundProof,
  realizationSource := none, generated := false,
  arena := .source ⟨boundArena⟩, objectArena := .source ⟨boundArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source boundArena ⟨boundProof⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize boundSignature boundActual.readout boundActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ActualPureQubitGeometry, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms traceRegistration
#print axioms recoveryRegistration
#print axioms geometryRegistration
#print axioms boundRegistration

end
end Reg.D5.S3.Quantum.Information.ActualPureQubitGeometry
