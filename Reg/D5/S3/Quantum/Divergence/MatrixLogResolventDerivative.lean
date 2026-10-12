import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
open LeanInformationAudit

set_option quotPrecheck false
noncomputable section
namespace Reg.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
universe u

abbrev weightSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
abbrev domainSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => Set ℝ)
abbrev traceSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ t => 1-t) (fun e => nomatch e)
def weightRejected : Realization weightSignature :=
  realize weightSignature (fun _ _ t => -t) (fun e => nomatch e)
def domainActual : Realization domainSignature :=
  realize domainSignature (fun _ _ t => Ioi t) (fun e => nomatch e)
def domainRejected : Realization domainSignature :=
  realize domainSignature (fun _ _ _ => ∅) (fun e => nomatch e)
def traceActual : Realization traceSignature :=
  realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e)
def traceRejected : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => -1) (fun e => nomatch e)

variable {n : Type u} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "S" => ↥(selfAdjoint.submodule ℝ M)
local notation "ι" => (selfAdjoint.submodule ℝ M).subtypeL
local notation "B" => fun (A : M) (t : ℝ) => (1-t) • (1 : M) + t • A
local notation "L" => fun (A : S) (t : ℝ) =>
  (ContinuousLinearMap.mulLeftRight ℝ M (Ring.inverse (B A.val t))
    (Ring.inverse (B A.val t))).comp ι

def pathKernel (R : Realization weightSignature) (A : S) (t : ℝ) : S →L[ℝ] M :=
  (ContinuousLinearMap.mulLeftRight ℝ M
    (Ring.inverse (R.readout () () t • (1 : M) + t • A.val))
    (Ring.inverse (B A.val t))).comp ι

def resolventKernel (A : S) (t : ℝ) : S →L[ℝ] M :=
  (ContinuousLinearMap.mulLeftRight ℝ M (Ring.inverse (A.val + t • (1 : M)))
    (Ring.inverse (A.val + t • (1 : M)))).comp ι

def traceEntropy (R : Realization traceSignature) (Y : S) : ℝ :=
  R.readout () () (Y.val * CFC.log Y.val).trace

def gradientLinear : M →L[ℝ] (S →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ S M ℝ
    (Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap)).comp
      ((ContinuousLinearMap.mul ℝ M).precompL S ι)

/-- The first inverse's affine weight varies; the second inverse remains source-fixed. -/
def pathArena : Arena where
  signature := weightSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) (_hA : A.val.PosDef),
    HasFDerivAt (fun Y : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) => CFC.log Y.val)
      (∫ t in (0 : ℝ)..1, pathKernel R A t) A

/-- The derivative integral's half-line varies; integrability and action remain source-fixed. -/
def resolventArena : Arena where
  signature := domainSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) (_hA : A.val.PosDef),
    HasFDerivAt (fun Y : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) => CFC.log Y.val)
      (∫ t in R.readout () () 0, resolventKernel A t) A ∧
    IntegrableOn (resolventKernel A) (Ioi (0 : ℝ)) ∧
    ∀ H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)),
      (∫ t in Ioi (0 : ℝ), resolventKernel A t) H =
        _root_.D5.S3.Divergence.LogDerivTrace.logDeriv A.val H.val

/-- Only the explicit trace pairing varies; both actual entropy derivatives remain fixed. -/
def hessianArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) (_hA : A.val.PosDef),
    HasFDerivAt (fderiv ℝ (traceEntropy traceActual))
      (gradientLinear.comp (∫ t in Ioi (0 : ℝ), resolventKernel A t)) A ∧
    (∀ H J : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)),
      (fderiv ℝ (fderiv ℝ (traceEntropy traceActual)) A) H J =
        R.readout () ()
          (J.val * _root_.D5.S3.Divergence.LogDerivTrace.logDeriv A.val H.val).trace) ∧
    ∀ H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)),
      0 ≤ (fderiv ℝ (fderiv ℝ (traceEntropy traceActual)) A) H H

theorem actual_path_law : pathArena.{u}.Law weightActual := @matrix_log_hasFDerivAt_path.{u}
theorem actual_resolvent_law : resolventArena.{u}.Law domainActual :=
  @matrix_log_hasFDerivAt_resolvent.{u}
theorem actual_hessian_law : hessianArena.{u}.Law traceActual :=
  @trace_entropy_hessian_resolvent.{u}

/-- At the identity the path derivative is the inclusion of the Hermitian space. -/
theorem log_identity_derivative :
    HasFDerivAt (fun Y : S => CFC.log Y.val) ι
      (⟨1, IsSelfAdjoint.one _⟩ : S) := by
  have hd := matrix_log_hasFDerivAt_path (⟨1, IsSelfAdjoint.one _⟩ : S) Matrix.PosDef.one
  have he : (fun t : ℝ => L (⟨1, IsSelfAdjoint.one _⟩ : S) t) = fun _ => ι := by
    funext t
    apply ContinuousLinearMap.ext
    intro H
    have hb : B (1 : M) t = 1 := by
      simp only [← add_smul, sub_add_cancel, one_smul]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply, hb,
      Ring.inverse_one]
  simpa only [he, intervalIntegral.integral_const, sub_zero, one_smul] using hd

theorem rejected_path_law : ¬ pathArena.{u}.Law weightRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hh := h A Matrix.PosDef.one
  have hz : (∫ t in (0 : ℝ)..1, pathKernel weightRejected A t) = 0 := by
    have he : (fun t : ℝ => pathKernel weightRejected A t) = fun _ => 0 := by
      funext t
      ext H i j
      simp [pathKernel, weightRejected, realize, A, neg_smul]
    rw [he]
    simp
  rw [hz] at hh
  have he := (log_identity_derivative (n := n)).unique hh
  have hv := congrArg (fun f => f A (⟨0⟩ : n) (⟨0⟩ : n)) he
  norm_num [A] at hv

theorem rejected_resolvent_law : ¬ resolventArena.{u}.Law domainRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hh := (h A Matrix.PosDef.one).1
  have hh' : HasFDerivAt (fun Y : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) =>
      CFC.log Y.val)
      (0 : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) →L[ℝ] Matrix n n ℂ) A := by
    simpa [domainRejected, realize] using hh
  have he := (log_identity_derivative (n := n)).unique hh'
  have hv := congrArg (fun f => f A (⟨0⟩ : n) (⟨0⟩ : n)) he
  norm_num [A] at hv

theorem rejected_hessian_law : ¬ hessianArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hh := (h A Matrix.PosDef.one).2.1 0 0
  simp [traceRejected, realize] at hh

theorem weight_dependence : ObservationalDependence weightSignature weightActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [weightActual, realize]

theorem domain_dependence : ObservationalDependence domainSignature domainActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change Ioi (0 : ℝ) ≠ Ioi (1 : ℝ)
  intro h
  have hm : (1 : ℝ) ∈ Ioi (0 : ℝ) := by norm_num
  rw [h] at hm
  exact lt_irrefl (1 : ℝ) hm

theorem trace_dependence : ObservationalDependence traceSignature traceActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [traceActual, realize]

def pathEvidence : Registration pathArena.{u} (type_of% @matrix_log_hasFDerivAt_path.{u}) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨actual_path_law, weightRejected, rejected_path_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    pathArena.Law weightActual weightRejected rejected_path_law
  dependence := weight_dependence

def resolventEvidence : Registration resolventArena.{u}
    (type_of% @matrix_log_hasFDerivAt_resolvent.{u}) where
  actual := domainActual
  bridge := Iff.rfl
  variation := ⟨actual_resolvent_law, domainRejected, rejected_resolvent_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    resolventArena.Law domainActual domainRejected rejected_resolvent_law
  dependence := domain_dependence

def hessianEvidence : Registration hessianArena.{u}
    (type_of% @trace_entropy_hessian_resolvent.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_hessian_law, traceRejected, rejected_hessian_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    hessianArena.Law traceActual traceRejected rejected_hessian_law
  dependence := trace_dependence

/-- Source-bound four-slot candidate for the complete path theorem. -/
def pathRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative.matrix_log_hasFDerivAt_path.{u})
      (type_of% (realize weightSignature (fun _ _ t => 1-t) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.MatrixLogResolventDerivative.matrix_log_hasFDerivAt_path.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative.pathEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨pathArena.{u}⟩
  objectArena := .source ⟨pathArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pathArena.{u} ⟨pathEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ t => 1-t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "fn", "arg", "fn",
        "fn", "fn", "arg", "body", "fn", "fn", "body", "body",
        "fn", "arg", "fn", "arg", "arg", "fn", "fn", "body",
        "body", "arg", "fn", "fn", "body", "body", "fn", "arg",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Source-bound four-slot candidate for the complete resolvent theorem. -/
def resolventRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative.matrix_log_hasFDerivAt_resolvent.{u})
      (type_of% (realize domainSignature (fun _ _ t => Ioi t) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.MatrixLogResolventDerivative.matrix_log_hasFDerivAt_resolvent.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative.resolventEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨resolventArena.{u}⟩
  objectArena := .source ⟨resolventArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source resolventArena.{u} ⟨resolventEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize domainSignature (fun _ _ t => Ioi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "fn", "arg", "fn",
        "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Source-bound four-slot candidate for the complete hessian theorem. -/
def hessianRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative.trace_entropy_hessian_resolvent.{u})
      (type_of% (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.MatrixLogResolventDerivative.trace_entropy_hessian_resolvent.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative.hessianEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨hessianArena.{u}⟩
  objectArena := .source ⟨hessianArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hessianArena.{u} ⟨hessianEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "arg", "fn", "arg",
        "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
