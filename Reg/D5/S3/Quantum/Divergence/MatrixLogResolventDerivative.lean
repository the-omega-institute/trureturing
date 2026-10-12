import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
import Reg.Support.DependentFamily

open MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
open LeanInformationAudit

set_option quotPrecheck false

noncomputable section
namespace Reg.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
universe u

/-- The original matrix index and both of its finite-matrix instances. -/
structure Parameters where
  index : Type u
  finite : Fintype index
  equality : DecidableEq index

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Matrix p.index p.index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.index p.index ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p X => by
    letI := p.finite
    letI := p.equality
    exact Ring.inverse X) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

variable {n : Type u} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "S" => ↥(selfAdjoint.submodule ℝ M)
local notation "ι" => (selfAdjoint.submodule ℝ M).subtypeL
local notation "B" => fun (A : M) (t : ℝ) => (1 - t) • (1 : M) + t • A
local notation "L" => fun (A : S) (t : ℝ) =>
  (ContinuousLinearMap.mulLeftRight ℝ M (Ring.inverse (B A.val t))
    (Ring.inverse (B A.val t))).comp ι
local notation "Rinv" => fun (R : Realization signature) (X : M) =>
  R.readout () ⟨n, inferInstance, inferInstance⟩ X
def pathKernel (R : Realization signature) (A : S) (t : ℝ) : S →L[ℝ] M :=
  (ContinuousLinearMap.mulLeftRight ℝ M (Rinv R (B A.val t))
    (Rinv R (B A.val t))).comp ι

/-- The full original telescope, with only the inverse readout varied. -/
def pathArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) (_hA : A.val.PosDef),
    HasFDerivAt (fun Y : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) => CFC.log Y.val)
      (∫ t in (0 : ℝ)..1, pathKernel R A t) A

theorem actual_path_law : pathArena.{u}.Law actual := @matrix_log_hasFDerivAt_path.{u}

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

theorem rejected_path_law : ¬ pathArena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hh := h A Matrix.PosDef.one
  have hz : (∫ t in (0 : ℝ)..1, pathKernel rejected A t) = 0 := by
    have he : (fun t : ℝ => pathKernel rejected A t) = fun _ => 0 := by
      funext t
      ext H i j
      simp [pathKernel, rejected, realize, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.mulLeftRight_apply]
    rw [he]
    simp
  rw [hz] at hh
  have he := (log_identity_derivative (n := n)).unique hh
  have hv := congrArg (fun f => f A (⟨0⟩ : n) (⟨0⟩ : n)) he
  norm_num [A] at hv

theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let n := ULift.{u} (Fin 1)
  refine ⟨⟨n, inferInstance, inferInstance⟩, 0, 1, ?_⟩
  change Ring.inverse (0 : Matrix n n ℂ) ≠ Ring.inverse (1 : Matrix n n ℂ)
  simp only [Ring.inverse_zero, Ring.inverse_one]
  exact zero_ne_one

def pathEvidence : Registration pathArena.{u} (type_of% @matrix_log_hasFDerivAt_path.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_path_law, rejected, rejected_path_law⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨rejected, ?_, rfl, rejected_path_law⟩
      intro j h
      change Unit at j
      exact (h (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := actual_dependence

def resolventKernel (R : Realization signature) (A : S) (t : ℝ) : S →L[ℝ] M :=
  (ContinuousLinearMap.mulLeftRight ℝ M (Rinv R (A.val + t • (1 : M)))
    (Rinv R (A.val + t • (1 : M)))).comp ι

def resolventArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) (_hA : A.val.PosDef),
    HasFDerivAt (fun Y : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) => CFC.log Y.val)
      (∫ t in Ioi (0 : ℝ), resolventKernel R A t) A ∧
    IntegrableOn (resolventKernel actual A) (Ioi (0 : ℝ)) ∧
    ∀ H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)),
      (∫ t in Ioi (0 : ℝ), resolventKernel actual A t) H =
        _root_.D5.S3.Divergence.LogDerivTrace.logDeriv A.val H.val

theorem actual_resolvent_law : resolventArena.{u}.Law actual :=
  @matrix_log_hasFDerivAt_resolvent.{u}

theorem rejected_resolvent_law : ¬ resolventArena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hh := (h A Matrix.PosDef.one).1
  have hz : (∫ t in Ioi (0 : ℝ), resolventKernel rejected A t) = 0 := by
    have he : (fun t : ℝ => resolventKernel rejected A t) = fun _ => 0 := by
      funext t
      ext H i j
      simp [resolventKernel, rejected, realize]
    rw [he]
    simp
  rw [hz] at hh
  have he := (log_identity_derivative (n := n)).unique hh
  have hv := congrArg (fun f => f A (⟨0⟩ : n) (⟨0⟩ : n)) he
  norm_num [A] at hv

def resolventEvidence : Registration resolventArena.{u}
    (type_of% @matrix_log_hasFDerivAt_resolvent.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_resolvent_law, rejected, rejected_resolvent_law⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨rejected, ?_, rfl, rejected_resolvent_law⟩
      intro j h
      change Unit at j
      exact (h (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := actual_dependence

abbrev traceSignature : Signature where
  Params := Parameters.{u}
  State p := Matrix p.index p.index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature := realize traceSignature
  (fun _ p X => by
    letI := p.finite
    exact X.trace.re) (fun e => nomatch e)

def traceRejected : Realization traceSignature := realize traceSignature
  (fun _ _ _ => -1) (fun e => nomatch e)

def traceEntropy (R : Realization traceSignature) (Y : S) : ℝ :=
  R.readout () ⟨n, inferInstance, inferInstance⟩ (Y.val * CFC.log Y.val)

def gradientLinear : M →L[ℝ] (S →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ S M ℝ
    (Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap)).comp
      ((ContinuousLinearMap.mul ℝ M).precompL S ι)

def hessianArena : Arena where
  signature := traceSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ))) (_hA : A.val.PosDef),
    HasFDerivAt (fderiv ℝ (traceEntropy R))
      (gradientLinear.comp (∫ t in Ioi (0 : ℝ), resolventKernel actual A t)) A ∧
    (∀ H J : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)),
      (fderiv ℝ (fderiv ℝ (traceEntropy R)) A) H J =
        R.readout () ⟨n, inferInstance, inferInstance⟩
          (J.val * _root_.D5.S3.Divergence.LogDerivTrace.logDeriv A.val H.val)) ∧
    ∀ H : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)),
      0 ≤ (fderiv ℝ (fderiv ℝ (traceEntropy R)) A) H H

theorem actual_hessian_law : hessianArena.{u}.Law traceActual :=
  @trace_entropy_hessian_resolvent.{u}

theorem rejected_hessian_law : ¬ hessianArena.{u}.Law traceRejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let A : ↥(selfAdjoint.submodule ℝ (Matrix n n ℂ)) := ⟨1, IsSelfAdjoint.one _⟩
  have hh := (h A Matrix.PosDef.one).2.1 0 0
  have he : traceEntropy (n := n) traceRejected = fun _ => (-1 : ℝ) := rfl
  rw [he] at hh
  simp [traceRejected, realize] at hh

theorem trace_dependence : ObservationalDependence traceSignature.{u} traceActual := by
  intro role
  let n := ULift.{u} (Fin 1)
  refine ⟨⟨n, inferInstance, inferInstance⟩, 0, 1, ?_⟩
  change (0 : Matrix n n ℂ).trace.re ≠ (1 : Matrix n n ℂ).trace.re
  simp [n]

def hessianEvidence : Registration hessianArena.{u}
    (type_of% @trace_entropy_hessian_resolvent.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨actual_hessian_law, traceRejected, rejected_hessian_law⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨traceRejected, ?_, rfl, rejected_hessian_law⟩
      intro j h
      change Unit at j
      exact (h (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := trace_dependence

#print axioms pathEvidence
#print axioms resolventEvidence
#print axioms hessianEvidence
#print axioms matrix_log_hasFDerivAt_path
#print axioms matrix_log_hasFDerivAt_resolvent
#print axioms trace_entropy_hessian_resolvent

end Reg.D5.S3.Quantum.Divergence.MatrixLogResolventDerivative
