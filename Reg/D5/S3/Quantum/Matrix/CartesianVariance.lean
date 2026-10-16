import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.CartesianVariance
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Matrix.CartesianVariance
open _root_.D5.S3.Quantum.Matrix.CartesianVariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Matrix
open scoped BigOperators ComplexInnerProductSpace ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.checkUnivs false
noncomputable section

abbrev sumSignature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n) (Fin n) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def sumActual : Realization sumSignature :=
  realize sumSignature (fun _ _ M => M) (fun e => nomatch e)

def sumRejected : Realization sumSignature :=
  realize sumSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sumArena : Arena where
  signature := sumSignature
  Law R := ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian),
    R.readout () n M = ∑ i, hM.eigenvalues i •
      (Matrix.vecMulVec (WithLp.ofLp (hM.eigenvectorBasis i))
        (star (WithLp.ofLp (hM.eigenvectorBasis i))))

theorem sumActualLaw : sumArena.Law sumActual := by
  intro n M hM
  exact _root_.D5.S3.Quantum.Matrix.CartesianVariance.hermitian_spectral_sum M hM

theorem sumRejectedLaw : ¬ sumArena.Law sumRejected := by
  intro h
  have he := h (1 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_one
  rw [← _root_.D5.S3.Quantum.Matrix.CartesianVariance.hermitian_spectral_sum
    (1 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_one] at he
  change (0 : Matrix (Fin 1) (Fin 1) ℂ) = 1 at he
  have he' := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) he
  simp at he'

theorem sumDependence : ObservationalDependence sumSignature sumActual := by
  intro i
  cases i
  refine ⟨1, 0, 1, ?_⟩
  exact zero_ne_one

def sumSourceRegistration : Registration sumArena
    (type_of% @_root_.D5.S3.Quantum.Matrix.CartesianVariance.hermitian_spectral_sum) where
  actual := sumActual
  bridge := Iff.rfl
  variation := ⟨sumActualLaw, sumRejected, sumRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sumRejected, ?_, rfl, sumRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := sumDependence

noncomputable def hermitianSpectralSumRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.CartesianVariance.hermitian_spectral_sum)
      (Realization sumSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CartesianVariance.hermitianSpectralSumUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CartesianVariance.sumSourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sumArena⟩
  objectArena := .source ⟨sumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sumArena ⟨sumSourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sumSignature (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CartesianVariance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev traceSignature : Signature where
  Params := Σ n : ℕ, Matrix (Fin n) (Fin n) ℂ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _p := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature :=
  realize traceSignature
    (fun _ p M => Matrix.trace (p.2 * M))
    (fun e => nomatch e)

def traceRejected : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev traceArena : Arena where
  signature := traceSignature
  Law R := ∀ {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.IsHermitian),
      R.readout () ⟨n, ρ⟩ A = ∑ i, hρ.eigenvalues i •
        inner ℂ (hρ.eigenvectorBasis i) (Matrix.toEuclideanLin A (hρ.eigenvectorBasis i))

theorem traceActualLaw : traceArena.Law traceActual := by
  intro n ρ A hρ
  exact _root_.D5.S3.Quantum.Matrix.CartesianVariance.hermitian_trace_spectral ρ A hρ

theorem traceRejectedLaw : ¬ traceArena.Law traceRejected := by
  intro h
  have he := h (1 : Matrix (Fin 1) (Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)
    Matrix.isHermitian_one
  rw [← _root_.D5.S3.Quantum.Matrix.CartesianVariance.hermitian_trace_spectral
    (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 Matrix.isHermitian_one] at he
  change (0 : ℂ) = Matrix.trace (1 * 1) at he
  have hz : (0 : ℂ) = 1 := by simpa using he
  exact zero_ne_one hz

theorem traceDependence : ObservationalDependence traceSignature traceActual := by
  intro i
  cases i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  intro he
  norm_num [traceActual, realize, Matrix.trace] at he

def traceSourceRegistration : Registration traceArena
    (type_of% @_root_.D5.S3.Quantum.Matrix.CartesianVariance.hermitian_trace_spectral) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨traceActualLaw, traceRejected, traceRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨traceRejected, ?_, rfl, traceRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := traceDependence

noncomputable def hermitianTraceSpectralRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.CartesianVariance.hermitian_trace_spectral)
      (Realization traceSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.CartesianVariance.hermitianTraceSpectralUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.CartesianVariance.traceSourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena⟩
  objectArena := .source ⟨traceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena ⟨traceSourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature
    (fun _ p M => Matrix.trace (p.2 * M)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.CartesianVariance
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sumSourceRegistration
#print axioms hermitianSpectralSumRegistration
#print axioms traceSourceRegistration
#print axioms hermitianTraceSpectralRegistration

end
end Reg.D5.S3.Quantum.Matrix.CartesianVariance
