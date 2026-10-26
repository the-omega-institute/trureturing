import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import Reg.Support.SingleDependentReadout

/-! Owning-mirror registration attempt. It observes each actual conclusion with the
complete original source telescope. No binding certificate is claimed.
Existing certificate boundaries are tracked in https://github.com/the-omega-institute/trureturing/issues/22313.
Source selection is left absent pending the actual compiled source-binding report. -/

noncomputable section
universe u v
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
open _root_.D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
open _root_.D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (entryNormSq)

namespace EntrySquares

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ),
    R.readout () () (entryNormSq A) (‖A‖ ^ 2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u} (type_of% @entryNormSq_eq_hs_sq.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entryNormSq_eq_hs_sq.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@entryNormSq_eq_hs_sq.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.EntrySquares.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end EntrySquares

namespace TraceGram

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    (C R₀ N : Matrix d d ℂ) (_hR : R₀.PosSemidef)
    (_htrR : R₀.trace = 1) (_htrN : N.trace = 1) (_hCN : C * Cᴴ ≤ N),
    R.readout () () (traceNorm (N - R₀)) (4 * ‖C - CFC.sqrt R₀‖)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let d := ULift.{u} Unit
  have h1 : (1 : Matrix d d ℂ).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix d d ℂ)
  exact @h d inferInstance inferInstance 0 1 1 h1
    (by simp [Matrix.trace, Matrix.diag]) (by simp [Matrix.trace, Matrix.diag])
    (by simpa using h1.nonneg)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u} (type_of% @traceNorm_sub_le_four_hs_sqrt.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_sub_le_four_hs_sqrt.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@traceNorm_sub_le_four_hs_sqrt.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.traceNorm_sub_le_four_hs_sqrt.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.TraceGram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end TraceGram

end Reg.D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
