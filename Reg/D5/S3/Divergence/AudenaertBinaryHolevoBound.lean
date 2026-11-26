import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Divergence.AudenaertBinaryHolevoBound

noncomputable section
open Matrix
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.Divergence.LogDerivTrace
open _root_.D5.S3.Divergence.AudenaertBinaryHolevoBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Divergence.AudenaertBinaryHolevoBound

abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature
  ℕ (fun n => Matrix (Fin n) (Fin n) ℂ) (fun n => Matrix (Fin n) (Fin n) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (m X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ),
    R.readout () n (logDeriv m (c • X)) (c • logDeriv m X)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := 0) 0 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : Matrix (Fin 1) (Fin 1) ℂ)
  change ((0 : Matrix (Fin 1) (Fin 1) ℂ) = 0) = (1 = 0) at hh
  have bad : (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := hh ▸ rfl
  exact one_ne_zero bad

def family : Registration arena (type_of% @logDeriv_smul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@logDeriv_smul, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@logDeriv_smul) (Realization signature) Unit Unit where
  unitName := `D5.S3.Divergence.AudenaertBinaryHolevoBound.logDeriv_smul.__information_unit
  realizationName := `Reg.D5.S3.Divergence.AudenaertBinaryHolevoBound.family
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
  sourceSelection := some {
    owner := `D5.S3.Divergence.AudenaertBinaryHolevoBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Divergence.AudenaertBinaryHolevoBound
