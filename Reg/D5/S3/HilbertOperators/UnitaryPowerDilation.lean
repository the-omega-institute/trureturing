import D5.S3.HilbertOperators.UnitaryPowerDilation
import Mathlib.Analysis.InnerProductSpace.PiL2
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.HilbertOperators.UnitaryPowerDilation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped InnerProductSpace

noncomputable section
universe u
namespace Reg.D5.S3.HilbertOperators.UnitaryPowerDilation

structure Scope where
  E : Type u
  H : Type u
  [addE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℂ E]
  [completeE : CompleteSpace E]
  [addH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℂ H]
  [completeH : CompleteSpace H]

attribute [instance] Scope.addE Scope.innerE Scope.completeE Scope.addH Scope.innerH Scope.completeH

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.E →L[ℂ] p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.H →L[ℂ] p.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ V => V.adjoint) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1),
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
      (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      U ∈ unitary (H →L[ℂ] H) ∧
      (∀ (n : ℕ) (x : E), (R.readout () ⟨E, H⟩ V) ((U ^ n) (V x)) = (T ^ n) x)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨H, nH, iH, cH, V, U, hV, hU, hpow⟩ :=
    h (ContinuousLinearMap.id ℂ E) (by simp)
  letI := nH
  letI := iH
  letI := cH
  have hz := hpow 0 (WithLp.toLp 2 (fun _ => (1 : ℂ)))
  have hz' : (0 : E) = WithLp.toLp 2 (fun _ : ULift.{u} Unit => (1 : ℂ)) := by
    simpa [rejected, realize] using hz
  have hc := congrArg (fun z : E => z (ULift.up ())) hz'
  simp at hc

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  let p : Scope.{u} := ⟨E, E⟩
  refine ⟨p, 0, ContinuousLinearMap.id ℂ E, ?_⟩
  intro he
  have hc := congrArg (fun T : E →L[ℂ] E =>
    (T (WithLp.toLp 2 (fun _ => (1 : ℂ)))) (ULift.up ())) he
  simp [actual, realize, p, ContinuousLinearMap.adjoint_id] at hc

def family : Registration arena.{u} (type_of% (@exists_unitary_power_dilation.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_unitary_power_dilation.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_unitary_power_dilation.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.UnitaryPowerDilation.unit
  realizationName := `Reg.D5.S3.HilbertOperators.UnitaryPowerDilation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ V => V.adjoint) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HilbertOperators.UnitaryPowerDilation
    definition := none
    coordinates := #[0,6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.HilbertOperators.UnitaryPowerDilation
