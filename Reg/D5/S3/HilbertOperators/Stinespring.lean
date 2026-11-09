import D5.S3.HilbertOperators.Stinespring
import Mathlib.Analysis.InnerProductSpace.PiL2
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.HilbertOperators.Stinespring
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder InnerProductSpace

noncomputable section
universe u
namespace Reg.D5.S3.HilbertOperators.Stinespring

structure Scope where
  H : Type u
  K : Type u
  [addH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℂ H]
  [completeH : CompleteSpace H]
  [addK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]

attribute [instance] Scope.addH Scope.innerH Scope.completeH Scope.addK Scope.innerK Scope.completeK

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.H →L[ℂ] p.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.K →L[ℂ] p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ V => V.adjoint) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A H : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)),
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      ∀ (a : A) (x : H), φ a x = (R.readout () ⟨H, K⟩ V) (π a (V x))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  let φ : (E →L[ℂ] E) →CP (E →L[ℂ] E) :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.id ℂ (E →L[ℂ] E))
  obtain ⟨K, nK, iK, cK, π, V, hx⟩ := h φ
  letI := nK
  letI := iK
  letI := cK
  have hz := hx 1 (WithLp.toLp 2 (fun _ => (1 : ℂ)))
  change (WithLp.toLp 2 (fun _ : ULift.{u} Unit => (1 : ℂ)) : E) = 0 at hz
  have hc := congrArg (fun z : E => z (ULift.up ())) hz
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

def family : Registration arena.{u} (type_of% (@stinespring_dilation.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@stinespring_dilation.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stinespring_dilation.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.Stinespring.unit
  realizationName := `Reg.D5.S3.HilbertOperators.Stinespring.family
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
    owner := `D5.S3.HilbertOperators.Stinespring
    definition := none
    coordinates := #[1,9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.HilbertOperators.Stinespring
