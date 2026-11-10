import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PowerSeries.ScalarComposition
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.PowerSeries.ScalarComposition
universe u v

abbrev signature : Signature where
  Params := Σ K : Type u, Field K
  State p := PowerSeries p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PowerSeries p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ P => P) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => by letI := p.2; exact 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {K : Type u} (E : Type v) [fK : Field K] [Ring E] [Algebra K E]
    [TopologicalSpace E] [IsTopologicalRing E] (P Q : PowerSeries K)
    (_ : PowerSeries.HasSubst P),
    PowerSeries.toFMS E (PowerSeries.subst (R.readout () ⟨K, fK⟩ P) Q) =
      FormalMultilinearSeries.comp (PowerSeries.toFMS E Q) (PowerSeries.toFMS E P)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let K := ULift.{u} ℚ
  let E := ULift.{v} ℚ
  letI : Algebra K E := (RingHom.ulift (RingHom.id ℚ)).toAlgebra
  letI : TopologicalSpace E := ⊥
  letI : DiscreteTopology E := ⟨rfl⟩
  have hX : PowerSeries.HasSubst (PowerSeries.X : PowerSeries K) := .X'
  have hh := h E (PowerSeries.X : PowerSeries K) PowerSeries.X hX
  rw [← PowerSeries.toFMS_subst E _ _ hX, PowerSeries.X_subst] at hh
  have hn := congrArg (fun p : FormalMultilinearSeries K E E => p 1 (fun _ => 1)) hh
  simpa [rejected, realize, PowerSeries.toFMS, PowerSeries.subst_X,
    PowerSeries.HasSubst.of_constantCoeff_zero' (R := K) (by simp)] using hn

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℚ, inferInstance⟩, 0, 1, ?_⟩
  simp [actual, realize]

def family : Registration arena.{u,v} (type_of% @PowerSeries.toFMS_subst.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@PowerSeries.toFMS_subst, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PowerSeries.toFMS_subst.{u,v}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName := `Reg.D5.S3.Analytic.PowerSeries.ScalarComposition.unit
  realizationName := `Reg.D5.S3.Analytic.PowerSeries.ScalarComposition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some PowerSeries
  sourceSelection := some {
    owner := `D5.S3.Analytic.PowerSeries.ScalarComposition
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.PowerSeries.ScalarComposition
