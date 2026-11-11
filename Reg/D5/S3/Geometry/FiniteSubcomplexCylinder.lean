import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteSubcomplexCylinder

noncomputable section
open Set
open scoped unitInterval ContinuousMap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteConeCollapse
open _root_.D5.S3.Geometry.FiniteSubcomplexCylinder

namespace Reg.D5.S3.Geometry.FiniteSubcomplexCylinder
universe u

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V
  K : PreAbstractSimplicialComplex V
  L : PreAbstractSimplicialComplex V
  inclusion : L ≤ K

attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Space p.K × I
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Space p.K × I
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p z => (retraction p.K p.L p.inclusion z).val)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ z => (z.1, 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u}, ∀ z : Space p.K × I,
    z.2 = 0 ∨ z.1.val ∈ realization p.L → R.readout () p z = z

private theorem bridge : (type_of% (@retraction_fixed.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p z hz
    exact h p.K p.L p.inclusion z hz
  · intro h V fv dv K L hLK z hz
    exact h ⟨V, fv, dv, K, L, hLK⟩ z hz

private abbrev pointComplex : PreAbstractSimplicialComplex (ULift.{u} Unit) :=
  ⊤

private def point : Space (pointComplex.{u}) :=
  ⟨fun _ => 1, (realization_mem_iff _ _).2
    ⟨{⟨()⟩}, by change ({⟨()⟩} : Finset (ULift.{u} Unit)).Nonempty; simp, by
      constructor
      · intro v; norm_num
      · constructor
        · simp
        · intro v hv
          exact (hv (by have : v = ⟨()⟩ := Subsingleton.elim _ _; simp [this])).elim⟩⟩

private abbrev pointParameters : Parameters.{u} :=
  ⟨ULift.{u} Unit, inferInstance, inferInstance, pointComplex, pointComplex, le_rfl⟩

private theorem point_side (t : I) :
    (point.{u} : Space pointParameters.K).val ∈ realization pointParameters.L :=
  point.property

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h pointParameters (point, 1) (Or.inr (point_side 1))
  have he := congrArg (fun z => (z.2 : ℝ)) hh
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨pointParameters, (point, 0), (point, 1), ?_⟩
  intro h
  have h0 := retraction_fixed pointParameters.K pointParameters.L
    pointParameters.inclusion (point, 0) (Or.inl rfl)
  have h1 := retraction_fixed pointParameters.K pointParameters.L
    pointParameters.inclusion (point, 1) (Or.inr (point_side 1))
  change (retraction _ _ _ (point, 0)).val = (retraction _ _ _ (point, 1)).val at h
  have hh : (point, (0 : I)) = (point, (1 : I)) := h0.symm.trans (h.trans h1)
  have he := congrArg (fun z => (z.2 : ℝ)) hh
  norm_num at he

def family : Registration arena.{u} (type_of% (@retraction_fixed.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@retraction_fixed.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@retraction_fixed.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteSubcomplexCylinder.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteSubcomplexCylinder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p z => (retraction p.K p.L p.inclusion z).val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteSubcomplexCylinder
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 6,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Geometry.FiniteSubcomplexCylinder

/- Complete source telescopes for the selected public statements. -/
#check @D5.S3.Geometry.FiniteSubcomplexCylinder.homotopy_extension
#check @D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction_fixed
#check @D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction_lower
#check @D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction_upper
#check @D5.S3.Geometry.FiniteSubcomplexCylinder.realization_eq_empty_of_no_faces
#check @D5.S3.Geometry.FiniteSubcomplexCylinder.realization_nonempty_iff_faces_nonempty
#check @D5.S3.Geometry.FiniteSubcomplexCylinder.retraction_fixed
