import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteConeUnionWedge

/-! The actual intersection observation over all finite vertex types and complexes. -/
noncomputable section
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteConeCollapse
open _root_.D5.S3.Geometry.FiniteConeUnionWedge

namespace Reg.D5.S3.Geometry.FiniteConeUnionWedge

universe u

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V
  other : PreAbstractSimplicialComplex V

attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := PreAbstractSimplicialComplex p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (p.V → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => realization (M ⊓ p.other)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u}, ∀ M : PreAbstractSimplicialComplex p.V,
    R.readout () p M = realization M ∩ realization p.other

private theorem bridge : (type_of% (@realization_intersection.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p M
    exact h M p.other
  · intro h V fv dv M N
    exact h ⟨V, fv, dv, N⟩ M

private abbrev unitParameters : Parameters.{u} :=
  ⟨ULift.{u} Unit, inferInstance, inferInstance, ⊤⟩

private theorem top_point :
    Pi.single (⟨()⟩ : unitParameters.{u}.V) (1 : ℝ) ∈
      realization (⊤ : PreAbstractSimplicialComplex unitParameters.V) :=
  ⟨{⟨()⟩}, Finset.singleton_nonempty _,
    subset_convexHull ℝ _ ⟨⟨()⟩, by simp, rfl⟩⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h unitParameters ⊤
  have hm := top_point.{u}
  change (∅ : Set (unitParameters.V → ℝ)) = realization ⊤ ∩ realization ⊤ at hh
  have : Pi.single (⟨()⟩ : unitParameters.V) (1 : ℝ) ∈
      (∅ : Set (unitParameters.V → ℝ)) := hh.symm ▸ ⟨hm, hm⟩
  exact this

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨unitParameters, ⊥, ⊤, ?_⟩
  intro h
  change realization ((⊥ : PreAbstractSimplicialComplex unitParameters.V) ⊓ ⊤) =
    realization ((⊤ : PreAbstractSimplicialComplex unitParameters.V) ⊓ ⊤) at h
  simp only [bot_inf_eq, inf_top_eq] at h
  have hm := h.symm ▸ top_point.{u}
  obtain ⟨s, hs, _⟩ := hm
  exact hs

def family : Registration arena.{u} (type_of% (@realization_intersection.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@realization_intersection.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@realization_intersection.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteConeUnionWedge.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteConeUnionWedge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => realization (M ⊓ p.other))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteConeUnionWedge
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 3,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.FiniteConeUnionWedge
