import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteConeCollapse

/-! The coordinate-face observation over all finite vertex types and all faces. -/
noncomputable section
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteConeCollapse

namespace Reg.D5.S3.Geometry.FiniteConeCollapse

universe u

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V

attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (p.V → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => faceSimplex s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u}, ∀ s : Finset p.V,
    R.readout () p s = convexHull ℝ ((fun v : p.V => Pi.single v (1 : ℝ)) '' (s : Set p.V))

private theorem bridge : (type_of% (@faceSimplex_eq_convexHull.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p s
    exact h s
  · intro h V fv dv s
    exact h ⟨V, fv, dv⟩ s

private def unitParameters : Parameters.{u} :=
  ⟨ULift.{u} Unit, inferInstance, inferInstance⟩

private theorem singleton_mem :
    (fun _ : unitParameters.{u}.V => (1 : ℝ)) ∈
      faceSimplex ({⟨()⟩} : Finset unitParameters.V) := by
  constructor
  · intro v
    norm_num
  · constructor
    · simp [unitParameters]
    · intro v hv
      exact (hv (by have : v = ⟨()⟩ := Subsingleton.elim _ _; simp [this])).elim

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h unitParameters ({⟨()⟩} : Finset unitParameters.V)
  have hm := singleton_mem.{u}
  rw [faceSimplex_eq_convexHull] at hm
  change (∅ : Set (unitParameters.V → ℝ)) = _ at hh
  rw [← hh] at hm
  exact hm

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨unitParameters, ∅, ({⟨()⟩} : Finset unitParameters.V), ?_⟩
  intro h
  have hm := singleton_mem.{u}
  change faceSimplex (∅ : Finset unitParameters.V) = faceSimplex {⟨()⟩} at h
  rw [← h] at hm
  have hz := hm.2.2 (⟨()⟩ : unitParameters.V) (by simp)
  norm_num at hz

def family : Registration arena.{u} (type_of% (@faceSimplex_eq_convexHull.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@faceSimplex_eq_convexHull.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@faceSimplex_eq_convexHull.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteConeCollapse.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteConeCollapse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => faceSimplex s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteConeCollapse
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 3,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.FiniteConeCollapse
