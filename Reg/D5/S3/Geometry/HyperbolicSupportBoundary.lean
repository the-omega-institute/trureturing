import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.HyperbolicSupportBoundary
import D5.S3.Geometry.HyperbolicPlaneRealization
import Reg.Support.DependentFamily

open scoped Topology BigOperators
open Set
open LeanInformationAudit
open _root_.D5.S3.Geometry.HyperbolicUpperHalfSpace
open _root_.D5.S3.Geometry.Hyperideal.LengthGramBody
open _root_.D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open _root_.D5.S3.Geometry.HyperbolicSupportBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Geometry.HyperbolicSupportBoundary
noncomputable section
universe u

abbrev SupportData := Σ (ι : Type u), ι → Fin 4 → ℝ

abbrev signature : Signature where
  Params := SupportData.{u}
  State _ := UpperHalfPlane → HyperbolicThreeSpace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set UpperHalfPlane
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p e => supportRegion e p.2) (fun a => nomatch a)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Finite ι]
    (e : UpperHalfPlane → HyperbolicThreeSpace) (he : Isometry e)
    (N : Fin 4 → ℝ)
    (hplane : range e = {p | lorentz N (lift p) = 0})
    (A : ι → Fin 4 → ℝ)
    (hw : ∀ i, ∃ y ∈ supportRegion e A, lorentz (A i) (lift (e y)) < 0),
    interior (R.readout () ⟨ι,A⟩ e) =
      {z | ∀ i, lorentz (A i) (lift (e z)) < 0} ∧
    frontier (R.readout () ⟨ι,A⟩ e) =
      {z ∈ R.readout () ⟨ι,A⟩ e | ∃ i, lorentz (A i) (lift (e z)) = 0}

theorem bridge :
    (type_of% (@support_region_boundary.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h ι finiteI e he N hp A hw
    exact h e he N hp A hw
  · intro h ι finiteI e he N hp A hw
    exact h e he N hp A hw

private def z : UpperHalfPlane := ⟨Complex.I, by norm_num⟩

private theorem time_support (p : HyperbolicThreeSpace) :
    lorentz ![0,0,0,1] (lift p) < 0 := by
  simpa [lorentz, Fin.sum_univ_succ] using (neg_neg_of_pos (lift_time p))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let N : Fin 4 → ℝ := ![0,1,0,0]
  obtain ⟨e,he,hp⟩ :=
    _root_.D5.S3.Geometry.HyperbolicPlaneRealization.supporting_plane_isometry N
      (by norm_num [N,lorentz,Fin.sum_univ_succ])
  have hp' : range e = {p | lorentz N (lift p) = 0} := by
    simpa only [lorentz_symm] using hp
  let A : ULift.{u} Unit → Fin 4 → ℝ := fun _ => ![0,0,0,1]
  have hw : ∀ i, ∃ y ∈ supportRegion e A, lorentz (A i) (lift (e y)) < 0 := by
    intro i
    exact ⟨z,fun _ => (time_support (e z)).le,time_support (e z)⟩
  have hi := (@h (ULift.{u} Unit) inferInstance e he N hp' A hw).1
  change interior (∅ : Set UpperHalfPlane) = _ at hi
  have hz : z ∈ interior (∅ : Set UpperHalfPlane) := by
    rw [hi]
    exact fun _ => time_support (e z)
  simpa using hz

private def point (x : ℝ) : HyperbolicThreeSpace :=
  ⟨⟨WithLp.toLp 2 (Complex.mk x 0,1), by norm_num⟩⟩

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let p : SupportData.{u} := ⟨ULift.{u} Unit,fun _ => ![1,0,0,0]⟩
  let N : Fin 4 → ℝ := ![0,1,0,0]
  obtain ⟨e,he,hplane⟩ :=
    _root_.D5.S3.Geometry.HyperbolicPlaneRealization.supporting_plane_isometry N
      (by norm_num [N,lorentz,Fin.sum_univ_succ])
  have hr : range e = {x | lorentz N (lift x) = 0} := by
    simpa only [lorentz_symm] using hplane
  have hmem : point (-1) ∈ range e := by
    rw [hr]
    norm_num [N,point,lift,lorentz,height,Fin.sum_univ_succ]
  obtain ⟨zm,hzm⟩ := hmem
  let shifted : {f : UpperHalfPlane → HyperbolicThreeSpace // Isometry f} :=
    ⟨fun z => ⟨horizontalTranslate (2 : ℂ) (e z).coordinates⟩, by
      apply Isometry.of_dist_eq
      intro x y
      change hyperbolicDist (horizontalTranslate (2 : ℂ) (e x).coordinates)
        (horizontalTranslate (2 : ℂ) (e y).coordinates) = dist x y
      rw [hyperbolicDist_horizontalTranslate]
      exact he.dist_eq x y⟩
  let ep : UpperHalfPlane → HyperbolicThreeSpace := shifted.val
  refine ⟨p,e,ep,?_⟩
  change supportRegion e p.2 ≠ supportRegion ep p.2
  intro h
  have hm : zm ∈ supportRegion e p.2 := by
    intro i
    rw [hzm]
    norm_num [p,point,lift,lorentz,height,Fin.sum_univ_succ]
  rw [h] at hm
  have hp := hm (ULift.up ())
  change lorentz ![1,0,0,0]
    (lift ⟨horizontalTranslate (2 : ℂ) (e zm).coordinates⟩) ≤ 0 at hp
  rw [hzm] at hp
  norm_num [horizontalTranslate,point,lift,lorentz,height,Fin.sum_univ_succ] at hp

def familyRegistration : Registration arena.{u} (type_of% (@support_region_boundary.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @support_region_boundary,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@support_region_boundary.{u})
    (type_of% (realize signature.{u} (fun _ p e => supportRegion e p.2) (fun a => nomatch a)))
    Unit Unit := {
  unitName := `D5.S3.Geometry.HyperbolicSupportBoundary.support_region_boundary.region,
  realizationName := `Reg.D5.S3.Geometry.HyperbolicSupportBoundary.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p e => supportRegion e p.2) (fun a => nomatch a)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.HyperbolicSupportBoundary,
    definition := none,
    coordinates := #[0,6],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","fn","arg","arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","body","body","arg","fn","arg","arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","body","body","arg","arg","arg","body","fn","arg","fn","arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
end Reg.D5.S3.Geometry.HyperbolicSupportBoundary
