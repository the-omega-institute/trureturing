import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open _root_.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound
noncomputable section

abbrev rankSignature : Signature where
  Params := Unit
  State _ := Finset (Fin 4)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rankActual : Realization rankSignature :=
  realize rankSignature (fun _ _ J => rankAverage J) (fun e => nomatch e)

def rankRejected : Realization rankSignature :=
  realize rankSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev rankArena : Arena where
  signature := rankSignature
  Law R :=
    (∀ J : Finset (Fin 4), (0 : Fin 4) ∈ J →
      (25 : ℝ) / 48 ≤ R.readout () () J) ∧
    R.readout () () (Finset.univ : Finset (Fin 4)) = (25 : ℝ) / 48

private theorem rankPositive : rankArena.Law rankActual := by
  exact _root_.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.second_star_rank_coordinate_bound_and_sharp

private theorem rankNegative : ¬ rankArena.Law rankRejected := by
  intro h
  have he := h.2
  change (0 : ℝ) = (25 : ℝ) / 48 at he
  norm_num at he

private theorem rankDependence :
    ObservationalDependence rankSignature rankActual := by
  intro i
  refine ⟨(), ({0} : Finset (Fin 4)), (Finset.univ : Finset (Fin 4)), ?_⟩
  intro heq
  have h := congrArg (fun x : ℝ => x) heq
  norm_num [rankActual, realize, rankAverage, rankWeight, Fin.sum_univ_succ] at h

def rankFamily : Registration rankArena
    (type_of% (@_root_.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.second_star_rank_coordinate_bound_and_sharp)) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨rankPositive, rankRejected, rankNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rankRejected, ?_, rfl, rankNegative⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := rankDependence

noncomputable def rank_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.second_star_rank_coordinate_bound_and_sharp)
      (type_of% (realize rankSignature
        (fun _ _ J => rankAverage J) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.second_star_rank_coordinate_bound_and_sharp.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.rankFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena⟩
  objectArena := .source ⟨rankArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankArena ⟨rankFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature
    (fun _ _ J => rankAverage J) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
}

#print axioms rankFamily
#print axioms rank_registration

abbrev parentSignature : Signature where
  Params := Unit
  State _ := Fin 4 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def parentActual : Realization parentSignature :=
  realize parentSignature
    (fun _ _ β => β 0 + (1 / 2 : ℝ) * β 1 +
      (1 / 3 : ℝ) * β 2 + (1 / 4 : ℝ) * β 3)
    (fun e => nomatch e)

def parentRejected : Realization parentSignature :=
  realize parentSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev parentArena : Arena where
  signature := parentSignature
  Law R :=
    (∀ (β : Fin 4 → ℝ), (∑ j, β j) = 1 →
      (∀ j, β j ≤ β 0) →
      (25 : ℝ) / 48 ≤ R.readout () () β) ∧
    (25 : ℝ) / 48 =
      R.readout () () (fun _ => (1 / 4 : ℝ))

private theorem parentPositive : parentArena.Law parentActual := by
  exact _root_.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.parent_star_coordinate_bound_and_sharp

private theorem parentNegative : ¬ parentArena.Law parentRejected := by
  intro h
  have he := h.2
  change (25 : ℝ) / 48 = 0 at he
  norm_num at he

private theorem parentDependence :
    ObservationalDependence parentSignature parentActual := by
  intro i
  refine ⟨(), (fun _ => (1 / 4 : ℝ)), (fun _ => 0), ?_⟩
  intro heq
  have h := congrArg (fun x : ℝ => x) heq
  norm_num [parentActual, realize] at h

def parentFamily : Registration parentArena
    (type_of% (@_root_.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.parent_star_coordinate_bound_and_sharp)) where
  actual := parentActual
  bridge := Iff.rfl
  variation := ⟨parentPositive, parentRejected, parentNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨parentRejected, ?_, rfl, parentNegative⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := parentDependence

noncomputable def parent_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.parent_star_coordinate_bound_and_sharp)
      (type_of% (realize parentSignature
        (fun _ _ β => β 0 + (1 / 2 : ℝ) * β 1 +
          (1 / 3 : ℝ) * β 2 + (1 / 4 : ℝ) * β 3)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.parent_star_coordinate_bound_and_sharp.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound.parentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨parentArena⟩
  objectArena := .source ⟨parentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source parentArena ⟨parentFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize parentSignature
    (fun _ _ β => β 0 + (1 / 2 : ℝ) * β 1 +
      (1 / 3 : ℝ) * β 2 + (1 / 4 : ℝ) * β 3)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
}

#print axioms parentFamily
#print axioms parent_registration

end
end Reg.D5.S3.Geometry.Gluing.SecondBarycentricCoordinateBound

