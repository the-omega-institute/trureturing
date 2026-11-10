import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Matroids.LocalSearchRobustness

/-! Full-telescope source-bound observations of the actual finite-set weight readout. -/

namespace Reg.D5.S3.Combinatorics.Matroids.LocalSearchRobustness

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.LocalSearchRobustness
open _root_.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Matroid
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

structure FiniteCarrier where
  carrier : Type u
  finite : Finite carrier

attribute [instance] FiniteCarrier.finite

abbrev signature : Signature where
  Params := FiniteCarrier.{u}
  State p := p.carrier → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set p.carrier → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ w => baseWeight w) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h ({ULift.up ()} : Set (ULift.{u} Unit))
  norm_num [actual,realize,baseWeight] at hh

namespace Comparison
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [hE : Finite E] (M : Matroid E) (w : E → ℝ)
    (B0 B1 : {B : Set E // M.IsBase B}) (r : ℕ)
    (_hstep : (B1.val \ B0.val).ncard ≤ 1),
    neighborhoodMax M w B1 r + neighborhoodMax M w B0 1 ≥
      neighborhoodMax M w B0 (r + 1) + R.readout () ⟨E,hE⟩ w B1.val

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (E := ULift.{u} Unit) (loopyOn ∅) (fun _ => 0)
    ⟨∅,by simp⟩ ⟨∅,by simp⟩ 0 (by simp)
  norm_num [rejected,realize,neighborhoodMax,baseWeight] at hh

def source_registration : Registration arena.{u}
    (type_of% (@neighborhood_comparison.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neighborhood_comparison, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@neighborhood_comparison.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.LocalSearchRobustness.neighborhood_comparison.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.LocalSearchRobustness.Comparison.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.LocalSearchRobustness
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Comparison

namespace Robustness
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [hE : Finite E] (M : Matroid E) (w : E → ℝ) (k : ℕ)
    (B : Fin (k + 1) → {B : Set E // M.IsBase B})
    (_hstep : ∀ i : Fin k, ((B i.succ).val \ (B i.castSucc).val).ncard ≤ 1),
    (∀ i : Fin k, 0 ≤ localError M w (B i.castSucc) (B i.succ)) ∧
      ∀ C : Set E, M.IsBase C → (C \ (B 0).val).ncard ≤ k →
        R.readout () ⟨E,hE⟩ w C ≤ baseWeight w (B (Fin.last k)).val +
          ∑ i : Fin k, localError M w (B i.castSucc) (B i.succ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (E := ULift.{u} Unit) (loopyOn ∅) (fun _ => 0) 0
    (fun _ => ⟨∅,by simp⟩) (by intro i; exact Fin.elim0 i)).2 ∅ (by simp) (by simp)
  norm_num [rejected,realize,baseWeight] at hh

def source_registration : Registration arena.{u}
    (type_of% (@local_search_robustness.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_search_robustness, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@local_search_robustness.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.LocalSearchRobustness.local_search_robustness.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.LocalSearchRobustness.Robustness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.LocalSearchRobustness
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Robustness

#print axioms Comparison.source_registration
#print axioms Robustness.source_registration

end
end Reg.D5.S3.Combinatorics.Matroids.LocalSearchRobustness
