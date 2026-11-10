import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Symbolic.PermutativeLifts.AlignedTowerLimit
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S1.Dynamics.Symbolic.PermutativeLifts.AlignedTowerLimit.Intersection

open _root_.D5.S1.Dynamics.Symbolic.PermutativeLifts
open TwoRunRefinement AlignedTowerLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

abbrev signature := Reg.Support.SingleDependentReadout.signature
  (ℕ → Bool → List Bool) (fun _ => ℕ) (fun _ => Set (ℤ → Bool))

def actual : Realization signature :=
  realize signature (fun _ W n => alignedConfigurations (W n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (W : ℕ → Bool → List Bool)
    (hW : ∀ n a, 0 < (W n a).length)
    (hnest : ∀ n, alignedConfigurations (W (n + 1)) ⊆ alignedConfigurations (W n)),
    (⋂ n : ℕ, R.readout () W n).Nonempty

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (fun _ _ => [false]) (by intros; simp) (fun _ => Set.Subset.rfl)
  simpa [rejected, realize] using hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(fun n _ => [if n = 0 then false else true]), 0, 1, ?_⟩
  change alignedConfigurations (fun _ => [false]) ≠ alignedConfigurations (fun _ => [true])
  intro heq
  obtain ⟨z, hz⟩ := (alignedConfigurations_compact_nonempty (fun _ => [false])
    (by intros; simp)).2
  have hz' := heq ▸ hz
  obtain ⟨xf, hxf, hf⟩ := hz
  obtain ⟨xt, hxt, ht⟩ := hz'
  have hval := congrFun (hf.trans ht.symm) 0
  simpa [readTiling, readTile, List.get_eq_getElem] using hval

def family : Registration arena
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.AlignedTowerLimit.aligned_intersection_nonempty)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.AlignedTowerLimit.aligned_intersection_nonempty,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.AlignedTowerLimit.aligned_intersection_nonempty)
    (type_of% actual) Unit Unit where
  unitName := `D5.S1.Dynamics.Symbolic.PermutativeLifts.AlignedTowerLimit.aligned_intersection_nonempty.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.PermutativeLifts.AlignedTowerLimit.Intersection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ W n => alignedConfigurations (W n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.PermutativeLifts.AlignedTowerLimit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S1.Dynamics.Symbolic.PermutativeLifts.AlignedTowerLimit.Intersection
