import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.TwoNegativeJointLift
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.TwoNegativeJointLift
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.TwoNegativeJointLift

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin k → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualSource k t)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → b < a →
    ∃ sigma : List (Fin (a + b)), ∃ j : ℕ, j ≤ a + b ∧
      (sigma.Perm (List.finRange (a+b)) ∧
        (sigma.map (R.readout () (a+b) (2^a+1))).sum = 0 ∧
        ∀ n : ℕ, ((sigma.take n).map (R.readout () (a+b) (2^a+1))).sum ∈
          Set.Icc (0:ℤ) (modulus (a+b)/2)) ∧
      (let word := earWord (a+b) sigma j
       word.Perm (List.finRange (a+b+1)) ∧
        (word.map (R.readout () (a+b+1) (2*(2^a+1)))).sum = 0 ∧
        ∀ n : ℕ, ((word.take n).map (R.readout () (a+b+1) (2*(2^a+1)))).sum ∈
          Set.Icc (0:ℤ) (modulus (a+b+1)/2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma, j, hj, hs, _⟩ := h 3 2 (by omega) (by omega) (by omega)
  have hlen : sigma.length = 5 := by simpa using hs.1.length_eq
  have hh := (hs.2.2 1).1
  cases sigma with
  | nil => simp at hlen
  | cons x xs =>
    change 0 ≤ ([-1] : List ℤ).sum at hh
    norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 3)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.TwoNegativeJointLift.actualSource_two_negative_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualSource_two_negative_joint_lift, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.TwoNegativeJointLift.actualSource_two_negative_joint_lift)
    (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.TwoNegativeJointLift.actualSource_two_negative_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.TwoNegativeJointLift.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration

end Reg.D5.S3.Combinatorics.Circle.TwoNegativeJointLift
