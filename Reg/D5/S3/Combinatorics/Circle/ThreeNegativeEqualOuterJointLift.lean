import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

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
  realize signature (fun _ k seed => actualSource k seed) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

private def readoutOrder (R : Realization signature) (k seed : ℕ)
    (word : List (Fin k)) : Prop :=
  word.Perm (List.finRange k) ∧ (word.map (R.readout () k seed)).sum = 0 ∧
    ∀ n : ℕ, ((word.take n).map (R.readout () k seed)).sum ∈
      Set.Icc (0 : ℤ) (modulus k / 2)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℕ) (_ha : 2 ≤ a) (_hab : a < b),
    ∃ sigma : List (Fin (a + b + a)),
      readoutOrder R (a + b + a) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      readoutOrder R (a + b + a + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b)))
        (earWord (a + b + a) sigma (a + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨sigma, hold, _⟩ := h 2 3 (by decide) (by decide)
  have hlength : sigma.length = 7 := by simpa using hold.1.length_eq
  have hz := hold.2.1
  norm_num [rejected, realize, List.map_const', hlength] at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨7, 1, 2, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 7)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def source_registration : Registration arena
    (type_of% (@actualSource_three_negative_equal_outer_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualSource_three_negative_equal_outer_joint_lift, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift.actualSource_three_negative_equal_outer_joint_lift)
    (type_of% (realize signature (fun _ k seed => actualSource k seed) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift.actualSource_three_negative_equal_outer_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k seed => actualSource k seed) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end Reg.D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
