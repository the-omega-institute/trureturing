import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.YangBaxterAutomatonPeriod
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

/-! Source-bound audit of the square-one hypothesis for commuting generators of a 2-group. -/

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.YangBaxterAutomatonPeriod

open _root_.D5.S3.StatisticalMechanics.CellularAutomata.YangBaxterAutomatonPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u_1
noncomputable section

/-- Equality of the two operands in the square-one hypothesis. -/
abbrev signature : Signature where
  Params := Type u_1
  State G := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ G := G → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

/-- Retain every group, generator set, and commutativity and square-one hypothesis. -/
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {G : Type u_1} [Group G] (S : Set G),
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) →
    (∀ x ∈ S, R.readout () G (x * x) 1) → IsPGroup 2 (Subgroup.closure S)

private theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro law
  have hp := @law (ULift.{u_1} (Multiplicative ℤ)) inferInstance Set.univ
    (fun x _ y _ => mul_comm x y) (fun _ _ => True.intro)
  rw [Subgroup.closure_univ, isPGroup_iff_pow_pow_eq_one] at hp
  obtain ⟨k, hk⟩ := hp ⟨⟨Multiplicative.ofAdd 1⟩, Subgroup.mem_top _⟩
  have hz := congrArg (fun g => Multiplicative.toAdd (ULift.down (Subtype.val g))) hk
  change (2 ^ k : ℕ) • (1 : ℤ) = 0 at hz
  have hpos : (0 : ℤ) < (2 : ℤ) ^ k := pow_pos (by decide) k
  simp only [nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at hz
  exact (ne_of_gt hpos) hz

private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨ULift.{u_1} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
  intro h
  have hbad : (ULift.up true : ULift.{u_1} Bool) = ULift.up false :=
    Eq.mp (congrFun h (ULift.up false)) rfl
  cases congrArg ULift.down hbad

def source_registration : Registration arena.{u_1}
    (type_of% (@isPGroup_closure_of_commuting_involutions.{u_1})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨isPGroup_closure_of_commuting_involutions, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@isPGroup_closure_of_commuting_involutions.{u_1})
      (Realization signature.{u_1}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.YangBaxterAutomatonPeriod.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.YangBaxterAutomatonPeriod.source_registration
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
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.YangBaxterAutomatonPeriod
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.CellularAutomata.YangBaxterAutomatonPeriod
