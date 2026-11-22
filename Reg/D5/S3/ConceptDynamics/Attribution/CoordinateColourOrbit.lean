import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
import Reg.Support.DependentFamily

/-! The left profile is observed at a coordinate where its colour can change. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
open _root_.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

noncomputable section

abbrev signature : Signature where
  Params := Type u
  State I := I → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := I → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ profile => profile) (fun e => nomatch e)

def alwaysTrue : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] (p q : I → Bool),
    (∀ m : Output I → Output I → ℕ,
      (∀ (g : Acting I) x y, m (g • x) (g • y) = m x y) →
      4 ∣ ∑ c : ZMod 2, ∑ d : ZMod 2, m ⟨p, c⟩ ⟨q, d⟩) ↔
      p ≠ q ∧ (∃ j, R.readout () I p j = false) ∧ (∃ j, q j = false)

private theorem always_true_fails : ¬ arena.{u}.Law alwaysTrue := by
  intro law
  let I := ULift.{u} Bool
  let p (i : I) := i.down
  let q (i : I) := !i.down
  have different : p ≠ q := by
    intro eq
    have atFalse := congrFun eq (⟨false⟩ : I)
    cases atFalse
  have counts := (universally_four_dvd_iff p q).mpr
    ⟨different, ⟨⟨false⟩, rfl⟩, ⟨⟨true⟩, rfl⟩⟩
  obtain ⟨i, bad⟩ := ((law p q).mp counts).2.1
  change true = false at bad
  cases bad

def family : Registration arena.{u} (type_of% (@universally_four_dvd_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@universally_four_dvd_iff, alwaysTrue, always_true_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysTrue, ?_, rfl, always_true_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨PUnit.{u+1}, (fun _ => false), (fun _ => true), ?_⟩
    intro eq
    have different := congrFun eq PUnit.unit
    change false = true at different
    cases different

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@universally_four_dvd_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit.leftProfile
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ profile => profile) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg",
        "arg", "body", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


open Classical in
abbrev singleShiftArena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] (p : I → Bool) (i : I) (a : ZMod 2),
    shift p (Pi.single i a) = if R.readout () I p i then 0 else a

private theorem zero_shift_fails : ¬ singleShiftArena.{u}.Law alwaysTrue := by
  classical
  intro law
  let I := PUnit.{u+1}
  let i : I := PUnit.unit
  let profile : I → Bool := fun _ => false
  have original := eval_single profile i (1 : ZMod 2)
  have modified := law profile i (1 : ZMod 2)
  have incompatible := original.symm.trans modified
  have eq : (1 : ZMod 2) = 0 := by simpa [profile, alwaysTrue, realize] using incompatible
  exact one_ne_zero eq

def singleShiftFamily : Registration singleShiftArena.{u} (type_of% (@eval_single.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eval_single, alwaysTrue, zero_shift_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysTrue, ?_, rfl, zero_shift_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := family.dependence

def singleShiftRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eval_single.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit.singleShiftProfile
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit.singleShiftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨singleShiftArena.{u}⟩
  objectArena := .source ⟨singleShiftArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source singleShiftArena.{u} ⟨singleShiftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ profile => profile) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "fn", "fn", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


def alwaysFalse : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => false) (fun e => nomatch e)

abbrev pairedShiftArena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] (p q : I → Bool), p ≠ q →
    (∃ j, R.readout () I p j = false) → (∃ j, q j = false) →
    Function.Surjective (fun v : I → ZMod 2 => (shift p v, shift q v))

private theorem always_false_fails : ¬ pairedShiftArena.{u}.Law alwaysFalse := by
  intro law
  let p : PUnit.{u+1} → Bool := fun _ => true
  let q : PUnit.{u+1} → Bool := fun _ => false
  have ne : p ≠ q := fun eq => Bool.noConfusion (congrFun eq PUnit.unit)
  obtain ⟨v, h⟩ := law p q ne ⟨PUnit.unit, rfl⟩ ⟨PUnit.unit, rfl⟩ (1, 0)
  have left := congrArg Prod.fst h
  change shift p v = 1 at left
  simp [shift, p] at left

def pairedShiftFamily : Registration pairedShiftArena.{u} (type_of% (@shifts_surjective.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@shifts_surjective, alwaysFalse, always_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysFalse, ?_, rfl, always_false_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := family.dependence

def pairedShiftRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shifts_surjective.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit.pairedShiftProfile
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit.pairedShiftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pairedShiftArena.{u}⟩
  objectArena := .source ⟨pairedShiftArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairedShiftArena.{u} ⟨pairedShiftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ profile => profile) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain",
        "arg", "body", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev allTrueShiftArena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] (p : I → Bool)
    (_ : ∀ i, R.readout () I p i = true) (v : I → ZMod 2), shift p v = 0

private theorem false_profile_can_shift : ¬ allTrueShiftArena.{u}.Law alwaysTrue := by
  intro law
  let I := PUnit.{u+1}
  let p : I → Bool := fun _ => false
  let v : I → ZMod 2 := fun _ => 1
  have h := law p (fun _ => rfl) v
  simp [p, v, I, shift] at h

def allTrueShiftFamily : Registration allTrueShiftArena.{u} (type_of% (@all_true_shift.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@all_true_shift, alwaysTrue, false_profile_can_shift⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysTrue, ?_, rfl, false_profile_can_shift⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := family.dependence

def allTrueShiftRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@all_true_shift.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit.allTrueShiftProfile
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit.allTrueShiftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨allTrueShiftArena.{u}⟩
  objectArena := .source ⟨allTrueShiftArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source allTrueShiftArena.{u} ⟨allTrueShiftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ profile => profile) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain", "body", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
