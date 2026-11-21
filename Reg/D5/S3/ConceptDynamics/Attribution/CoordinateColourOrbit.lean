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

end
end Reg.D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
