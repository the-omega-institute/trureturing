import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.ArithUnits.GolovanovBareDrazinEqualities
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic

/-! Readout of the first test of the finite Drazin sum equality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ArithUnits.GolovanovBareDrazinEqualities

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithUnits.GolovanovBareDrazinEqualities
open LeanInformationAudit

universe u

private abbrev signature : Signature where
  Params := Type u
  State R := R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ R := R → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law V := ∀ {R : Type u} [Ring R] (a c u v b : R) (hab : (a + c) * b = 1)
    (hba : b * (a + c) = 1) (ha : FD a u) (hc : FD c v),
    let p := a * u
    let r := c * v
    let z := r - p
    let nₐ := a - p * a
    let nc := c - r * c
    let t := a - a * b * a
    let P := c * b * nₐ * b * c + a * b * nc * b * a
    (∃ ht : ∃ y, FD t y, drazin t ht = drazin a ⟨u, ha⟩ + drazin c ⟨v, hc⟩) ↔
      V.readout () R (a * b * z) (z * b * a) ∧ z * b * z = 0 ∧ IsNilpotent P

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let R := ULift.{u} (ZMod 1)
  have fd : FD (0 : R) 0 := ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
    ⟨1, Subsingleton.elim _ _⟩⟩
  have hu : ((0 : R) + 0) * 0 = 1 := Subsingleton.elim _ _
  have hv : (0 : R) * (0 + 0) = 1 := Subsingleton.elim _ _
  have hpositive := (result 0 0 0 0 0 hu hv fd fd).mpr
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, ⟨1, Subsingleton.elim _ _⟩⟩
  exact ((h 0 0 0 0 0 hu hv fd fd).mp hpositive).1

noncomputable def family : Registration arena.{u} (type_of% @result.{u}) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@result.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨ULift.{u} ℤ, 0, 1, fun h => ?_⟩
    have he : ((0 : ULift.{u} ℤ) = 0) = ((1 : ULift.{u} ℤ) = 0) := congrFun h 0
    exact one_ne_zero (Eq.mp he rfl)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.ArithUnits.GolovanovBareDrazinEqualities.result.__information_unit
  realizationName := `Reg.D5.S3.ArithUnits.GolovanovBareDrazinEqualities.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithUnits.GolovanovBareDrazinEqualities
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ArithUnits.GolovanovBareDrazinEqualities
