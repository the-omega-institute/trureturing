import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.ArithUnits.RakicTheorem213RingExtension
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic

/-! Readout of the equality between the cube and the sandwiched product. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ArithUnits.RakicTheorem213RingExtension

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithUnits.RakicTheorem213RingExtension
open _root_.D5.S3.ArithUnits.GolovanovBareDrazinEqualities (FD)
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

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law V := ∀ {R : Type u} [Ring R] (a α b β : R) (ha : GroupInv a α) (hb : GroupInv b β),
    (MinusOrder a b ∧ GroupInv (b - a) (β - α)) ↔
      (V.readout () R (a ^ 3) (a * b * a) ∧ a ^ 3 = a * b ^ 2 ∧ a ^ 3 = b ^ 2 * a ∧
        (b - a) ^ 3 = b ^ 3 - a ^ 3)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let R := ULift.{u} (ZMod 1)
  have gi (x y : R) : GroupInv x y := by
    unfold GroupInv FD
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      ⟨1, Subsingleton.elim _ _⟩⟩
  have hm : MinusOrder (0 : R) 0 :=
    ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  exact ((h 0 0 0 0 (gi 0 0) (gi 0 0)).mp ⟨hm, gi _ _⟩).1

noncomputable def family : Registration arena.{u} (type_of% @result.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact (h (Subsingleton.elim _ _)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro role
    refine ⟨ULift.{u} ℤ, 0, 1, fun h => ?_⟩
    have he : ((0 : ULift.{u} ℤ) = 0) = ((1 : ULift.{u} ℤ) = 0) := congrFun h 0
    exact one_ne_zero (Eq.mp he rfl)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.ArithUnits.RakicTheorem213RingExtension.result.__information_unit
  realizationName := `Reg.D5.S3.ArithUnits.RakicTheorem213RingExtension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ArithUnits.RakicTheorem213RingExtension
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ArithUnits.RakicTheorem213RingExtension
