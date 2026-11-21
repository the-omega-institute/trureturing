import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
import Reg.Support.DependentFamily

/-! The lift uses the divided left row of each coloured profile. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

abbrev signature : Signature where
  Params := Type u
  State I := (I → Bool) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := Output I → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ law x => law x.profile / 2) (fun e => nomatch e)

def negativeLeft : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (left right : (I → Bool) → ℝ) (a : I → ℝ),
    (∃ w : Output I → Output I → ℝ,
      Coupling (R.readout () I left) (fun y => right y.profile / 2) w ∧
      (∀ (g : Acting I) x y, w (g • x) (g • y) = w x y) ∧
      ∀ i, commonFixed w i = a i) ↔
    ∃ w : (I → Bool) → (I → Bool) → ℝ, Coupling left right w ∧ ∀ i, commonTrue w i = a i

private theorem negative_left_fails : ¬ arena.{u}.Law negativeLeft := by
  intro law
  let I := PUnit.{u+1}
  let _ : Fintype I := inferInstanceAs (Fintype PUnit)
  let _ : DecidableEq I := inferInstanceAs (DecidableEq PUnit)
  have feasible :
      ∃ w : (I → Bool) → (I → Bool) → ℝ, Coupling (fun _ => 0) (fun _ => 0) w ∧
        ∀ i, commonTrue w i = 0 := by
    refine ⟨fun _ _ => 0, ⟨fun _ _ => le_rfl, by simp, by simp⟩, fun i => ?_⟩
    simp [commonTrue]
  obtain ⟨w, hw, _, _⟩ := (law (I := I) (fun _ => 0) (fun _ => 0) (fun _ => 0)).mpr feasible
  let y : Output I := ⟨fun _ => false, 0⟩
  have nonnegative : 0 ≤ ∑ z, w y z := sum_nonneg (fun z _ => hw.1 y z)
  have negative := hw.2.1 y
  change (∑ z, w y z) = -1 at negative
  norm_num [negative] at nonnegative

def family : Registration arena.{u} (type_of% (@invariant_coupling_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@invariant_coupling_iff, negativeLeft, negative_left_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨negativeLeft, ?_, rfl, negative_left_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    let y : Output PUnit.{u+1} := ⟨fun _ => false, 0⟩
    refine ⟨PUnit.{u+1}, (fun _ => 0), (fun _ => 2), ?_⟩
    intro eq
    have diff := congrFun eq y
    change (0 : ℝ) / 2 = 2 / 2 at diff
    norm_num at diff

def colouredRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@invariant_coupling_iff) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling.colouredLeft
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ law x => law x.profile / 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body",
        "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
