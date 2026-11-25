import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.ClippedWindowBadSet
import Reg.Support.UniverseSingleReadout

/-! The source observation is the cardinality of the full-window exceptional set. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset Real
open _root_.D5.S3.CharacterSums.ClippedWindowBadSet
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.ClippedWindowBadSet
universe u v

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Type u) (fun α => Finset α)
    (fun _ => ℝ)

def actual : Realization signature.{u} :=
  realize signature (fun _ _ B => (B.card : ℝ)) (fun e => nomatch e)

def inflated : Realization signature.{u} :=
  realize signature (fun _ _ _ => (1:ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law V := ∀ {α : Type u} {ι : Type v} (T : Finset ι) (h : ι → ℝ) (a : ι → α → ℂ),
    ∀ {C τ d Y X : ℝ} {P B : Finset α},
    0 ≤ C → 0 < τ → 0 < d → 2 ≤ Y →
    (∀ y ∈ Set.Icc Y X, ∀ κ' : ι → ℂ, (∀ n ∈ T, ‖κ' n‖ ≤ 1) →
      ∑ q ∈ P, ‖clippedSum T h a y q κ'‖^2 ≤ C*y*log y*P.card) →
    ∀ {κ : ι → ℂ}, (∀ n ∈ T, ‖κ n‖ ≤ 1) → B ⊆ P →
    (∀ q ∈ B, ∃ y ∈ Set.Icc Y X,
      d*y^(1/2+τ) ≤ ‖clippedSum T h a y q κ‖) →
    V.readout () α B ≤ min 1 (8*C/(d^2*τ)*Y^(-τ)/(1-(2:ℝ)^(-τ)))*P.card

private theorem inflated_fails : ¬ arena.{u,v}.Law inflated := by
  intro H
  have bad := H (α := ULift.{u} ℕ) (ι := ULift.{v} ℕ) ∅
    (fun _ => 1) (fun _ _ => 0)
    (C := 0) (τ := 1) (d := 1) (Y := 2) (X := 2) (P := ∅) (B := ∅)
    (κ := fun _ => 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp) (by simp) (by simp) (by simp)
  norm_num [inflated, realize] at bad

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨ULift.{u} ℕ, ∅, {⟨0⟩}, ?_⟩
  change ((∅ : Finset (ULift.{u} ℕ)).card : ℝ) ≠
    (({⟨0⟩} : Finset (ULift.{u} ℕ)).card : ℝ)
  simp


def family : Registration arena.{u,v} (type_of% @clipped_window_bad_set.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@clipped_window_bad_set, inflated, inflated_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual inflated inflated_fails
  dependence := dependence

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@clipped_window_bad_set.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.ClippedWindowBadSet.clipped_window_bad_set
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.ClippedWindowBadSet.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ B => (B.card:ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.ClippedWindowBadSet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","body","body","body",
        "body","fn","arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.ClippedWindowBadSet
