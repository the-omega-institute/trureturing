import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.FinitePowerWindowAvoidance
import Reg.Support.SingleDependentReadout

/-! The positive lower endpoint is observed as a real-valued witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.CharacterSums.FinitePowerWindowAvoidance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.FinitePowerWindowAvoidance

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ y => y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (E : Finset ℝ) (η C X L : ℝ), (η < C → 0 < η) → 1 < X → 1 ≤ L →
    let J := if C ≤ η then L
      else L * (L * C / η) ^ (E.filter (fun a => 1 < a ∧ a ≤ X ^ C)).card
    ∃ Y : ℝ, 1 < V.readout () () Y ∧ X ^ (1 / J) ≤ Y ∧ Y ^ L ≤ X ∧
      ∀ x ∈ Set.Icc Y (Y ^ L), ∀ a ∈ E, a ≤ x ^ C → a ≤ x ^ η

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Y, hY, _⟩ := h ∅ 1 1 2 2 (by norm_num) (by norm_num) (by norm_num)
  change (1 : ℝ) < 0 at hY
  norm_num at hY

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @finite_power_window) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_power_window, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_power_window) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.FinitePowerWindowAvoidance.finite_power_window "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.FinitePowerWindowAvoidance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ y => y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.FinitePowerWindowAvoidance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
