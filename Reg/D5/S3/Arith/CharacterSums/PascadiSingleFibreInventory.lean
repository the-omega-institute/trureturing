import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.CharacterSums.PascadiSingleFibreInventory
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-! The literal stationary inventory genuinely depends on the lower pivot at fixed slice. -/

namespace Reg.D5.S3.Arith.CharacterSums.PascadiSingleFibreInventory

open _root_.D5.S3.Arith.CharacterSums.PascadiSingleFibreInventory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := StationarySlice
  State R := ZMod R.p × ZMod R.p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev countBound (R : StationarySlice) (d : ZMod R.p × ZMod R.p) : ℝ :=
  8 * ((R.H : ℝ) ^ 4 / R.p) + 24 * ((R.H : ℝ) ^ 3 / directionMinimum R d) + 4 * (R.H : ℝ) ^ 2

def actual : Realization signature :=
  realize signature (fun _ R d => (stationaryCount R d : ℝ)) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ R d => countBound R d + 1) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (R : StationarySlice) (d : ZMod R.p × ZMod R.p), d.1 ≠ 0 ∨ d.2 ≠ 0 →
    F.readout () R d ≤ countBound R d ∧
    ((R.p : ℝ) / R.H ≤ directionMinimum R d →
      (stationaryCount R d : ℝ) ≤ 40 * ((R.H : ℝ) ^ 4 / R.p)) ∧
    ((shortDirections R).card : ℝ) ≤ 9 * ((R.p : ℝ) / R.H) ^ 2

private def sample : StationarySlice where
  p := 5
  prime := by decide
  H := 1
  width_pos := by decide
  width_lt := by decide
  firstCorner := (0, 0)
  secondCorner := (0, 0)
  h := 4
  point := (1, 1)
  smooth := by decide

private theorem reject_law : ¬ arena.Law rejected := by
  intro h
  have hn : (((1, 0) : ZMod sample.p × ZMod sample.p).1 ≠ 0) := by decide
  have hb := (h sample (1, 0) (Or.inl hn)).1
  change countBound sample (1, 0) + 1 ≤ countBound sample (1, 0) at hb
  exact (not_le_of_gt (lt_add_one _)) hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨sample, (1, 0), (1, 1), ?_⟩
  have h1 : stationaryCount sample (1, 0) = 8 := by decide
  have h2 : stationaryCount sample (1, 1) = 6 := by decide
  change (stationaryCount sample (1, 0) : ℝ) ≠ (stationaryCount sample (1, 1) : ℝ)
  rw [h1, h2]
  norm_num

def family : Registration arena (type_of% @single_fibre_inventory) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨single_fibre_inventory, rejected, reject_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, reject_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@single_fibre_inventory) (Realization signature) (Type) Unit where
  unitName :=
    `Reg.D5.S3.Arith.CharacterSums.PascadiSingleFibreInventory.unit
  realizationName :=
    `Reg.D5.S3.Arith.CharacterSums.PascadiSingleFibreInventory.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ R d => (stationaryCount R d : ℝ))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CharacterSums.PascadiSingleFibreInventory
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Arith.CharacterSums.PascadiSingleFibreInventory
