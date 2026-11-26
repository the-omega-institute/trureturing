import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.CharacterSums.PascadiResonantRectangleEnergy
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The actual energy varies with the coefficient on one fixed unit rectangle. -/

namespace Reg.D5.S3.Arith.CharacterSums.PascadiResonantRectangleEnergy

open _root_.D5.S3.Arith.CharacterSums.PascadiDualPivotOrthogonality
open _root_.D5.S3.Arith.CharacterSums.PascadiResonantRectangleEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := LiteralResonantRectangle
  State R := (ZMod (R.p ^ 2) × ZMod (R.p ^ 2)) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ R c => normalizedRectangleEnergy R c) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1126) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (R : LiteralResonantRectangle) (c : (ZMod (R.p ^ 2) × ZMod (R.p ^ 2)) → ℂ),
    (∀ a ∈ R.pivots, ‖c (resonanceReading R.p R.r R.s R.ρ R.σ a)‖ ≤ 1) →
      F.readout () R c ≤ 9 * (R.p : ℝ) * (R.A : ℝ) ^ 2

private def witness : LiteralResonantRectangle where
  p := 5
  A := 5
  prime := by decide
  prime_gt := by decide
  side_lower := by decide
  side_upper := by decide
  L := 1
  M := 1
  r := 1
  s := 1
  ρ := 5
  σ := 0
  determinant := by decide
  primitive := ⟨1, 0, by decide⟩
  g := 3
  h := 3
  g_unit := (ZMod.isUnit_iff_coprime 3 25).2 (by decide)
  pivots := {(1, 1)}
  box := by
    intro a ha
    have e := Finset.mem_singleton.mp ha
    subst a
    decide
  resonance := by
    intro a ha
    have e := Finset.mem_singleton.mp ha
    subst a
    exact ⟨0, by decide⟩
  units := by
    intro a ha
    have e := Finset.mem_singleton.mp ha
    subst a
    exact ⟨isUnit_one, isUnit_one⟩
  χ := fun _ => 1
  mask_bound := by simp

private theorem witness_coeff (b : ℂ) (hb : ‖b‖ ≤ 1) :
    ∀ a ∈ witness.pivots, ‖(fun _ => b) (resonanceReading
      witness.p witness.r witness.s witness.ρ witness.σ a)‖ ≤ 1 := by
  intro _ _
  exact hb

private lemma witness_mem :
    ((1,1) : ZMod 25 × ZMod 25) ∈ actualFiber (p := 5) 1 1 5 0 3 3 (1,0) := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hu : IsUnit (2 : ZMod 25) := (ZMod.isUnit_iff_coprime 2 25).2 (by decide)
  change IsUnit (1 : ZMod 25) ∧ IsUnit (1 : ZMod 25) ∧ IsUnit (1 : ZMod 25) ∧
    IsUnit (1 : ZMod 25) ∧ IsUnit (3 - 1 - 1 : ZMod 25) ∧ IsUnit (1 + 1 : ZMod 25) ∧
    IsUnit (3 - 1 : ZMod 25) ∧ IsUnit (3 - 1 : ZMod 25) ∧
    (3 : ZMod 25) * 1 * 1 * (1 * 1 * (3 - 1 - 1)) = 3
  norm_num
  exact hu

private theorem energy_identity (R : LiteralResonantRectangle)
    (c : (ZMod (R.p ^ 2) × ZMod (R.p ^ 2)) → ℂ) :
    normalizedRectangleEnergy R c =
      ∑ u ∈ R.pivots.image (resonanceReading R.p R.r R.s R.ρ R.σ),
        ‖c u * R.χ u‖ ^ 2 *
          ((let : NeZero (R.p ^ 2) := ⟨pow_ne_zero _ R.prime.ne_zero⟩
            actualFiber (R.r : ZMod (R.p ^ 2)) (R.s : ZMod (R.p ^ 2))
              R.ρ R.σ R.g R.h u).card : ℝ) := by
  classical
  let : NeZero (R.p ^ 2) := ⟨pow_ne_zero _ R.prime.ne_zero⟩
  exact complete_dual_energy _ _ _ _ _ _ R.g_unit _ _
    (fun _ _ _ hz => (Finset.mem_filter.mp hz).2) c R.χ

private theorem witness_positive :
    0 < normalizedRectangleEnergy witness (fun _ => 1) := by
  classical
  let P : Finset (ZMod 25 × ZMod 25) := {(1, 0)}
  let Z := actualFiber (p := 5) 1 1 5 0 3 3
  have he : witness.pivots.image
      (resonanceReading witness.p witness.r witness.s witness.ρ witness.σ) = P := by
    simp only [witness, P]
    congr 1
  rw [energy_identity, he]
  change 0 < ∑ u ∈ P, ‖(1 : ℂ) * 1‖ ^ 2 * ((Z u).card : ℝ)
  simp only [P, Finset.sum_singleton, one_mul, norm_one, one_pow]
  exact_mod_cast Finset.card_pos.mpr ⟨_, witness_mem⟩

private theorem witness_zero : normalizedRectangleEnergy witness (fun _ => 0) = 0 := by
  simp [normalizedRectangleEnergy]


private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h witness (fun _ => 0) (witness_coeff 0 (by simp))
  change (1126 : ℝ) ≤ 9 * (5 : ℕ) * ((5 : ℕ) : ℝ) ^ 2 at hb
  norm_num at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨witness, (fun _ => 0), (fun _ => 1), ?_⟩
  change normalizedRectangleEnergy witness (fun _ => 0) ≠
    normalizedRectangleEnergy witness (fun _ => 1)
  rw [witness_zero]
  exact ne_of_lt witness_positive

def family : Registration arena (type_of% @complete_resonant_rectangle_energy_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_resonant_rectangle_energy_le, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_resonant_rectangle_energy_le) (Realization signature) (Type) Unit where
  unitName :=
    `Reg.D5.S3.Arith.CharacterSums.PascadiResonantRectangleEnergy.unit
  realizationName :=
    `Reg.D5.S3.Arith.CharacterSums.PascadiResonantRectangleEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ R c => normalizedRectangleEnergy R c)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CharacterSums.PascadiResonantRectangleEnergy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Arith.CharacterSums.PascadiResonantRectangleEnergy
