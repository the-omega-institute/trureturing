import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.StructureGraphs.ChernevExtensionFieldCycles
import Reg.Support.DependentFamily

/-! Source-bound registration of the prime power in the field-cardinality premise. -/

namespace Reg.D5.S3.FiniteGroups.StructureGraphs.ChernevExtensionFieldCycles

open Trureturing.StructureGraphCycles
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => p ^ n) (fun e => nomatch e)

def constantTwo : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : Type) [Field K] [Fintype K] (p n : ℕ),
    Nat.Prime p → 1 < n → Fintype.card K = R.readout () p n → Fintype.card K ≠ 4 →
      ∃ (r : ℕ) (v : Fin r → K × K), 1 < r ∧ IsDirectedCycle (structureGraph K) r v

private theorem constant_two_fails : ¬ arena.Law constantTwo := by
  intro h
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, v, hr, _, hinj, hedge⟩ :=
    h (ZMod 2) 2 2 Nat.prime_two (by decide) (ZMod.card 2)
      (by rw [ZMod.card]; decide)
  let : NeZero r := ⟨by omega⟩
  have hval : (1 : Fin r).val = 1 := by
    rw [Fin.val_one' r, Nat.mod_eq_of_lt hr]
  have step (i : Fin r) : phi (v i) = v (i + 1) := by
    apply hedge i (i + 1)
    rw [Fin.val_add, hval]
  have stable : ∀ x : ZMod 2 × ZMod 2, phi (phi (phi x)) = phi (phi x) := by
    decide
  let j : Fin r := (0 + 1) + 1
  have hj : phi (v j) = v j := by
    change phi (v ((0 + 1) + 1)) = v ((0 + 1) + 1)
    rw [← step (0 + 1), ← step 0]
    exact stable _
  have heq : j + 1 = j := hinj ((step j).symm.trans hj)
  have hone : (1 : Fin r) = 0 := add_left_cancel (heq.trans (add_zero j).symm)
  have hzero : (0 : Fin r).val = 0 := Fin.val_zero r
  exact Nat.one_ne_zero (hval.symm.trans ((congrArg Fin.val hone).trans hzero))

def sourceRegistration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, constantTwo, constant_two_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨constantTwo, ?_, rfl, constant_two_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    exact ⟨2, 2, 3, by decide⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@result) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.StructureGraphs.ChernevExtensionFieldCycles.unit
  realizationName := `Reg.D5.S3.FiniteGroups.StructureGraphs.ChernevExtensionFieldCycles.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => p ^ n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.StructureGraphs.ChernevExtensionFieldCycles
    definition := some {
      owner := `D5.S3.FiniteGroups.StructureGraphs.ChernevExtensionFieldCycles
      name := `Trureturing.StructureGraphCycles.claim
      path := #[] }
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.FiniteGroups.StructureGraphs.ChernevExtensionFieldCycles
