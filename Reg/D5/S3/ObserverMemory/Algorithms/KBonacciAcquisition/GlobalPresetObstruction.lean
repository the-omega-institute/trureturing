import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost GlobalPresetObstruction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Tower.DBonacci.Names
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Tower.DBonacciGeneral.UniformBaseGap

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := Σ Y : Type u, {m : ℕ // 5 ≤ m} × Bool
  State p := Option (LiveRecord (2 * p.2.1.val - 2)) → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p f => @decide (OriginalPresetFeasible (2 * p.2.1.val - 2) p.2.1.val
    (by have := p.2.1.property; omega) p.2.2 f 2) (Classical.propDecidable _))
  (fun e => nomatch e)

def oracle : Realization signature.{u} :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset (ZMod (2 * m - 2 + 1)))
    (inside : ∀ v j, j ∈ H v → 2 ≤ j.val ∧ j.val < m)
    (even : ∀ v, Even (H v).card)
    (nonempty : ∀ v, (H v).Nonempty) (unequal : H 0 ≠ H 1)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j ∈ H v then B v else A v),
    ¬ R.readout () ⟨Y, ⟨m, hm⟩, alphabet⟩ f = true

private theorem positive : arena.{u}.Law actual := by
  classical
  intro Y m hm alphabet H inside even nonempty unequal A B distinct f target feasible
  apply original_global_two_block_obstruction m hm alphabet H inside even nonempty
    unequal A B distinct f target
  exact of_decide_eq_true feasible

private def sampleSupports (v : ZMod 2) : Finset (ZMod 9) :=
  if v = 0 then {2, 3} else {2, 4}

def sampleTarget : Option (LiveRecord 8) → ULift.{u} Bool
  | none => ⟨false⟩
  | some q => ⟨decide (-q.phase ∈ sampleSupports q.value)⟩

theorem sample_not_feasible :
    ¬ OriginalPresetFeasible 8 5 (by omega) false sampleTarget.{u} 2 := by
  have inside : ∀ v j, j ∈ sampleSupports v → 2 ≤ j.val ∧ j.val < 5 := by
    decide
  have even : ∀ v, Even (sampleSupports v).card := by decide
  have nonempty : ∀ v, (sampleSupports v).Nonempty := by decide
  have unequal : sampleSupports 0 ≠ sampleSupports 1 := by decide
  have distinct : ∀ _v : ZMod 2, (ULift.up false : ULift.{u} Bool) ≠ ⟨true⟩ := by
    intro v equal
    cases congrArg ULift.down equal
  have target : ∀ (v : ZMod 2) (j : ZMod 9) (s : ℕ), s < 8 →
      sampleTarget (some ⟨v, -j, s⟩) =
        if j ∈ sampleSupports v then (ULift.up true : ULift.{u} Bool) else ⟨false⟩ := by
    intro v j s _
    simp only [sampleTarget, neg_neg]
    by_cases h : j ∈ sampleSupports v
    · rw [if_pos h, decide_eq_true h]
    · rw [if_neg h, decide_eq_false h]
  exact original_global_two_block_obstruction 5 (by omega) false sampleSupports
    inside even nonempty unequal (fun _ => ⟨false⟩) (fun _ => ⟨true⟩)
    distinct sampleTarget target

private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have inside : ∀ v j, j ∈ sampleSupports v → 2 ≤ j.val ∧ j.val < 5 := by
    decide
  have even : ∀ v, Even (sampleSupports v).card := by decide
  have nonempty : ∀ v, (sampleSupports v).Nonempty := by decide
  have unequal : sampleSupports 0 ≠ sampleSupports 1 := by decide
  have distinct : ∀ _v : ZMod 2, (ULift.up false : ULift.{u} Bool) ≠ ⟨true⟩ := by
    intro v equal
    cases congrArg ULift.down equal
  have target : ∀ (v : ZMod 2) (j : ZMod 9) (s : ℕ), s < 8 →
      sampleTarget (some ⟨v, -j, s⟩) =
        if j ∈ sampleSupports v then (ULift.up true : ULift.{u} Bool) else ⟨false⟩ := by
    intro v j s _
    simp only [sampleTarget, neg_neg]
    by_cases h : j ∈ sampleSupports v
    · rw [if_pos h, decide_eq_true h]
    · rw [if_neg h, decide_eq_false h]
  exact law 5 (by omega) false sampleSupports inside even nonempty unequal
    (fun _ => ⟨false⟩) (fun _ => ⟨true⟩) distinct sampleTarget target rfl

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.original_global_two_block_obstruction.{u})) where
  actual := actual
  bridge := by
    classical
    constructor
    · intro source Y m hm alphabet H inside even nonempty unequal A B distinct f target yes
      exact source m hm alphabet H inside even nonempty unequal A B distinct f target
        (of_decide_eq_true yes)
    · intro law Y m hm alphabet H inside even nonempty unequal A B distinct f target feasible
      exact law m hm alphabet H inside even nonempty unequal A B distinct f target
        (decide_eq_true feasible)
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨⟨ULift.{u} Bool, ⟨5, by omega⟩, false⟩, fun _ => ⟨false⟩,
      sampleTarget, ?_⟩
    have yes : OriginalPresetFeasible 8 5 (by omega) false
        (fun _ => (ULift.up false : ULift.{u} Bool)) 2 := by
      refine ⟨fun _ _ => false, fun _ _ => some ⟨false⟩, ?_, rfl, ?_⟩
      · intro free archive B impossible
        simp [presetSelector] at impossible
      · intro history
        exact ⟨0, by omega, rfl⟩
    intro equal
    apply sample_not_feasible.{u}
    exact of_decide_eq_true (equal.symm.trans (decide_eq_true yes))

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.original_global_two_block_obstruction.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.original_global_two_block_obstruction
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction,
    definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction
