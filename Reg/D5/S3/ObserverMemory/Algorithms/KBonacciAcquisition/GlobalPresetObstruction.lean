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
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration

end

open OriginalExecutionBridge
open scoped BigOperators


noncomputable section
universe u

namespace NativeZeroAudit
@[reducible] def signature : Signature where
  Params := Σ Y : Type u, Σ k : ℕ, Σ m : ℕ,
    Option (LiveRecord k) × Option (ZMod 2) × NarrowWindowCost.Archive m
  State p := NarrowWindowCost.Selector p.2.2.1 p.1

  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (p.1 × ℕ)

  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ ⟨_Y, _k, _m, q, free, ar⟩ pi => NativeExecute pi (0) q free ar)
  (fun e => nomatch e)
def oracle : Realization signature.{u} := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Y : Type u} {k m : ℕ}
    (pi : NarrowWindowCost.Selector m Y) (q : Option (LiveRecord k))
    (free : Option (ZMod 2)) (ar : NarrowWindowCost.Archive m),
    R.readout () ⟨Y, k, m, q, free, ar⟩ pi = match pi free ar with
      | .inl z => some (z, 0)
      | .inr _ => none
private theorem positive : arena.{u}.Law actual := native_zero
private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have bad := law (k := 2) (m := 1)
    (fun _ _ => .inl (ULift.up false : ULift.{u} Bool)) none none []
  cases bad

def evidence : Registration arena.{u} (type_of% (@native_zero.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, 2, 1, none, none, []⟩,
      (fun _ _ => .inl ⟨false⟩), (fun _ _ => .inl ⟨true⟩), ?_⟩
    intro impossible
    have eq := congrArg (fun r : Option (ULift.{u} Bool × ℕ) => r.map (fun p => p.1.down)) impossible
    cases eq

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.native_zero.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.native_zero
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.NativeZeroAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.NativeZeroAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.NativeZeroAudit.evidence,
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
    coordinates := #[0, 1, 2, 4, 5, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "fn", "fn", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end NativeZeroAudit

namespace NativeSuccAudit
@[reducible] def signature : Signature where
  Params := Σ Y : Type u, Σ k : ℕ, Σ m : ℕ,
    ℕ × Option (LiveRecord k) × Option (ZMod 2) × NarrowWindowCost.Archive m
  State p := NarrowWindowCost.Selector p.2.2.1 p.1

  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (p.1 × ℕ)

  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ ⟨_Y, _k, _m, d, q, free, ar⟩ pi => NativeExecute pi (d + 1) q free ar)
  (fun e => nomatch e)
def oracle : Realization signature.{u} := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Y : Type u} {k m d : ℕ}
    (pi : NarrowWindowCost.Selector m Y) (q : Option (LiveRecord k))
    (free : Option (ZMod 2)) (ar : NarrowWindowCost.Archive m),
    R.readout () ⟨Y, k, m, d, q, free, ar⟩ pi = match pi free ar with
      | .inl z => some (z, 0)
      | .inr B => Option.map (fun r => (r.1, r.2 + 1))
          (NativeExecute pi d (runBits k B q) free
            (ar ++ [(B, endpointReading (runBits k B q))]))
private theorem positive : arena.{u}.Law actual := native_succ
private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have bad := law (k := 2) (m := 1) (d := 0)
    (fun _ _ => .inl (ULift.up false : ULift.{u} Bool)) none none []
  cases bad

def evidence : Registration arena.{u} (type_of% (@native_succ.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, 2, 1, 0, none, none, []⟩,
      (fun _ _ => .inl ⟨false⟩), (fun _ _ => .inl ⟨true⟩), ?_⟩
    intro impossible
    have eq := congrArg (fun r : Option (ULift.{u} Bool × ℕ) => r.map (fun p => p.1.down)) impossible
    cases eq

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.native_succ.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.native_succ
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.NativeSuccAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.NativeSuccAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.NativeSuccAudit.evidence,
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
    coordinates := #[0, 1, 2, 3, 5, 6, 7],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "fn", "fn", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end NativeSuccAudit

namespace NativeTwoSameAudit
open OriginalExecutionBridge
@[reducible] def signature : Signature where
  Params := Σ Y : Type u, Σ k : ℕ, Σ m : ℕ,
    (ℕ → Fin m → Bool) × ZMod 2 × ZMod (k + 1) × ℕ
  State p := Option (ZMod 2) → NarrowWindowCost.Archive p.2.2.1 → Option p.1

  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (p.1 × ℕ)

  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ ⟨_Y, k, _m, stream, v, phase, s⟩ stop =>
    NativeExecute (presetSelector stream stop) 2
      (some (LiveRecord.mk (k := k) v phase s)) (some v) []) (fun e => nomatch e)
def oracle : Realization signature.{u} := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Y : Type u} (k m : ℕ) (hk : 2 ≤ k)
    (stream : ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y)
    (v : ZMod 2) (p q : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (first : wordIncrement k p (stream 0) = wordIncrement k q (stream 0))
    (second : wordIncrement k (p + (m : ℕ)) (stream 1) =
      wordIncrement k (q + (m : ℕ)) (stream 1)),
    R.readout () ⟨Y, k, m, stream, v, p, s⟩ stop =
      NativeExecute (presetSelector stream stop) 2 (some ⟨v, q, s⟩) (some v) []
private theorem positive : arena.{u}.Law actual := native_two_same
private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have bad := law 2 1 (by omega) (fun _ _ => false)
    (fun _ _ => some (ULift.up false : ULift.{u} Bool)) 0 0 0 0 (by omega) rfl rfl
  cases bad

def evidence : Registration arena.{u} (type_of% (@native_two_same.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, 2, 1, (fun _ _ => false), 0, 0, 0⟩,
      (fun _ _ => some ⟨false⟩), (fun _ _ => some ⟨true⟩), ?_⟩
    intro impossible
    have eq := congrArg (fun r : Option (ULift.{u} Bool × ℕ) => r.map (fun p => p.1.down)) impossible
    cases eq

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.native_two_same.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.native_two_same
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.NativeTwoSameAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.NativeTwoSameAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.NativeTwoSameAudit.evidence,
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
    coordinates := #[0, 1, 2, 4, 6, 7, 9],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "fn", "fn", "fn", "arg", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end NativeTwoSameAudit

namespace ChargeEvenAudit
@[reducible] def signature : Signature where
  Params := Σ k : ℕ, Σ _m : ℕ, ZMod (k + 1)
  State p := Fin p.2.1 → Bool

  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod (p.1 + 1) → ZMod 2

  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ ⟨k, _m, shift⟩ word j => wordIncrement k (-j + shift) word)
  (fun e => nomatch e)
def oracle : Realization signature := realize signature
  (fun _ _ _ _ => 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (k m : ℕ) (hk : 2 ≤ k) (shift : ZMod (k + 1)) (word : Fin m → Bool),
    (∑ j : ZMod (k + 1), R.readout () ⟨k, m, shift⟩ word j) = 0
private theorem positive : arena.Law actual := charge_even
private theorem negative : ¬ arena.Law oracle := by
  intro law
  have bad := law 2 1 (by omega) 0 (fun _ => false)
  have impossible : (3 : ZMod 2) = 0 := by simpa [oracle, realize, ZMod.card] using bad
  exact (show (3 : ZMod 2) ≠ 0 by decide) impossible

def evidence : Registration arena (type_of% (@charge_even)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨2, 1, 0⟩, (fun _ => false), (fun _ => true), ?_⟩
    intro impossible
    have eq := congrFun impossible 0
    change wordIncrement 2 0 (fun _ : Fin 1 => false) =
      wordIncrement 2 0 (fun _ : Fin 1 => true) at eq
    exact (by decide : wordIncrement 2 0 (fun _ : Fin 1 => false) ≠
      wordIncrement 2 0 (fun _ : Fin 1 => true)) eq

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.charge_even)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.charge_even
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.ChargeEvenAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.ChargeEvenAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.ChargeEvenAudit.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction,
    definition := none,
    coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end ChargeEvenAudit

namespace SecondChargeBlindAudit
@[reducible] def signature : Signature where
  Params := Σ m : ℕ, ZMod (2 * m - 2 + 1)
  State p := Fin p.1 → Bool

  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2

  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ ⟨m, j⟩ word => wordIncrement (2 * m - 2) (-j + (m : ℕ)) word)
  (fun e => nomatch e)
def oracle : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 5 ≤ m) (word : Fin m → Bool)
    (j : ZMod (2 * m - 2 + 1)) (lo : 2 ≤ j.val) (hi : j.val < m),
    R.readout () ⟨m, j⟩ word = 0
private theorem positive : arena.Law actual := second_charge_blind
private theorem negative : ¬ arena.Law oracle := by
  intro law
  have bad := law 5 (by omega) (fun _ => false) 2 (by decide) (by decide)
  exact one_ne_zero bad

def evidence : Registration arena (type_of% (@second_charge_blind)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨5, 0⟩, (fun _ => false), (fun i => decide (i.val = 4)), ?_⟩
    cases i
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.second_charge_blind)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.second_charge_blind
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.SecondChargeBlindAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.SecondChargeBlindAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.SecondChargeBlindAudit.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction,
    definition := none,
    coordinates := #[0, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end SecondChargeBlindAudit

end
#print axioms _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.native_zero
#print axioms _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.native_succ
#print axioms _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.native_two_same
#print axioms _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.charge_even
#print axioms _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.second_charge_blind

end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction
