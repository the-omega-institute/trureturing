import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel PhysicalWindowDecoder OriginalNarrowCost
open FirstWindowBoundaryAttainment GlobalPresetObstruction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := Σ m : ℕ, Σ _v : ZMod 2, Σ _j : Phase m, ℕ
  State p := List (Fin p.1 → Bool)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := NarrowWindowCost.Archive p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ ⟨_m, v, j, s⟩ bs => scriptArchive bs (some ⟨v, -j, s⟩))
  (fun e => nomatch e)
def emptyArchive : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (table : Phase m → Pair)
    (outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → table j = 0)
    (label : ZMod 2 → Pair → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = label v (table j)),
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 3 ∧
    (words m table)[1]? = some (pulse m) ∧
    ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      endpointDifferences (some v)
        ((R.readout () ⟨m, v, j, s⟩ (words m table)).map Prod.snd) = code m table j ∧
      (R.readout () ⟨m, v, j, s⟩ (words m table)).length = 3 ∧
      ((R.readout () ⟨m, v, j, s⟩ (words m table)).flatMap
        (fun a => List.ofFn a.1)).length = 3 * m

private theorem positive : arena.{u}.Law actual := original_first_window_three_block_stream
private theorem negative : ¬ arena.{u}.Law emptyArchive := by
  intro law
  have bad := (law 5 (by omega) false (fun _ => (PUnit.unit : PUnit.{u + 1}))
    (fun _ => 0) (by intros; rfl) (fun _ _ => PUnit.unit) (by intros; rfl)).2.2
    0 0 0 (by omega)
  have impossible := bad.2.1
  change (0 : ℕ) = 3 at impossible
  omega

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.original_first_window_three_block_stream.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, emptyArchive, negative⟩
  sensitivity := ⟨fun i => ⟨emptyArchive,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨5, 0, 0, 0⟩, [], [fun _ => false], ?_⟩
    intro same
    have length := congrArg List.length same
    change (0 : ℕ) = 1 at length
    omega

#print axioms evidence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.original_first_window_three_block_stream.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.original_first_window_three_block_stream
    "Reg/D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment,
    definition := none,
    coordinates := #[1, 9, 10, 11],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"],
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"],
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
namespace BinaryAudit

@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun m => List (Fin m → Bool)) (fun _ => Nat)

def actual : Realization signature := realize signature
  (fun _ _ bs => bs.length) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 3) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : Finset ℕ) (inside : ∀ h ∈ H, 1 ≤ h ∧ h ≤ m)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (label : ZMod 2 → ZMod 2 → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = label v (supportRow H j.val)),
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (binaryCost H) ∧
    R.readout () m (binaryWords m H) = binaryCost H ∧
    (∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      endpointDifferences (some v)
        ((scriptArchive (binaryWords m H) (some ⟨v, -j, s⟩)).map Prod.snd) = binaryCode m H j ∧
      (scriptArchive (binaryWords m H) (some ⟨v, -j, s⟩)).length = binaryCost H ∧
      ((scriptArchive (binaryWords m H) (some ⟨v, -j, s⟩)).flatMap
        (fun a => List.ofFn a.1)).length = binaryCost H * m) ∧
    (∀ (v : ZMod 2), label v 0 ≠ label v 1 →
      ∀ (π : NarrowWindowCost.Selector m Y), FiberCorrect m hm alphabet f v 0 π → H = ∅) ∧
    (H.Nonempty → ∀ (v : ZMod 2), label v 0 ≠ label v 1 →
      ∀ (π : NarrowWindowCost.Selector m Y), FiberCorrect m hm alphabet f v 1 π →
      ∃ W : Fin m → Bool, π (some v) [] = .inr W ∧
        W ⟨0, by omega⟩ = false ∧
        (∀ j : Phase m, wordIncrement (2 * m - 2) (-j) W = supportRow H j.val) ∧
        Even H.card)

private theorem positive : arena.{u}.Law actual := original_first_window_binary_stream
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  have bad := (law 5 (by omega) false ∅ (by simp)
    (fun _ => (PUnit.unit : PUnit.{u + 1})) (fun _ _ => PUnit.unit) (by intros; rfl)).2.1
  change (3 : ℕ) = 0 at bad
  omega

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.original_first_window_binary_stream.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, [], [fun _ => false], ?_⟩
    change (0 : ℕ) ≠ 1
    omega

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.original_first_window_binary_stream.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.original_first_window_binary_stream
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment/BinaryAudit.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.BinaryAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment,
    definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end BinaryAudit

namespace SupportSumAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun _ => Finset ℕ) (fun _ => ZMod 2)
def actual : Realization signature := realize signature
  (fun _ m H => ∑ h ∈ Finset.range (m + 1), supportRow H h) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (H : Finset ℕ) (inside : ∀ h ∈ H, h ≤ m),
    R.readout () m H = (H.card : ZMod 2)
private theorem positive : arena.Law actual := support_sum
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := law 1 ∅ (by simp)
  change (1 : ZMod 2) = 0 at bad
  exact one_ne_zero bad

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.support_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨1, ∅, {1}, ?_⟩
    change (∑ h ∈ Finset.range 2, supportRow ∅ h) ≠ ∑ h ∈ Finset.range 2, supportRow {1} h
    decide +kernel

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.support_sum)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.support_sum
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.SupportSumAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.SupportSumAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment, definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration

end SupportSumAudit

namespace ShiftValueAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _m : ℕ, ℕ) (fun p => Phase p.1) (fun _ => Nat)
def actual : Realization signature := realize signature
  (fun _ ⟨m, a⟩ j => ZMod.val (n := 2 * m - 2 + 1) (j - (a : ℕ))) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m a : ℕ) (_hm : 5 ≤ m) (ha : a < 2 * m - 2 + 1) (j : Phase m),
    R.readout () ⟨m, a⟩ j = if a ≤ j.val then j.val - a else j.val + (2 * m - 2 + 1) - a
private theorem positive : arena.Law actual := shift_value
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := law 5 0 (by omega) (by omega) 0
  change (1 : ℕ) = 0 at bad
  omega

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.shift_value)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨⟨5, 0⟩, 0, 1, ?_⟩
    change ((0 : Phase 5) - 0).val ≠ ((1 : Phase 5) - 0).val
    decide +kernel

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.shift_value)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.shift_value
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.ShiftValueAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.ShiftValueAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment, definition := none, coordinates := #[0, 1, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := some #["arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration

end ShiftValueAudit

namespace BinarySeparationAudit
@[reducible] def signature : Signature := Reg.Support.SingleDependentReadout.signature (Σ m : ℕ, Finset ℕ) (fun p => Phase p.1) (fun _ => List (Option (ZMod 2)))
def actual : Realization signature := realize signature (fun _ p j => binaryCode p.1 p.2 j) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 5 ≤ m) (H : Finset ℕ)
    (inside : ∀ h ∈ H, 1 ≤ h ∧ h ≤ m)
    (j l : Phase m) (same : R.readout () ⟨m, H⟩ j = R.readout () ⟨m, H⟩ l),
    supportRow H j.val = supportRow H l.val
private theorem positive : arena.Law actual := binary_separates
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := law 5 (by omega) {1, 2} (by intro h hh; simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with rfl | rfl <;> omega) 0 1 rfl
  change (0 : ZMod 2) = 1 at bad
  exact zero_ne_one bad

def evidence : Registration arena (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.binary_separates)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨⟨5, {1, 2}⟩, 0, 1, ?_⟩
    change binaryCode 5 {1, 2} 0 ≠ binaryCode 5 {1, 2} 1
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.binary_separates) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.binary_separates "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.BinarySeparationAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.BinarySeparationAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 2, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end BinarySeparationAudit

namespace CodeSeparationAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ m : ℕ, Phase m → Pair)
    (fun p => Phase p.1) (fun _ => List (Option (ZMod 2)))
def actual : Realization signature := realize signature
  (fun _ p j => code p.1 p.2 j) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (table : Phase m → Pair)
    (outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → table j = 0)
    (j l : Phase m) (same : R.readout () ⟨m, table⟩ j = R.readout () ⟨m, table⟩ l),
    table j = table l
private theorem positive : arena.Law actual := code_separates
private theorem negative : ¬ arena.Law rejected := by
  intro law
  let table : Phase 5 → Pair := fun j => if j.val = 1 then (1, 0) else 0
  have outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ 5) → table j = 0 := by
    intro j h; simp [table, show j.val ≠ 1 by omega]
  have bad := law 5 table outside 0 1 rfl
  have first := congrArg Prod.fst bad
  change (0 : ZMod 2) = 1 at first
  exact zero_ne_one first

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.code_separates)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨⟨5, fun j => if j.val = 1 then (1, 0) else 0⟩, 0, 1, ?_⟩
    change code 5 _ 0 ≠ code 5 _ 1
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.code_separates)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.code_separates
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.CodeSeparationAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment.CodeSeparationAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "type", "fn", "arg", "fn"],
      stateBinder := 3, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end CodeSeparationAudit

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment
