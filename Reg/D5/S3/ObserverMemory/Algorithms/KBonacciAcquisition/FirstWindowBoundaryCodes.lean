import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder OriginalNarrowCost
open FirstWindowBoundaryAttainment FirstWindowBoundaryCodes GlobalPresetObstruction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace BoundaryRowsAudit
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
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v) ,
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 →
      ∃ (stream : ℕ → Fin m → Bool)
        (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
        (∀ v, FiberCorrect m hm alphabet f v 2 (presetSelector stream stop)) ∧
        ((H 0).Nonempty → stop (some 0) [] = none ∧ stream 0 ⟨0, by omega⟩ = false ∧
          ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → firstCharge m stream j = 0) ∧
        (∀ j, 2 ≤ j.val → j.val < m → secondCharge m stream j = 0) ∧
        (∑ j, firstCharge m stream j) = 0 ∧ (∑ j, secondCharge m stream j) = 0 ∧
        (∀ p q, firstCharge m stream p = firstCharge m stream q →
          secondCharge m stream p = secondCharge m stream q → membership m H p = membership m H q) ∧
        (internalImage m H).card ≤ 2) ∧
    R.readout () m (homogeneousWords m) = 2 ∧
    ((internalImage m H).card = 1 →
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (homogeneousWords m) (some ⟨v, -j, s⟩)).map Prod.snd) = homogeneousCode m j ∧
        (scriptArchive (homogeneousWords m) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (homogeneousWords m) (some ⟨v, -j, s⟩)).flatMap
          (fun a => List.ofFn a.1)).length = 2 * m)
private theorem positive : arena.{u}.Law actual := original_first_window_boundary_rows
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  have bad := (law 5 (by omega) false (fun _ => ∅) (by simp)
    (fun _ => (ULift.up (0 : ZMod 2) : ULift.{u} (ZMod 2)))
    (fun _ => ULift.up (1 : ZMod 2)) (by intro v h; have := congrArg ULift.down h; exact zero_ne_one this)
    (fun _ => ULift.up (0 : ZMod 2)) (by simp)).2.1
  change (3 : ℕ) = 2 at bad
  omega

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.original_first_window_boundary_rows.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, [], [fun _ => false], ?_⟩
    change (0 : ℕ) ≠ 1
    omega

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.original_first_window_boundary_rows.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.original_first_window_boundary_rows
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.BoundaryRowsAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.BoundaryRowsAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration

end BoundaryRowsAudit
namespace NonbaseInternalAudit
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
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (three : (fullImage m H).card = 3) (two : (internalImage m H).card = 2)
    (nonbase : (0 : Pair) ∉ internalImage m H)
    ,
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 →
      Odd m ∨ membership m H (1 : ℕ) ≠ 0 ∨ membership m H (m : ℕ) ≠ 0) ∧
    ((Odd m ∨ membership m H (1 : ℕ) ≠ 0 ∨ membership m H (m : ℕ) ≠ 0) →
    ∃ (S : Finset ℕ) (flip : ZMod 2) (left right : Pair),
      (∀ h ∈ S, 2 ≤ h ∧ h < m) ∧
      (S.card : ZMod 2) + flip * (m : ℕ) + left.1 + right.1 = 0 ∧
      (m : ZMod 2) + 1 + left.2 + right.2 = 0 ∧
      R.readout () m (nonbaseWords m S flip left right) = 2 ∧
      (∀ p q, nonbaseCode m S flip left right p = nonbaseCode m S flip left right q →
        membership m H p = membership m H q) ∧
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (nonbaseWords m S flip left right) (some ⟨v, -j, s⟩)).map Prod.snd) =
          [some (nonbaseCode m S flip left right j).1, some (nonbaseCode m S flip left right j).2] ∧
        (scriptArchive (nonbaseWords m S flip left right) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (nonbaseWords m S flip left right) (some ⟨v, -j, s⟩)).flatMap
          (fun a => List.ofFn a.1)).length = 2 * m)
private theorem positive : arena.{u}.Law actual := original_first_window_nonbase_internal_stream
private def sampleSupport (v : ZMod 2) : Finset ℕ := if v = 0 then {2} else {3, 4}
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  let f : Option (LiveRecord 8) → ULift.{u} (ZMod 2) := fun q =>
    match q with
    | none => ULift.up 0
    | some q => ULift.up (supportRow (sampleSupport q.value) (-q.phase).val)
  have inside : ∀ v h, h ∈ sampleSupport v → 1 ≤ h ∧ h ≤ 5 := by
    intro v h mem
    unfold sampleSupport at mem
    by_cases zero : v = 0
    · rw [if_pos zero] at mem
      simp only [Finset.mem_singleton] at mem
      omega
    · rw [if_neg zero] at mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at mem
      rcases mem with rfl | rfl <;> omega
  have target : ∀ (v : ZMod 2) (j : Phase 5) (s : ℕ), s < 8 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ sampleSupport v then ULift.up 1 else ULift.up 0 := by
    intro v j s hs
    simp only [f, neg_neg, supportRow]
    split_ifs <;> rfl
  obtain ⟨S, flip, left, right, _, _, _, bad, _⟩ := (law 5 (by omega) false sampleSupport inside
    (fun _ => (ULift.up (0 : ZMod 2) : ULift.{u} (ZMod 2))) (fun _ => ULift.up 1)
    (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target
    (by decide) (by decide) (by decide)).2 (Or.inl (by decide))
  change (3 : ℕ) = 2 at bad
  omega

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.original_first_window_nonbase_internal_stream.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, [], [fun _ => false], ?_⟩
    change (0 : ℕ) ≠ 1
    omega

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.original_first_window_nonbase_internal_stream.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.original_first_window_nonbase_internal_stream
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.NonbaseInternalAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.NonbaseInternalAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes,
    definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end NonbaseInternalAudit

namespace NonbaseEvenAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun _ => ℕ → ZMod 2) (fun _ => ZMod 2)
def actual : Realization signature := realize signature
  (fun _ m q => ∑ h ∈ Finset.range (m + 1), q h) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 5 ≤ m) (S : Finset ℕ)
    (inside : ∀ h ∈ S, 2 ≤ h ∧ h < m) (flip : ZMod 2) (left right : Pair)
    (first : (S.card : ZMod 2) + flip * (m : ℕ) + left.1 + right.1 = 0)
    (second : (m : ZMod 2) + 1 + left.2 + right.2 = 0),
    R.readout () m (nonbaseRoot m S flip left right) = 0 ∧
    (∑ h ∈ Finset.range (m + 1), nonbaseSecond m left right h) = 0 ∧
    nonbaseRoot m S flip left right 0 = 0
private theorem positive : arena.Law actual := nonbase_even
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := (law 5 (by omega) ∅ (by simp) 0 (0, 0) (0, 0) (by simp) (by decide)).1
  change (1 : ZMod 2) = 0 at bad
  exact one_ne_zero bad

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.nonbase_even)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨0, fun _ => 0, fun _ => 1, ?_⟩
    change (0 : ZMod 2) ≠ 1
    exact zero_ne_one

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.nonbase_even)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.nonbase_even
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.NonbaseEvenAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.NonbaseEvenAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end NonbaseEvenAudit

namespace NonbaseChargesAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ m : ℕ, Phase m) (fun _ => ℕ → ZMod 2) (fun _ => ZMod 2)
def actual : Realization signature := realize signature
  (fun _ p q => windowCharge (2 * p.1 - 2) p.1 q p.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 5 ≤ m) (S : Finset ℕ)
    (inside : ∀ h ∈ S, 2 ≤ h ∧ h < m) (flip : ZMod 2) (left right : Pair)
    (j : Phase m),
    (R.readout () ⟨m, j⟩ (nonbaseRoot m S flip left right),
     windowCharge (2 * m - 2) m (nonbaseSecond m left right) (j - (m : ℕ))) =
      nonbaseCode m S flip left right j
private theorem positive : arena.Law actual := nonbase_charges
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := congrArg Prod.fst (law 5 (by omega) ∅ (by simp) 0 (0, 0) (0, 0) 0)
  change (1 : ZMod 2) = (nonbaseCode 5 ∅ 0 (0, 0) (0, 0) 0).1 at bad
  have zero : (nonbaseCode 5 ∅ 0 (0, 0) (0, 0) 0).1 = 0 := by simp [nonbaseCode]
  rw [zero] at bad
  exact one_ne_zero bad

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.nonbase_charges)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨⟨5, 1⟩, fun _ => 0, fun _ => 1, ?_⟩
    change windowCharge 8 5 (fun _ => 0) 1 ≠ windowCharge 8 5 (fun _ => 1) 1
    simp [windowCharge, show (1 : Phase 5).val ≤ 5 by decide]

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.nonbase_charges)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.nonbase_charges
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.NonbaseChargesAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.NonbaseChargesAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes,
    definition := none, coordinates := #[0, 7],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end NonbaseChargesAudit

namespace ClassRestoreAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Pair × Pair) (fun _ => Fin 3) (fun _ => Pair)
def actual : Realization signature := realize signature
  (fun _ p i => classLabel p.1 p.2 i) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (X Y z : Pair) (Xzero : X ≠ 0) (Yzero : Y ≠ 0)
    (different : X ≠ Y) (member : z = 0 ∨ z = X ∨ z = Y),
    R.readout () (X, Y) (classIndex X z) = z
private theorem positive : arena.Law actual := class_restore
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := law (1, 0) (0, 1) (1, 0) (by decide) (by decide) (by decide) (Or.inr (Or.inl rfl))
  have badFirst := congrArg Prod.fst bad
  change (0 : ZMod 2) = 1 at badFirst
  exact zero_ne_one badFirst

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.class_restore)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨((1, 0), (0, 1)), 0, 1, ?_⟩
    change classLabel (1, 0) (0, 1) 0 ≠ classLabel (1, 0) (0, 1) 1
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.class_restore)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.class_restore
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.ClassRestoreAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.ClassRestoreAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end ClassRestoreAudit

namespace HomogeneousSeparationAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun m => Phase m)
    (fun _ => List (Option (ZMod 2)))
def actual : Realization signature := realize signature
  (fun _ m j => homogeneousCode m j) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 5 ≤ m) (table : Phase m → Pair)
    (outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → table j = 0)
    (homogeneous : ∀ p q, 2 ≤ p.val → p.val < m → 2 ≤ q.val → q.val < m → table p = table q)
    (j l : Phase m) (same : R.readout () m j = R.readout () m l),
    table j = table l
private theorem positive : arena.Law actual := homogeneous_separates
private theorem negative : ¬ arena.Law rejected := by
  intro law
  let table : Phase 5 → Pair := fun j => if j.val = 1 then (1, 0) else 0
  have outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ 5) → table j = 0 := by
    intro j h; simp [table, show j.val ≠ 1 by omega]
  have homogeneous : ∀ p q, 2 ≤ p.val → p.val < 5 → 2 ≤ q.val → q.val < 5 → table p = table q := by
    intro p q a b c d; simp [table, show p.val ≠ 1 by omega, show q.val ≠ 1 by omega]
  have bad := law 5 (by omega) table outside homogeneous 0 1 rfl
  have first := congrArg Prod.fst bad
  change (0 : ZMod 2) = 1 at first
  exact zero_ne_one first

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.homogeneous_separates)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, 0, 1, ?_⟩
    change homogeneousCode 5 0 ≠ homogeneousCode 5 1
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.homogeneous_separates)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.homogeneous_separates
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.HomogeneousSeparationAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes.HomogeneousSeparationAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "type", "fn", "arg", "fn"],
      stateBinder := 5, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end HomogeneousSeparationAudit

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes
