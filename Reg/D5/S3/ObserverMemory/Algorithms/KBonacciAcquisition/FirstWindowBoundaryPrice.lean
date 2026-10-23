import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder OriginalNarrowCost
open FirstWindowBoundaryAttainment FirstWindowBoundaryCodes FirstWindowBoundaryCompatibility FirstWindowBoundaryFourLabels FirstWindowBoundaryPrice GlobalPresetObstruction
open DonorCorrection OriginalAcquiredTrace OriginalExecutionBridge
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace TableExtremesAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun _ => ZMod 2 → Finset ℕ) (fun _ => Nat)
def actual : Realization signature := realize signature
  (fun _ m H => (internalImage m H).card) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (four : (fullImage m H).card = 4),
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ↔ piFour m H) ∧
    (R.readout () m H = 1 → piFour m H) ∧
    (3 ≤ R.readout () m H → ¬ piFour m H)
private theorem positive : arena.{u}.Law actual := original_first_window_table_extremes
private def sampleSupport (v : ZMod 2) : Finset ℕ := if v = 0 then {1, 2} else {2, 3}
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  let f : Option (LiveRecord 8) → ULift.{u} (ZMod 2) := fun q =>
    match q with
    | none => ULift.up 0
    | some q => ULift.up (supportRow (sampleSupport q.value) (-q.phase).val)
  have inside : ∀ v h, h ∈ sampleSupport v → 1 ≤ h ∧ h ≤ 5 := by
    intro v h mem
    unfold sampleSupport at mem
    split_ifs at mem <;> simp only [Finset.mem_insert, Finset.mem_singleton] at mem
    all_goals rcases mem with rfl | rfl <;> omega
  have target : ∀ (v : ZMod 2) (j : Phase 5) (s : ℕ), s < 8 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ sampleSupport v then ULift.up 1 else ULift.up 0 := by
    intro v j s hs
    simp only [f, neg_neg, supportRow]
    split_ifs <;> rfl
  have yes := (law 5 (by omega) false sampleSupport inside
    (fun _ => ULift.up 0) (fun _ => ULift.up 1)
    (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target (by decide)).2.1 rfl
  have no := (positive 5 (by omega) false sampleSupport inside
    (fun _ => ULift.up 0) (fun _ => ULift.up 1)
    (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target (by decide)).2.2
      (by change 3 ≤ (internalImage 5 sampleSupport).card; decide)
  exact no yes

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.original_first_window_table_extremes.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, (fun _ => ∅), sampleSupport, ?_⟩
    change (internalImage 5 (fun _ => ∅)).card ≠ (internalImage 5 sampleSupport).card
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.original_first_window_table_extremes.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.original_first_window_table_extremes
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.TableExtremesAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.TableExtremesAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice,
    definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "type", "fn", "arg", "fn"],
      stateBinder := 4, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end TableExtremesAudit
namespace PresetPriceAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun _ => ZMod 2 → Finset ℕ) (fun _ => Nat)
def actual : Realization signature := realize signature
  (fun _ m H => presetCost m H) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v),
    GlobalPresetPrice (2 * m - 2) m (by omega) alphabet f = (R.readout () m H : ℕ∞) ∧
    (∀ d, OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f d ↔ R.readout () m H ≤ d) ∧
    ((fullImage m H).card = 1 ↔ H 0 = ∅ ∧ H 1 = ∅) ∧
    ((fullImage m H).card = 2 →
      ∃ z : Pair, z ≠ 0 ∧ fullImage m H = {0, z} ∧
        (∀ j : Phase m, membership m H j = if j.val ∈ H 0 ∪ H 1 then z else 0) ∧
        (∀ v : ZMod 2, H v = ∅ ∨ H v = H 0 ∪ H 1) ∧
        ∃ v : ZMod 2, H v = H 0 ∪ H 1) ∧
    ((fullImage m H).card = 4 →
      ((internalImage m H).card = 1 → piFour m H) ∧
      (3 ≤ (internalImage m H).card → ¬ piFour m H) ∧
      (∀ z : Pair, z ≠ 0 → internalImage m H = {0, z} →
        (piFour m H ↔ Odd (internalFiber m H z).card)) ∧
      ((internalImage m H).card = 2 → (0 : Pair) ∉ internalImage m H →
        (piFour m H ↔ Even (boundaryParity m H)))) ∧
    (∀ b, PresetBitFeasible m hm alphabet f b ↔ m * R.readout () m H ≤ b) ∧
    ∃ (stream : ℕ → Fin m → Bool)
      (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
      FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet (presetSelector stream stop) ∧
      stop none [] = some (f none) ∧
      (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
        let w := history.flatMap (fun a => List.ofFn a.val)
        ∃ issued, PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
          (OriginalRecord (2 * m - 2) (by omega) w) [] issued (f (OriginalRecord (2 * m - 2) (by omega) w)) ∧
          issued.length ≤ R.readout () m H ∧ (archiveWords issued).length = m * issued.length) ∧
      ∃ (history : List (AllowedBlock (2 * m - 2) m alphabet)) (issued : NarrowWindowCost.Archive m),
        let w := history.flatMap (fun a => List.ofFn a.val)
        PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
          (OriginalRecord (2 * m - 2) (by omega) w) [] issued (f (OriginalRecord (2 * m - 2) (by omega) w)) ∧
        issued.length = R.readout () m H ∧ (archiveWords issued).length = m * R.readout () m H
private theorem positive : arena.{u}.Law actual := original_first_window_preset_price
set_option maxHeartbeats 800000 in
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  let H : ZMod 2 → Finset ℕ := fun _ => {1, 2}
  let f : Option (LiveRecord 8) → ULift.{u} (ZMod 2) := fun q =>
    q.elim (ULift.up 0) (fun q => ULift.up (supportRow (H q.value) (-q.phase).val))
  have inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ 5 := by
    intro v h mem
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at mem
    rcases mem with rfl | rfl <;> omega
  have target : ∀ (v : ZMod 2) (j : Phase 5) (s : ℕ), s < 8 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then ULift.up 1 else ULift.up 0 := by
    intro v j s hs
    simp only [f, Option.elim_some, neg_neg, supportRow]
    split_ifs <;> rfl
  have bad := (law 5 (by omega) false H inside
    (fun _ => ULift.up 0) (fun _ => ULift.up 1)
    (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target).1
  have image : (fullImage 5 H).card = 2 := by decide
  have cost : presetCost 5 H = 1 := by
    unfold presetCost
    rw [if_neg (by omega), if_pos image]
    decide
  have good := (original_first_window_preset_price 5 (by omega) false H inside
    (fun _ => ULift.up 0) (fun _ => ULift.up 1)
    (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target).1
  have price : (presetCost 5 H : ℕ∞) = 0 := good.symm.trans bad
  rw [cost] at price
  exact one_ne_zero price

def evidence : Registration arena.{u} (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.original_first_window_preset_price.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, (fun _ => ∅), (fun _ => {1, 2}), ?_⟩
    change presetCost 5 (fun _ => ∅) ≠ presetCost 5 (fun _ => {1, 2})
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.original_first_window_preset_price.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.original_first_window_preset_price
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.PresetPriceAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice.PresetPriceAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end PresetPriceAudit

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice
