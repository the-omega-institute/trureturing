import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells GlobalPresetObstruction OriginalNarrowCost PhysicalWindowDecoder
open OriginalAcquiredTrace DonorCorrection FirstWindowBoundaryAttainment FirstWindowBoundaryCodes
open FirstWindowBoundaryFourLabels FirstWindowBoundaryPrice FirstWindowBoundarySafePrice
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace SafePresetPriceAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun _ => ZMod 2 → Finset ℕ) (fun _ => Nat)
def actual : Realization signature := realize signature
  (fun _ m H => presetCost m H) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u} (m : ℕ) (hm : 5 ≤ m)
    (alphabet : Bool) (H : ZMod 2 → Finset ℕ)
    (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v),
    ∃ (stream : ℕ → Fin m → Bool)
      (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
      FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet (presetSelector stream stop) ∧
      stop none [] = some (f none) ∧
      (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
        let w := history.flatMap (fun a => List.ofFn a.val)
        let q := OriginalRecord (2 * m - 2) (by omega) w
        ∃ issued, PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
          q [] issued (f q) ∧ issued.length = NearCriticalGrid.fee (R.readout () m H) q ∧
          (archiveWords issued).length = m * NearCriticalGrid.fee (R.readout () m H) q ∧
          none ∉ issued.map Prod.snd) ∧
      ∃ (history : List (AllowedBlock (2 * m - 2) m alphabet)) (issued : NarrowWindowCost.Archive m),
        OriginalRecord (2 * m - 2) (by omega) (history.flatMap (fun a => List.ofFn a.val)) =
          some ⟨0, 0, 0⟩ ∧
        PaidTrace (k := 2 * m - 2) (presetSelector stream stop) (some 0) (some ⟨0, 0, 0⟩) [] issued
          (f (some ⟨0, 0, 0⟩)) ∧ issued.length = R.readout () m H ∧
          (archiveWords issued).length = m * R.readout () m H
private theorem positive : arena.{u}.Law actual := original_first_window_safe_preset_price
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
  obtain ⟨stream, stop, lawful, bottom, traces, _⟩ := law 5 (by omega) false H inside
    (fun _ => ULift.up 0) (fun _ => ULift.up 1)
    (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target
  have feasible : OriginalPresetFeasible 8 5 (by omega) false f 0 := by
    refine ⟨stream, stop, lawful, bottom, ?_⟩
    intro history w
    obtain ⟨issued, traced, count, _⟩ := traces history
    have zero : issued.length = 0 := by
      simpa [rejected, realize, NearCriticalGrid.fee] using count
    refine ⟨0, le_rfl, ?_⟩
    rw [execute_paid_trace 8 5 (by omega)]
    exact ⟨issued, traced, zero, le_rfl⟩
  have main := original_first_window_preset_price 5 (by omega) false H inside
    (fun _ => ULift.up 0) (fun _ => ULift.up 1)
    (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target
  have bound := (main.2.1 0).mp feasible
  have image : (fullImage 5 H).card = 2 := by decide
  have cost : presetCost 5 H = 1 := by
    unfold presetCost
    rw [if_neg (by omega), if_pos image]
    decide
  rw [cost] at bound
  omega

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice.original_first_window_safe_preset_price.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, (fun _ => ∅), (fun _ => {1, 2}), ?_⟩
    change presetCost 5 (fun _ => ∅) ≠ presetCost 5 (fun _ => {1, 2})
    have empty : (fullImage 5 (fun _ => ∅)).card = 1 := by decide
    have two : (fullImage 5 (fun _ => {1, 2})).card = 2 := by decide
    unfold presetCost
    rw [if_pos empty, if_neg (by omega), if_pos two]
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice.original_first_window_safe_preset_price.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice.original_first_window_safe_preset_price
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice.SafePresetPriceAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice.SafePresetPriceAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "body", "arg", "fn", "arg", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end SafePresetPriceAudit

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundarySafePrice
