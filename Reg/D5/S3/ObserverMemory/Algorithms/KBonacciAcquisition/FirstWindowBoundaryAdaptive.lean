import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder OriginalNarrowCost
open FirstWindowBoundaryAdaptive FirstWindowBoundaryAttainment GlobalPresetObstruction
open DonorCorrection OriginalAcquiredTrace OriginalExecutionBridge
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace AdaptivePriceAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun _ => ZMod 2 → Finset ℕ) (fun _ => Nat)
def actual : Realization signature := realize signature
  (fun _ m H => worstCost H) (fun e => nomatch e)
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
    GlobalAdaptivePrice (2 * m - 2) m (by omega) alphabet f = (R.readout () m H : ℕ∞) ∧
    (∀ d, OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f d ↔ R.readout () m H ≤ d) ∧
    FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet
      (adaptiveSelector m H A B (f none)) ∧
    adaptiveSelector m H A B (f none) none [] = .inl (f none) ∧
    (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      ∃ issued, PaidTrace (adaptiveSelector m H A B (f none)) free q [] issued (f q) ∧
        issued.map Prod.fst = q.elim [] (fun q => binaryWords m (H q.value)) ∧
        issued.length = sourceCost H q ∧ (archiveWords issued).length = m * sourceCost H q ∧
      none ∉ issued.map Prod.snd) ∧
    (∃ (v : ZMod 2) (history : List (AllowedBlock (2 * m - 2) m alphabet))
      (issued : NarrowWindowCost.Archive m),
      OriginalRecord (2 * m - 2) (by omega) (history.flatMap (fun a => List.ofFn a.val)) =
        some ⟨v, 0, 0⟩ ∧
      PaidTrace (k := 2 * m - 2) (adaptiveSelector m H A B (f none)) (some v) (some ⟨v, 0, 0⟩) [] issued
        (f (some ⟨v, 0, 0⟩)) ∧
      issued.length = R.readout () m H ∧ (archiveWords issued).length = m * R.readout () m H) ∧
    (∀ b, AdaptiveBitFeasible m hm alphabet f b ↔ m * R.readout () m H ≤ b)
private theorem positive : arena.{u}.Law actual := original_first_window_adaptive_price
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
  have good := (positive 5 (by omega) false H inside
    (fun _ => ULift.up 0) (fun _ => ULift.up 1)
    (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target).1
  have price : (worstCost H : ℕ∞) = 0 := good.symm.trans bad
  have count : worstCost H = 1 := by decide
  rw [count] at price
  exact one_ne_zero price

def evidence : Registration arena.{u} (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.original_first_window_adaptive_price.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, (fun _ => ∅), (fun _ => {1, 2}), ?_⟩
    change worstCost (fun _ => ∅) ≠ worstCost (fun _ => {1, 2})
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.original_first_window_adaptive_price.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.original_first_window_adaptive_price
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.AdaptivePriceAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.AdaptivePriceAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end AdaptivePriceAudit
namespace DifferencesLiveAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ZMod 2)
    (fun _ => List (Option (ZMod 2))) (fun _ => List (Option (ZMod 2)))
def actual : Realization signature := realize signature
  (fun _ v replies => endpointDifferences (some v) replies) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (v : ZMod 2) (replies : List (Option (ZMod 2)))
    (live : none ∉ R.readout () v replies), none ∉ replies
private theorem positive : arena.Law actual := differences_live
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := law 0 [none] (by simp [rejected, realize])
  exact bad (by simp)

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.differences_live)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨0, [], [none], ?_⟩
    change endpointDifferences (some 0) [] ≠ endpointDifferences (some 0) [none]
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.differences_live)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.differences_live
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.DifferencesLiveAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive.DifferencesLiveAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "type", "arg", "fn", "arg", "fn"],
      stateBinder := 1, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end DifferencesLiveAudit

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive
