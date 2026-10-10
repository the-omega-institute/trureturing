import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open OriginalAcquiredTrace GlobalPresetObstruction DonorCorrection NearCriticalGrid
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := ℕ × ℕ
  State rm := Option (LiveRecord (2 * rm.2 - 2))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ rm q => fee (4 * rm.1 - 1) q) (fun e => nomatch e)
def oracle : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R :=  ∀ {Y : Type u} (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (alphabet : Bool)
    (labels : Fin (2 ^ r) → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (target : GridTarget r m labels f),
    GlobalAdaptivePrice (2 * m - 2) m (by omega) alphabet f = (2 * r - 1 : ℕ) ∧
    GlobalPresetPrice (2 * m - 2) m (by omega) alphabet f = (4 * r - 1 : ℕ) ∧
    OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f (2 * r - 1) ∧
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (4 * r - 1) ∧
    FourLabelPaidFeedback.OriginalSelectedPresetFeasible (2 * m - 2) m (by omega)
      alphabet f (2 * r - 1) ∧
    (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      (∃ issued : NarrowWindowCost.Archive m, OriginalAcquiredTrace.PaidTrace (adaptiveSelector (r := r) (m := m) labels (f none))
        free q [] issued (f q) ∧ issued.length = fee (2 * r - 1) q ∧
        (OriginalAcquiredTrace.archiveWords issued).length = m * fee (2 * r - 1) q ∧
        none ∉ issued.map Prod.snd) ∧
      (∃ issued : NarrowWindowCost.Archive m, OriginalAcquiredTrace.PaidTrace
        (presetSelector (commonStream r m) (commonStop (r := r) (m := m) labels (f none)))
        free q [] issued (f q) ∧ issued.length = R.readout () (r, m) q ∧
        (OriginalAcquiredTrace.archiveWords issued).length = m * fee (4 * r - 1) q ∧
        none ∉ issued.map Prod.snd)) ∧
    ∀ v : ZMod 2, ∃ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      q = some ⟨v, -gridPhase r m 0 0, 0⟩ ∧ ∃ ad pre : NarrowWindowCost.Archive m,
        OriginalAcquiredTrace.PaidTrace (adaptiveSelector (r := r) (m := m) labels (f none)) free q [] ad (f q) ∧
        (OriginalAcquiredTrace.archiveWords ad).length = m * (2 * r - 1) ∧
        OriginalAcquiredTrace.PaidTrace
          (presetSelector (commonStream r m) (commonStop (r := r) (m := m) labels (f none))) free q [] pre (f q) ∧
        (OriginalAcquiredTrace.archiveWords pre).length = m * (4 * r - 1)

private theorem positive : arena.{u}.Law actual := original_near_critical_grid_law

def sampleValue (v : ZMod 2) (j : ZMod 139) : Fin 8 :=
  if 6 ≤ j.val ∧ j.val < 70 then
    if v = 0 then ⟨((j.val - 6) / 8) % 8, Nat.mod_lt _ (by omega)⟩
    else ⟨(j.val - 6) % 8, Nat.mod_lt _ (by omega)⟩
  else 0

def sampleTarget : Option (LiveRecord 138) → ULift.{u} (Fin 8)
  | none => ⟨0⟩
  | some q => ⟨sampleValue q.value (-q.phase)⟩

set_option maxRecDepth 8192 in
private theorem sample_target : GridTarget 3 70 (fun a => (ULift.up a : ULift.{u} (Fin 8))) sampleTarget := by
  have grid : ∀ (v : ZMod 2) (p q : Fin 8),
      sampleValue v (gridPhase 3 70 p q) = if v = 0 then p else q := by decide
  have outside : ∀ (v : ZMod 2) (j : ZMod 139),
      (∀ p q : Fin 8, j ≠ gridPhase 3 70 p q) → sampleValue v j = 0 := by decide
  constructor
  · intro v p q s hs
    simp only [sampleTarget, neg_neg, grid]
  · intro v j s hs off
    simp only [sampleTarget, neg_neg, outside v j off]

private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have bad := law 3 70 (by omega) (by norm_num) false
    (fun a => (ULift.up a : ULift.{u} (Fin 8)))
    (by intro a b eq; exact congrArg ULift.down eq) sampleTarget sample_target
  obtain ⟨issued, _, count, bits, _⟩ := (bad.2.2.2.2.2.1 []).2
  change issued.length = 0 at count
  have size := archive_length issued
  rw [count] at size
  rw [size] at bits
  simp only [List.flatMap_nil] at bits
  have empty : OriginalRecord 138 (by omega) [] = some ⟨0, 0, 0⟩ := rfl
  change 0 * 70 = 70 * fee 11 (OriginalRecord 138 (by omega) []) at bits
  rw [empty] at bits
  norm_num [fee] at bits

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.original_near_critical_grid_law.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨(3, 70), none, some ⟨0, 0, 0⟩, ?_⟩
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.original_near_critical_grid_law.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.original_near_critical_grid_law,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.evidence,
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
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid,
    definition := none,
    coordinates := #[1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "body", "body", "arg", "arg", "body", "arg", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration

namespace Adaptive
@[reducible] def signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ d => d) (fun e => nomatch e)
def oracle : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R :=  ∀ {Y : Type u} (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (alphabet : Bool)
    (labels : Fin (2 ^ r) → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (target : GridTarget r m labels f)
    (d : ℕ) (feasible : OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f d),
    2 * r - 1 ≤ R.readout () (r, m) d
private theorem positive : arena.{u}.Law actual := original_grid_adaptive_lower
private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have upper := original_near_critical_grid_law 3 70 (by omega) (by norm_num) false
    (fun a => (ULift.up a : ULift.{u} (Fin 8)))
    (by intro a b eq; exact congrArg ULift.down eq) sampleTarget sample_target
  have bad := law 3 70 (by omega) (by norm_num) false
    (fun a => (ULift.up a : ULift.{u} (Fin 8)))
    (by intro a b eq; exact congrArg ULift.down eq) sampleTarget sample_target
    5 upper.2.2.1
  norm_num [oracle, realize, signature] at bad

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.original_grid_adaptive_lower.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    exact ⟨(3, 70), 0, 1, by decide⟩

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.original_grid_adaptive_lower.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.original_grid_adaptive_lower,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.Adaptive.evidence,
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
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid,
    definition := none,
    coordinates := #[1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 10,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms evidence
#print axioms registration
end Adaptive

namespace Preset
@[reducible] def signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ d => d) (fun e => nomatch e)
def oracle : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R :=  ∀ {Y : Type u} (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (alphabet : Bool)
    (labels : Fin (2 ^ r) → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (target : GridTarget r m labels f)
    (d : ℕ) (feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f d),
    4 * r - 1 ≤ R.readout () (r, m) d
private theorem positive : arena.{u}.Law actual := original_grid_preset_lower
private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have upper := original_near_critical_grid_law 3 70 (by omega) (by norm_num) false
    (fun a => (ULift.up a : ULift.{u} (Fin 8)))
    (by intro a b eq; exact congrArg ULift.down eq) sampleTarget sample_target
  have bad := law 3 70 (by omega) (by norm_num) false
    (fun a => (ULift.up a : ULift.{u} (Fin 8)))
    (by intro a b eq; exact congrArg ULift.down eq) sampleTarget sample_target
    11 upper.2.2.2.1
  norm_num [oracle, realize, signature] at bad

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.original_grid_preset_lower.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    exact ⟨(3, 70), 0, 1, by decide⟩

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.original_grid_preset_lower.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.original_grid_preset_lower,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid.Preset.evidence,
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
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid,
    definition := none,
    coordinates := #[1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 10,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms evidence
#print axioms registration
end Preset
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid
