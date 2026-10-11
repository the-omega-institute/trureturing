import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse DonorCorrection
open OriginalNarrowCost OwnPathCharges GlobalPresetObstruction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Tower.DBonacci.Names

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

@[reducible] def signature : Signature where
  Params := Σ m : ℕ, Σ _alphabet : Bool, Σ _v : ZMod 2,
    Σ _j : ZMod (2 * m - 2 + 1), ℕ
  State p := List (AllowedBlock (2 * p.1 - 2) p.1 p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List (Option (ZMod 2))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ ⟨_m, _alphabet, v, j, s⟩ actions => fixedBlockArchive actions (some ⟨v, -j, s⟩))
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => [none]) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ),
      s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ) (positive : 1 ≤ d)
    (bound : d ≤ 2 * m - 10)
    (correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c))
    (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ) (hs : s < 2 * m - 2),
    let rows := List.ofFn (fun t : Fin d => codingRow table π d t.val)
    let actions := chargeBlocks (2 * m - 2) m (by omega) (by omega) alphabet rows
    (∀ (t : Fin d) (phase : ZMod (2 * m - 2 + 1)), ¬ Donor m phase →
      windowCharge (2 * m - 2) m (codingRow table π d t.val)
        (phase - ((t.val * m : ℕ) : ZMod (2 * m - 2 + 1))) =
        phaseCharges table π d t.val phase) ∧
    actions.length = d ∧
    R.readout () ⟨m, alphabet, v, j, s⟩ actions =
      chargeArchive (2 * m - 2) m rows v j ∧
    (fixedBlockArchive actions (some ⟨v, -j, s⟩)).length = d ∧
    none ∉ fixedBlockArchive actions (some ⟨v, -j, s⟩)

private theorem positive : arena.Law actual := original_donor_coding_archive
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have instanceLaw := law 6 (by decide) false (fun _ => PUnit.unit)
    (fun _ => PUnit.unit) (by intros; rfl) (fun _ _ => .inl PUnit.unit) 1
    (by decide) (by decide)
    (by intro history; dsimp only; intro _; exact ⟨0, by decide, rfl⟩)
    0 0 0 (by decide)
  have impossible := instanceLaw.2.2.1
  have real := positive 6 (by decide) false (fun _ => PUnit.unit)
    (fun _ => PUnit.unit) (by intros; rfl) (fun _ _ => .inl PUnit.unit) 1
    (by decide) (by decide)
    (by intro history; dsimp only; intro _; exact ⟨0, by decide, rfl⟩)
    0 0 0 (by decide)
  have nativeEq := real.2.2.1
  change fixedBlockArchive _ _ = _ at nativeEq
  apply instanceLaw.2.2.2.2
  rw [nativeEq, ← impossible]
  change none ∈ [none]
  simp

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_donor_coding_archive.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let zero : AllowedBlock 10 6 false := ⟨(fun _ => false), fun _ => by decide⟩
    refine ⟨⟨6, false, 0, 0, 0⟩, [zero], [zero, zero], ?_⟩
    change fixedBlockArchive [zero] (some (⟨0, 0, 0⟩ : LiveRecord 10)) ≠
      fixedBlockArchive [zero, zero] (some (⟨0, 0, 0⟩ : LiveRecord 10))
    intro same
    have length := congrArg List.length same
    simp only [fixedBlockArchive, List.length_cons, List.length_nil] at length
    omega

#print axioms evidence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_donor_coding_archive.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_donor_coding_archive
    "Reg/D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.evidence,
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
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection,
    definition := none,
    coordinates := #[1, 3, 12, 13, 14],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration

@[reducible] def presetSignature : Signature where
  Params := Σ Y : Type u, {m : ℕ // 5 ≤ m} × Bool × ℕ
  State p := Option (LiveRecord (2 * p.2.1.val - 2)) → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def presetActual : Realization presetSignature.{u} := realize presetSignature
  (fun _ p f => @decide (OriginalPresetFeasible (2 * p.2.1.val - 2) p.2.1.val
    (by have := p.2.1.property; omega) p.2.2.1 f p.2.2.2) (Classical.propDecidable _))
  (fun e => nomatch e)

def presetDenied : Realization presetSignature.{u} :=
  realize presetSignature (fun _ _ _ => false) (fun e => nomatch e)

@[reducible] def presetArena : Arena where
  signature := presetSignature.{u}
  Law R := ∀ {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ),
      s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ) (positive : 1 ≤ d)
    (bound : d ≤ 2 * m - 10)
    (correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c)),
    R.readout () ⟨Y, ⟨m, hm⟩, alphabet, d + 4⟩ f = true

private theorem presetPositive : presetArena.{u}.Law presetActual := by
  classical
  intro Y m hm alphabet f table target π d positive bound correct
  exact decide_eq_true (original_donor_preset_feasible m hm alphabet f table target
    π d positive bound correct)

private theorem presetNegative : ¬ presetArena.{u}.Law presetDenied := by
  intro law
  have bad := law 6 (by omega) false
    (fun _ => (ULift.up false : ULift.{u} Bool)) (fun _ => ⟨false⟩)
    (by intros; rfl) (fun _ _ => .inl ⟨false⟩) 1 (by omega) (by omega)
    (by intro history; dsimp only; intro _; exact ⟨0, by omega, rfl⟩)
  change false = true at bad
  cases bad

def presetEvidence : Registration presetArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_donor_preset_feasible.{u})) where
  actual := presetActual
  bridge := by
    classical
    constructor
    · intro source Y m hm alphabet f table target π d positive bound correct
      exact decide_eq_true (source m hm alphabet f table target π d positive bound correct)
    · intro law Y m hm alphabet f table target π d positive bound correct
      exact of_decide_eq_true (law m hm alphabet f table target π d positive bound correct)
  variation := ⟨presetPositive, presetDenied, presetNegative⟩
  sensitivity := ⟨fun i => ⟨presetDenied,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, presetNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨⟨ULift.{u} Bool, ⟨5, by omega⟩, false, 2⟩, fun _ => ⟨false⟩,
      _root_.Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.sampleTarget,
      ?_⟩
    have yes : OriginalPresetFeasible 8 5 (by omega) false
        (fun _ => (ULift.up false : ULift.{u} Bool)) 2 := by
      refine ⟨fun _ _ => false, fun _ _ => some ⟨false⟩, ?_, rfl, ?_⟩
      · intro free archive B impossible
        simp [presetSelector] at impossible
      · intro history
        exact ⟨0, by omega, rfl⟩
    intro equal
    apply _root_.Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.sample_not_feasible.{u}
    exact of_decide_eq_true (equal.symm.trans (decide_eq_true yes))

def presetRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_donor_preset_feasible.{u})
    (type_of% (realize presetSignature.{u} presetActual.{u}.readout presetActual.{u}.anchor))
    Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_donor_preset_feasible
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.presetArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.presetEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨presetArena.{u}⟩,
  objectArena := .source ⟨presetArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source presetArena.{u} ⟨presetEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize presetSignature.{u} presetActual.{u}.readout presetActual.{u}.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection,
    definition := none,
    coordinates := #[0, 1, 2, 3, 8],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"],
      booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms presetEvidence
#print axioms presetRegistration

@[reducible] def uniformArena : Arena where
  signature := presetSignature.{u}
  Law R := ∀ {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2*m-2)) → Y)
    (table : ZMod (2*m-2+1) → Y)
    (target : ∀ v j s, s < 2*m-2 → f (some ⟨v, -j, s⟩) = table j),
    R.readout () ⟨Y, ⟨m, hm⟩, alphabet, uniformHorizon m⟩ f = true

private theorem uniformPositive : uniformArena.{u}.Law presetActual := by
  classical
  intro Y m hm alphabet f table target
  exact decide_eq_true (original_uniform_phase_preset m hm alphabet f table target)

private theorem uniformNegative : ¬ uniformArena.{u}.Law presetDenied := by
  intro law
  have bad := law 5 (by omega) false (fun _ => (ULift.up false : ULift.{u} Bool))
    (fun _ => ⟨false⟩) (by intros; rfl)
  change false = true at bad
  cases bad

def uniformEvidence : Registration uniformArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_uniform_phase_preset.{u})) where
  actual := presetActual
  bridge := by
    classical
    constructor
    · intro source Y m hm alphabet f table target
      exact decide_eq_true (source m hm alphabet f table target)
    · intro law Y m hm alphabet f table target
      exact of_decide_eq_true (law m hm alphabet f table target)
  variation := ⟨uniformPositive, presetDenied, uniformNegative⟩
  sensitivity := ⟨fun i => ⟨presetDenied,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, uniformNegative⟩,
    fun i => nomatch i⟩
  dependence := presetEvidence.dependence

def uniformRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_uniform_phase_preset.{u})
    (type_of% (realize presetSignature.{u} presetActual.{u}.readout presetActual.{u}.anchor))
    Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_uniform_phase_preset
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.uniformArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.uniformEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨uniformArena.{u}⟩,
  objectArena := .source ⟨uniformArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source uniformArena.{u} ⟨uniformEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize presetSignature.{u} presetActual.{u}.readout presetActual.{u}.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection,
    definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"],
      booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

@[reducible] def priceSignature : Signature where
  Params := Σ Y : Type u, {m : ℕ // 5 ≤ m} × Bool
  State p := Option (LiveRecord (2*p.2.1.val-2)) → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

def priceActual : Realization priceSignature.{u} := realize priceSignature
  (fun _ p f => GlobalPresetPrice (2*p.2.1.val-2) p.2.1.val
    (by have := p.2.1.property; omega) p.2.2 f) (fun e => nomatch e)
def priceDenied : Realization priceSignature.{u} :=
  realize priceSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

@[reducible] def priceArena : Arena where
  signature := priceSignature.{u}
  Law R := ∀ {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2*m-2)) → Y)
    (table : ZMod (2*m-2+1) → Y)
    (target : ∀ v j s, s < 2*m-2 → f (some ⟨v, -j, s⟩) = table j),
    GlobalAdaptivePrice (2*m-2) m (by omega) alphabet f ≤
      R.readout () ⟨Y, ⟨m, hm⟩, alphabet⟩ f ∧
    R.readout () ⟨Y, ⟨m, hm⟩, alphabet⟩ f ≤
      GlobalAdaptivePrice (2*m-2) m (by omega) alphabet f + 4 ∧
    GlobalAdaptivePrice (2*m-2) m (by omega) alphabet f + 4 < ⊤

private theorem zeroAdaptive : GlobalAdaptivePrice 8 5 (by omega) false
    (fun _ => (ULift.up false : ULift.{u} Bool)) = 0 := by
  classical
  change GlobalAdaptivePrice 8 5 (by omega) false _ = ((0 : ℕ) : ℕ∞)
  rw [GlobalAdaptivePrice, FullPositiveWindowPrice.BudgetPrice, ENat.iInf_eq_natCast_iff]
  refine ⟨⟨⟨0, ?_⟩, rfl⟩, fun d => by simp⟩
  refine ⟨fun _ _ => .inl ⟨false⟩, ?_, rfl, ?_⟩
  · intro free ar B impossible
    cases impossible
  · intro history
    exact ⟨0, le_rfl, rfl⟩

private theorem zeroPreset : GlobalPresetPrice 8 5 (by omega) false
    (fun _ => (ULift.up false : ULift.{u} Bool)) = 0 := by
  classical
  change GlobalPresetPrice 8 5 (by omega) false _ = ((0 : ℕ) : ℕ∞)
  rw [GlobalPresetPrice, FullPositiveWindowPrice.BudgetPrice, ENat.iInf_eq_natCast_iff]
  refine ⟨⟨⟨0, ?_⟩, rfl⟩, fun d => by simp⟩
  refine ⟨fun _ _ => false, fun _ _ => some ⟨false⟩, ?_, rfl, ?_⟩
  · intro free ar B impossible
    cases impossible
  · intro history
    exact ⟨0, le_rfl, rfl⟩

private theorem samplePriceNonzero : GlobalPresetPrice 8 5 (by omega) false
    _root_.Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.sampleTarget.{u}
      ≠ 0 := by
  classical
  intro zero
  change GlobalPresetPrice 8 5 (by omega) false _ = ((0 : ℕ) : ℕ∞) at zero
  rw [GlobalPresetPrice, FullPositiveWindowPrice.BudgetPrice,
    ENat.iInf_eq_natCast_iff] at zero
  obtain ⟨⟨budget, eq⟩, _⟩ := zero
  have count : budget.val = 0 := by exact_mod_cast eq
  have feasible := budget.property
  rw [count] at feasible
  obtain ⟨stream, stop, legal, bottom, correct⟩ := feasible
  apply _root_.Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.sample_not_feasible.{u}
  refine ⟨stream, stop, legal, bottom, ?_⟩
  intro history
  obtain ⟨c, bound, success⟩ := correct history
  refine ⟨c, by omega, ?_⟩
  rw [OriginalAcquiredTrace.execute_paid_trace 8 5 (by omega)] at success ⊢
  obtain ⟨issued, trace, count, _⟩ := success
  exact ⟨issued, trace, count, by omega⟩

private theorem pricePositive : priceArena.{u}.Law priceActual :=
  original_uniform_paid_feedback_bound
private theorem priceNegative : ¬ priceArena.{u}.Law priceDenied := by
  intro law
  have bad := (law 5 (by omega) false (fun _ => (ULift.up false : ULift.{u} Bool))
    (fun _ => ⟨false⟩) (by intros; rfl)).2.1
  change (⊤ : ℕ∞) ≤ GlobalAdaptivePrice 8 5 (by omega) false
    (fun _ => (ULift.up false : ULift.{u} Bool)) + 4 at bad
  rw [zeroAdaptive] at bad
  norm_num at bad

def priceEvidence : Registration priceArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_uniform_paid_feedback_bound.{u})) where
  actual := priceActual
  bridge := Iff.rfl
  variation := ⟨pricePositive, priceDenied, priceNegative⟩
  sensitivity := ⟨fun i => ⟨priceDenied,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, priceNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ⟨5, by omega⟩, false⟩, fun _ => ⟨false⟩,
      _root_.Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction.sampleTarget,
      ?_⟩
    change GlobalPresetPrice 8 5 (by omega) false (fun _ => (ULift.up false : ULift.{u} Bool)) ≠
      GlobalPresetPrice 8 5 (by omega) false _
    rw [zeroPreset]
    exact Ne.symm samplePriceNonzero

def priceRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_uniform_paid_feedback_bound.{u})
    (type_of% (realize priceSignature.{u} priceActual.{u}.readout priceActual.{u}.anchor))
    Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.original_uniform_paid_feedback_bound
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.priceArena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.priceEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨priceArena.{u}⟩,
  objectArena := .source ⟨priceArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source priceArena.{u} ⟨priceEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize priceSignature.{u} priceActual.{u}.readout priceActual.{u}.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection,
    definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms uniformEvidence
#print axioms uniformRegistration
#print axioms priceEvidence
#print axioms priceRegistration

namespace Calendar

@[reducible] def signature : Signature where
  Params := ℕ × ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ i => i) (fun e => nomatch e)
def oracle : Realization signature := realize signature (fun _ _ i => i + 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 5 ≤ m) (h eps i : ℕ),
    (((2 * h + eps) * m + R.readout () (m, h, eps) i : ℕ) : ZMod (2 * m - 2 + 1)) =
      ((h + eps * m + i : ℕ) : ZMod (2 * m - 2 + 1))
private theorem positive : arena.Law actual := calendar
private theorem negative : ¬ arena.Law oracle := by
  intro law
  have bad := law 5 (by omega) 0 0 0
  change (1 : ZMod 9) = 0 at bad
  exact (by decide : (1 : ZMod 9) ≠ 0) bad

def evidence : Registration arena (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.calendar)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    exact ⟨(5, 0, 0), 0, 1, by decide⟩

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.calendar)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.Calendar.calendar,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.Calendar.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection, definition := none,
    coordinates := #[0, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end Calendar

namespace RowReadings

@[reducible] def signature : Signature where
  Params := ℕ × ℕ × List (ℕ → ZMod 2) × ℕ
  State p := ZMod (p.1 + 1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (Option (ZMod 2))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p j => (PhysicalWindowDecoder.rowReadings p.1 p.2.1 p.2.2.1 j)[p.2.2.2]?)
  (fun e => nomatch e)
def oracle : Realization signature := realize signature (fun _ _ _ => none) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (k m : ℕ) (rows : List (ℕ → ZMod 2)) (j : ZMod (k + 1)) (t : ℕ),
    R.readout () (k, m, rows, t) j =
      (rows[t]?).map (fun row => some (windowCharge k m row (j - ((t * m : ℕ) : ZMod (k + 1)))))
private theorem positive : arena.Law actual := row_readings_index
private theorem negative : ¬ arena.Law oracle := by
  intro law
  have bad := law 3 1 [fun _ => 0] 0 0
  norm_num [oracle, realize, windowCharge] at bad
  cases bad

def evidence : Registration arena (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.row_readings_index)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨(3, 1, [fun n => if n = 0 then 0 else 1], 0), 0, 1, ?_⟩
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.row_readings_index)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.RowReadings.row_readings_index,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.RowReadings.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection, definition := none,
    coordinates := #[0, 1, 2, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end RowReadings

end
noncomputable section
universe u
namespace ScriptPreset

@[reducible] def signature : Signature where
  Params := ℕ
  State m := List (Fin m → Bool)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ words => words.length) (fun e => nomatch e)
def oracle : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u} (k m : ℕ) (hk : 2 ≤ k) (short : m < k) (alphabet : Bool)
    (f : Option (LiveRecord k) → Y) (words : List (Fin m → Bool))
    (decode : ZMod 2 → NarrowWindowCost.Archive m → Y)
    (decoded : ∀ (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ), s < k →
      decode v (PhysicalWindowDecoder.scriptArchive words (some ⟨v, phase, s⟩)) = f (some ⟨v, phase, s⟩)),
    OriginalPresetFeasible k m (by omega) alphabet f (R.readout () m words)
private theorem positive : arena.{u}.Law actual := script_global_preset

def word : Fin 2 → Bool := fun i => decide (i.val = 1)
def sample : Option (LiveRecord 3) → ULift.{u} (ZMod 2)
  | none => ⟨0⟩
  | some q => ⟨q.value + LiteralModel.wordIncrement 3 q.phase word⟩
def decode (v : ZMod 2) (ar : NarrowWindowCost.Archive 2) : ULift.{u} (ZMod 2) :=
  ⟨(ar[0]?).map Prod.snd |>.join.getD v⟩
private theorem decoded : ∀ (v : ZMod 2) (phase : ZMod 4) (s : ℕ), s < 3 →
    decode v (PhysicalWindowDecoder.scriptArchive [word] (some ⟨v, phase, s⟩)) =
    sample (some ⟨v, phase, s⟩) := by
  intro v phase s hs
  have step := short_safe_execution 3 (by omega) 2 (by omega) (by omega) word v phase s hs
    (Or.inr (by decide : word 0 = false))
  simp [PhysicalWindowDecoder.scriptArchive, step.1, decode, sample, endpointReading]
private theorem negative : ¬ arena.{u}.Law oracle := by
  intro law
  have bad := law 3 2 (by omega) (by omega) false sample [word] decode decoded
  change OriginalPresetFeasible 3 2 (by omega) false sample 0 at bad
  obtain ⟨stream, stop, legal, bottom, correct⟩ := bad
  have ex (phase : ZMod 4) (reachable : 2 ∣ phase.val) := OwnPathCharges.native_fiber 3 2 (by omega) (by omega)
    false sample 0 0 (presetSelector stream stop)
    (fun history readout => by simpa only [readout] using correct history)
    phase 0 (by omega) (by simpa using reachable)
  obtain ⟨c, _, left⟩ := ex 0 (by decide)
  obtain ⟨c', _, right⟩ := ex 2 (by decide)
  have same : OriginalExecutionBridge.NativeExecute (presetSelector stream stop) 0
      (some ⟨0, (0 : ZMod 4), 0⟩) (some 0) [] =
      OriginalExecutionBridge.NativeExecute (presetSelector stream stop) 0
      (some ⟨0, (2 : ZMod 4), 0⟩) (some 0) [] := rfl
  rw [left, right] at same
  have different : sample.{u} (some ⟨0, (0 : ZMod 4), 0⟩) ≠
      sample.{u} (some ⟨0, (2 : ZMod 4), 0⟩) := by decide
  exact different (Prod.mk.inj (Option.some.inj same)).1

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.script_global_preset.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, oracle, negative⟩
  sensitivity := ⟨fun i => ⟨oracle, fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    exact ⟨1, [], [fun _ => false], by decide⟩

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.script_global_preset.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.ScriptPreset.script_global_preset,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection.ScriptPreset.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection, definition := none,
    coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 7, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end ScriptPreset

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection
