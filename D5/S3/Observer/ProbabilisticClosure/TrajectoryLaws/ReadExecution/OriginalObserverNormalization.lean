/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original joint actions normalize without changing acquired bits, paid reads or internal decisions. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalObserverNormalization
open FreshServiceRestart

variable {C I R : Type*}

/-- A chosen original action carries one complete configuration. Its decision
    is internal and agrees with that configuration's emitted-label tag. -/
inductive Action (emission : C → Option Bool) where
  | read (state : {c : C // emission c = none})
  | emit (state : C) (decision : Bool) (valid : emission state = some decision)

def Action.output {emission : C → Option Bool} : Action emission → Option Bool
  | .read _ => none
  | .emit _ d _ => some d

/-- The initialization and paid operation include their ensuing action choice.
    The update and that choice may use the SAME innovation and newly read bit.
    Neither primitive receives a clock, a source name, a cost or a past record.
    Intermediate and retained configurations both belong to C. -/
structure Machine (C I R : Type*) where
  emission : C → Option Bool
  label : Bool → C
  label_emission : ∀ d, emission (label d) = some d
  prepare : I → C
  initialAction : C → I → Action emission
  update : C → Bool → R → C
  afterRead : C → Bool → R → C → Action emission

namespace Machine
variable (O : Machine C I R)

/-- Every live configuration is retained, including unreachable ones. Only
    the already emitted configurations with the same decision are merged. -/
abbrev Boundary := {c : C // O.emission c = none} ⊕ Bool

instance [Fintype C] : Fintype O.Boundary := by
  unfold Boundary
  infer_instance

instance : MeasurableSpace O.Boundary := ⊤
instance : MeasurableSingletonClass O.Boundary := ⟨fun _ => trivial⟩

def boundary : Action O.emission → O.Boundary
  | .read c => .inl c
  | .emit _ d _ => .inr d

def output : O.Boundary → Option Bool
  | .inl _ => none
  | .inr d => some d

def labels : Set O.Boundary := {s | O.output s ≠ none}

def initial (seed : I) : Action O.emission :=
  O.initialAction (O.prepare seed) seed

def joint (c : C) (b : Bool) (r : R) : Action O.emission :=
  O.afterRead c b r (O.update c b r)

/-- This is extracted from the original joint outcome, not a specified row law. -/
def normalizedUpdate : O.Boundary → Bool → R → O.Boundary
  | .inl c, b, r => O.boundary (O.joint c.val b r)
  | .inr d, _, _ => .inr d

/-- A mathematical receipt of the actual reads, not persistent observer memory. -/
structure Execution where
  action : Action O.emission
  acquired : List Bool

/-- One original action either stops internally without reading, or acquires
    the next consecutive bit and performs its joint update/ensuing choice.
    The read-port cursor is the receipt length; it is not a primitive input. -/
def execute (seed : I) (source : ℕ → Bool) (coins : ℕ → R) : ℕ → O.Execution
  | 0 => ⟨O.initial seed, []⟩
  | n + 1 =>
    let e := execute seed source coins n
    match e.action with
    | .emit _ _ _ => e
    | .read c =>
      let t := e.acquired.length
      ⟨O.joint c.val (source t) (coins t), e.acquired ++ [source t]⟩

/-- Defined from original action execution before any target first-hit time. -/
def stopIndex (seed : I) (source : ℕ → Bool) (coins : ℕ → R) : Option ℕ :=
  if h : ∃ n, (O.execute seed source coins n).action.output ≠ none then
    some (Nat.find h) else none

/-- Nonemission is none. A finite result contains the actual receipt and the
    internally emitted decision, rather than a decoder of the stopping index. -/
def result (seed : I) (source : ℕ → Bool) (coins : ℕ → R) :
    Option (List Bool × Bool) :=
  (O.stopIndex seed source coins).bind fun n =>
    (O.execute seed source coins n).action.output.map fun d =>
      ((O.execute seed source coins n).acquired, d)

/-- The original paid cost is read from its actual receipt, including the
    terminal partial gap; none denotes an execution that never emits. -/
def paidCost (seed : I) (source : ℕ → Bool) (coins : ℕ → R) : Option ℕ :=
  (O.result seed source coins).map (fun v => v.1.length)

def decision (seed : I) (source : ℕ → Bool) (coins : ℕ → R) : Option Bool :=
  (O.result seed source coins).map Prod.snd

private theorem live_length (seed : I) (source : ℕ → Bool) (coins : ℕ → R)
    (n : ℕ) : (O.execute seed source coins n).action.output = none →
      (O.execute seed source coins n).acquired.length = n := by
  induction n with
  | zero => simp [execute]
  | succ n ih =>
    cases ha : (O.execute seed source coins n).action with
    | emit c d hd => simp [execute, ha, Action.output]
    | read c =>
      have hlen := ih (by simp [ha, Action.output])
      simp [execute, ha, hlen]

private theorem receipt_prefix (seed : I) (source : ℕ → Bool) (coins : ℕ → R)
    (n : ℕ) : (O.execute seed source coins n).acquired =
      (List.range (O.execute seed source coins n).acquired.length).map source := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases ha : (O.execute seed source coins n).action with
    | emit c d hd => simpa [execute, ha] using ih
    | read c =>
      simp only [execute, ha, List.length_append, List.length_singleton,
        List.range_succ, List.map_append, List.map_singleton]
      rw [ih]
      simp only [List.length_map, List.length_range]

/-- The boundary embeds into the SAME complete carrier using the original two
    labels. No active state, initialization state or phase is added. -/
private theorem same_budget [Fintype C] : Fintype.card O.Boundary ≤ Fintype.card C := by
  let embed : O.Boundary → C := fun s => match s with
    | .inl c => c.val
    | .inr d => O.label d
  apply Fintype.card_le_of_injective embed
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext h)
    | inr b =>
      have := congrArg O.emission h
      simp [embed, a.property, O.label_emission] at this
  | inr a =>
    cases b with
    | inl b =>
      have := congrArg O.emission h
      simp [embed, b.property, O.label_emission] at this
    | inr b =>
      have := congrArg O.emission h
      exact congrArg Sum.inr (by simpa [embed, O.label_emission] using this)

/-- Pointwise simulation on the ORIGINAL initialization and operation coins.
    The original receipt is the acquired consecutive prefix; live execution
    has paid exactly n reads. Initial and in-zero stopping are included. -/
theorem execution_normalization (seed : I) (coins : ℕ → R)
    (wait : ℕ) (gaps : ℕ → ℕ) (n : ℕ) :
    let e := O.execute seed (ActualRenewalStopping.sourceBit wait gaps) coins n
    O.boundary e.action =
      ActualRenewalStopping.run O.labels O.normalizedUpdate
        (O.boundary (O.initial seed)) coins wait gaps n ∧
    e.acquired = (List.range e.acquired.length).map
      (ActualRenewalStopping.sourceBit wait gaps) ∧
    (e.action.output = none → e.acquired.length = n) := by
  refine ⟨?_, receipt_prefix O seed _ coins n, live_length O seed _ coins n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ActualRenewalStopping.run, ← ih]
    cases ha : (O.execute seed (ActualRenewalStopping.sourceBit wait gaps) coins n).action with
    | emit c d hd => simp [execute, ha, boundary, labels, Set.mem_ofPred_eq, output]
    | read c =>
      have hlen := live_length O seed (ActualRenewalStopping.sourceBit wait gaps) coins n
        (by simp [ha, Action.output])
      simp [execute, ha, hlen, boundary, labels, Set.mem_ofPred_eq, output, normalizedUpdate]

private theorem boundary_output (a : Action O.emission) :
    O.output (O.boundary a) = a.output := by
  cases a <;> rfl

theorem stop_spec (seed : I) (source : ℕ → Bool) (coins : ℕ → R) (n : ℕ) :
    O.stopIndex seed source coins = some n ↔
      (O.execute seed source coins n).action.output ≠ none ∧
      ∀ k < n, (O.execute seed source coins k).action.output = none := by
  constructor
  · intro hn
    unfold stopIndex at hn
    split at hn
    next h =>
      have he := Option.some.inj hn
      subst n
      exact ⟨Nat.find_spec h, fun k hk => not_not.mp (Nat.find_min h hk)⟩
    next h => cases hn
  · rintro ⟨hn, hpre⟩
    have h : ∃ k, (O.execute seed source coins k).action.output ≠ none := ⟨n, hn⟩
    have he : Nat.find h = n := (Nat.find_eq_iff h).mpr
      ⟨hn, fun k hk => by rw [hpre k hk]; simp⟩
    simp only [stopIndex, dif_pos h, he]

theorem stop_length (seed : I) (source : ℕ → Bool) (coins : ℕ → R)
    (n : ℕ) (hn : O.stopIndex seed source coins = some n) :
    (O.execute seed source coins n).acquired.length = n := by
  cases n with
  | zero => rfl
  | succ n =>
    have hpre := ((stop_spec O seed source coins (n + 1)).mp hn).2 n (by omega)
    have hlen := live_length O seed source coins n hpre
    cases ha : (O.execute seed source coins n).action with
    | emit c d hd => simp [ha, Action.output] at hpre
    | read c => simp [execute, ha, hlen]

/-- Original first emission is identified with the target only AFTER its
    operational definition. Its full receipt and internal label are retained;
    the actual-renewal epoch consumer then charges only originally paid bits. -/
private theorem stopping_transfer [Fintype C] (M : ℕ) (hM : Fintype.card C ≤ M)
    (seed : I) (coins : ℕ → R) (wait : ℕ) (gaps : ℕ → ℕ) :
    Fintype.card O.Boundary ≤ M ∧
    O.stopIndex seed (ActualRenewalStopping.sourceBit wait gaps) coins =
      firstHit O.labels (ActualRenewalStopping.run O.labels O.normalizedUpdate
        (O.boundary (O.initial seed)) coins wait gaps) ∧
    O.result seed (ActualRenewalStopping.sourceBit wait gaps) coins =
      (firstHit O.labels (ActualRenewalStopping.run O.labels O.normalizedUpdate
        (O.boundary (O.initial seed)) coins wait gaps)).bind (fun t =>
          (O.output (ActualRenewalStopping.run O.labels O.normalizedUpdate
            (O.boundary (O.initial seed)) coins wait gaps t)).map (fun d =>
              ((List.range t).map (ActualRenewalStopping.sourceBit wait gaps), d))) ∧
    (∀ T, O.stopIndex seed (ActualRenewalStopping.sourceBit wait gaps) coins = some T →
      ∃ N d,
        O.result seed (ActualRenewalStopping.sourceBit wait gaps) coins =
          some ((List.range T).map (ActualRenewalStopping.sourceBit wait gaps), d) ∧
        firstHit O.labels (ActualRenewalStopping.epoch O.labels O.normalizedUpdate
          (O.boundary (O.initial seed)) coins wait gaps) = some N ∧
        ActualRenewalStopping.epoch O.labels O.normalizedUpdate
          (O.boundary (O.initial seed)) coins wait gaps N = Sum.inr d ∧
        N ≤ ActualRenewalStopping.paidTicks wait gaps T ∧
        ActualRenewalStopping.paidTicks wait gaps T ≤ T ∧
        (N = 0 ↔ T ≤ wait + 1)) := by
  let source := ActualRenewalStopping.sourceBit wait gaps
  let Z := ActualRenewalStopping.run O.labels O.normalizedUpdate
    (O.boundary (O.initial seed)) coins wait gaps
  have houtput (n : ℕ) : O.output (Z n) =
      (O.execute seed source coins n).action.output := by
    rw [show Z n = O.boundary (O.execute seed source coins n).action from
      (execution_normalization O seed coins wait gaps n).1.symm]
    exact boundary_output O _
  have hstop : O.stopIndex seed source coins = firstHit O.labels Z := by
    unfold stopIndex firstHit
    simp only [labels, Set.mem_ofPred_eq, houtput]
  have hresult : O.result seed source coins = (firstHit O.labels Z).bind
      (fun t => (O.output (Z t)).map fun d => ((List.range t).map source, d)) := by
    rw [result, ← hstop]
    cases hs : O.stopIndex seed source coins with
    | none => simp
    | some t =>
      simp only [Option.bind_some]
      have htrace := receipt_prefix O seed source coins t
      rw [stop_length O seed source coins t hs] at htrace
      rw [htrace, houtput]
  refine ⟨(same_budget O).trans hM, hstop, hresult, ?_⟩
  intro T hT
  have hfirst : firstHit O.labels Z = some T := hstop ▸ hT
  have hterm := ((stop_spec O seed source coins T).mp hT).1
  cases ha : (O.execute seed source coins T).action with
  | read c => simp [ha, Action.output] at hterm
  | emit c d hd =>
    have hZ : Z T = Sum.inr d := by
      rw [show Z T = O.boundary (O.execute seed source coins T).action from
        (execution_normalization O seed coins wait gaps T).1.symm, ha]
      rfl
    obtain ⟨N, hN, hsame, _, _, hpaid, hle, hzero⟩ :=
      (ActualRenewalStopping.stopping_correspondence O.labels O.normalizedUpdate
        (O.boundary (O.initial seed)) coins wait gaps).1 T hfirst
    refine ⟨N, d, ?_, hN, hsame.trans hZ, hpaid, hle, hzero⟩
    rw [hresult, hfirst]
    simp [hZ, output, source]

/-- A single initialization law and two single-operation rows precede every
    source coordinate. They are pushforwards of the actual primitive maps.
    Their original-innovation simulation retains the full stopped receipt. -/
theorem stopping_normalization [Fintype C] [MeasurableSpace I] [MeasurableSpace R]
    (κ : Measure I) (ρ : Measure R) [IsProbabilityMeasure κ] [IsProbabilityMeasure ρ]
    (hinit : Measurable (fun seed => O.boundary (O.initial seed)))
    (hread : ∀ c b, Measurable (fun r => O.boundary (O.joint c b r)))
    (M : ℕ) (hM : Fintype.card C ≤ M) :
    ∃ (η : PMF O.Boundary) (A B : O.Boundary → PMF O.Boundary),
      κ.map (fun seed => O.boundary (O.initial seed)) = η.toMeasure ∧
      (∀ s, η s = κ {seed | O.boundary (O.initial seed) = s}) ∧
      (∀ b, Measurable (fun p : O.Boundary × R =>
        ActualRenewalPrefixLaw.effective O.labels O.normalizedUpdate p.1 b p.2)) ∧
      (∀ s b, ρ.map (ActualRenewalPrefixLaw.effective O.labels O.normalizedUpdate s b) =
        (if b then B s else A s).toMeasure) ∧
      (∀ d, A (Sum.inr d) = PMF.pure (Sum.inr d) ∧
        B (Sum.inr d) = PMF.pure (Sum.inr d)) ∧
      Fintype.card O.Boundary ≤ M ∧
      ∀ (seed : I) (coins : ℕ → R) (wait : ℕ) (gaps : ℕ → ℕ),
        let source := ActualRenewalStopping.sourceBit wait gaps
        let Z := ActualRenewalStopping.run O.labels O.normalizedUpdate
          (O.boundary (O.initial seed)) coins wait gaps
        let Y := ActualRenewalStopping.epoch O.labels O.normalizedUpdate
          (O.boundary (O.initial seed)) coins wait gaps
        O.stopIndex seed source coins = firstHit O.labels Z ∧
        O.paidCost seed source coins = firstHit O.labels Z ∧
        O.decision seed source coins = (firstHit O.labels Z).bind (fun t => O.output (Z t)) ∧
        O.result seed source coins = (firstHit O.labels Z).bind
          (fun t => (O.output (Z t)).map fun d => ((List.range t).map source, d)) ∧
        (∀ T, O.stopIndex seed source coins = some T → ∃ N d,
          O.result seed source coins = some ((List.range T).map source, d) ∧
          firstHit O.labels Y = some N ∧ Y N = Sum.inr d ∧
          N ≤ ActualRenewalStopping.paidTicks wait gaps T ∧
          ActualRenewalStopping.paidTicks wait gaps T ≤ T ∧
          (N = 0 ↔ T ≤ wait + 1)) := by
  have heff (s : O.Boundary) (b : Bool) (r : R) :
      ActualRenewalPrefixLaw.effective O.labels O.normalizedUpdate s b r =
        O.normalizedUpdate s b r := by
    cases s <;> simp [ActualRenewalPrefixLaw.effective, labels, Set.mem_ofPred_eq,
      output, normalizedUpdate]
  have hmeas (b : Bool) : Measurable (fun p : O.Boundary × R =>
      ActualRenewalPrefixLaw.effective O.labels O.normalizedUpdate p.1 b p.2) := by
    simp_rw [heff]
    apply measurable_from_prod_countable_right
    intro s
    cases s with
    | inl c => exact hread c.val b
    | inr d => exact measurable_const
  let η := (κ.map (fun seed => O.boundary (O.initial seed))).toPMF
  let A := fun s =>
    (ρ.map (ActualRenewalPrefixLaw.effective O.labels O.normalizedUpdate s false)).toPMF
  let B := fun s =>
    (ρ.map (ActualRenewalPrefixLaw.effective O.labels O.normalizedUpdate s true)).toPMF
  refine ⟨η, A, B, (Measure.toPMF_toMeasure _).symm, ?_, hmeas, ?_, ?_,
    (same_budget O).trans hM, ?_⟩
  · intro s
    exact Measure.map_apply hinit (measurableSet_singleton s)
  · intro s b
    cases b <;> exact (Measure.toPMF_toMeasure _).symm
  · intro d
    have habs (b : Bool) :
        ActualRenewalPrefixLaw.effective O.labels O.normalizedUpdate (Sum.inr d) b =
          fun _ => Sum.inr d := by
      funext r
      rw [heff]
      rfl
    constructor <;> apply PMF.toMeasure_injective <;>
      simp [A, B, Measure.toPMF_toMeasure, habs, Measure.map_const, PMF.toMeasure_pure]
  · intro seed coins wait gaps
    let source := ActualRenewalStopping.sourceBit wait gaps
    let Z := ActualRenewalStopping.run O.labels O.normalizedUpdate
      (O.boundary (O.initial seed)) coins wait gaps
    obtain ⟨_, hs, hr, hf⟩ := stopping_transfer O M hM seed coins wait gaps
    refine ⟨hs, ?_, ?_, hr, hf⟩
    · change (O.result seed source coins).map (fun v => v.1.length) = firstHit O.labels Z
      rw [hr]
      cases ht : firstHit O.labels Z with
      | none => rfl
      | some t =>
        have hterm := ((first_hit_some O.labels Z t).mp ht).1
        cases ho : O.output (Z t) with
        | none => exact False.elim (hterm ho)
        | some d => simp [Z, source] at ho; simp [ho]
    · change (O.result seed source coins).map Prod.snd =
        (firstHit O.labels Z).bind (fun t => O.output (Z t))
      rw [hr]
      cases ht : firstHit O.labels Z with
      | none => rfl
      | some t => cases ho : O.output (Z t) <;> simp only [Z] at ho ⊢ <;> simp [ho]

end Machine
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalObserverNormalization
