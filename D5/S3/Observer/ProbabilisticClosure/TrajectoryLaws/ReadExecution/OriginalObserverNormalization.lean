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
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalObserverNormalization
open FreshServiceRestart

variable {C I R : Type*}

/-- A chosen original action carries one complete configuration. Its decision
    is internal and agrees with that configuration's emitted-label tag. -/
inductive Action (emission : C → Option Bool) where
  | read (state : {c : C // emission c = none})
  | emit (state : C) (decision : Bool) (valid : emission state = some decision)

def Action.configuration {emission : C → Option Bool} : Action emission → C
  | .read c => c.val
  | .emit c _ _ => c

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
  initialize : I → C
  initialAction : C → I → Action emission
  update : C → Bool → R → C
  afterRead : C → Bool → R → C → Action emission

namespace Machine
variable (O : Machine C I R)

/-- Every live configuration is retained, including unreachable ones. Only
    the already emitted configurations with the same decision are merged. -/
def Boundary := {c : C // O.emission c = none} ⊕ Bool

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
  O.initialAction (O.initialize seed) seed

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
    let e := O.execute seed source coins n
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

/-- The boundary embeds into the SAME complete carrier using the original two
    labels. No active state, initialization state or phase is added. -/
theorem same_budget [Fintype C] : Fintype.card O.Boundary ≤ Fintype.card C := by
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
      simpa [embed, O.label_emission] using this

/-- Pointwise simulation on the ORIGINAL initialization and operation coins.
    The original receipt is the acquired consecutive prefix; live execution
    has paid exactly n reads. Initial and in-zero stopping are included. -/
theorem execution_normalization (seed : I) (coins : ℕ → R)
    (wait : ℕ) (gaps : ℕ → ℕ) (n : ℕ) :
    O.boundary (O.execute seed (ActualRenewalStopping.sourceBit wait gaps) coins n).action =
      ActualRenewalStopping.run O.labels O.normalizedUpdate
        (O.boundary (O.initial seed)) coins wait gaps n ∧
    (O.execute seed (ActualRenewalStopping.sourceBit wait gaps) coins n).acquired =
      (List.range (O.execute seed (ActualRenewalStopping.sourceBit wait gaps) coins n).
        acquired.length).map (ActualRenewalStopping.sourceBit wait gaps) ∧
    ((O.execute seed (ActualRenewalStopping.sourceBit wait gaps) coins n).action.output =
      none → (O.execute seed (ActualRenewalStopping.sourceBit wait gaps) coins n).
        acquired.length = n) := by
  refine ⟨?_, receipt_prefix O seed _ coins n, live_length O seed _ coins n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ActualRenewalStopping.run, ← ih]
    cases ha : (O.execute seed (ActualRenewalStopping.sourceBit wait gaps) coins n).action with
    | emit c d hd => simp [execute, ha, boundary, labels, output]
    | read c =>
      have hlen := live_length O seed (ActualRenewalStopping.sourceBit wait gaps) coins n
        (by simp [ha, Action.output])
      simp [execute, ha, hlen, boundary, labels, output, normalizedUpdate]

end Machine
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalObserverNormalization
