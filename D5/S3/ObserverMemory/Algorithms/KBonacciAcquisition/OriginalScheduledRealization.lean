/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization
   mirror-E: none(waiver:symbolic-execution-and-measure)
   anchors: []
   utility: none
   digest: Scheduled tables execute original prime reads and hand off original marks. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization
/-- Chronological actual paid requests, including repeated indices and the first zero. -/
def acquired (stop : Bool) : List ℕ → (ℕ → Bool) → List (ℕ × Bool)
  | [], _ => []
  | i :: xs, q => (i, q i) :: if stop && !q i then [] else acquired stop xs q
/-- The tape label uses only the recorded replies and the preselected table. -/
def cellLabel {L : ℕ} (stop : Bool) (xs : List ℕ)
    (f : (Fin L → Bool) → Fin (L + 1)) (h : List (ℕ × Bool)) : Fin (L + 1) :=
  if e : ∃ b, view stop xs (lowReply b) = h.map Prod.snd then f e.choose else 0
/-- Configuration fields contain only a remaining schedule, acquired answers, and a tape label. -/
abbrev Config (L : ℕ) := List ℕ × List (ℕ × Bool) × Option (Fin (L + 1))
/-- Common source-free actions. Only the interpreter's read reply depends on the source. -/
def program {L : ℕ} (stop : Bool) (xs : List ℕ)
    (f : (Fin L → Bool) → Fin (L + 1)) : Config L → Instruction (Config L) ℕ Bool
  | (_, _, some _) => .halt
  | ([], h, none) => .update ([], h, some (cellLabel stop xs f h))
  | (i :: rest, h, none) => .read i (fun answer =>
      (if stop && !answer then [] else rest, h ++ [(i,answer)], none))
private theorem run_reaches {L : ℕ} (stop : Bool) (xs : List ℕ)
    (f : (Fin L → Bool) → Fin (L + 1)) (q : ℕ → Bool) (rest : List ℕ)
    (before log : List (ℕ × Bool)) :
    StateTransition.Reaches (step (program stop xs f) q)
      ((rest, before, none), log)
      (([], before ++ acquired stop rest q,
        some (cellLabel stop xs f (before ++ acquired stop rest q))),
        log ++ acquired stop rest q) := by
  induction rest generalizing before log with
  | nil =>
      apply Relation.ReflTransGen.single
      simp [step, program, acquired]
  | cons i rest ih =>
      by_cases stopped : (stop && !q i) = true
      · have next : StateTransition.Reaches (step (program stop xs f) q)
            (([], before ++ [(i, q i)], none), log ++ [(i, q i)])
            (([], before ++ [(i, q i)], some (cellLabel stop xs f (before ++ [(i, q i)]))),
              log ++ [(i, q i)]) :=
          Relation.ReflTransGen.single (by simp [step, program])
        have one : StateTransition.Reaches (step (program stop xs f) q)
            ((i :: rest, before, none), log)
            (([], before ++ [(i, q i)],none), log ++ [(i, q i)]) := by
          apply Relation.ReflTransGen.single
          simp only [step, program, if_pos stopped]
          rfl
        simpa only [StateTransition.Reaches, acquired, if_pos stopped, List.append_nil,
          List.append_assoc] using one.trans next
      · have one : StateTransition.Reaches (step (program stop xs f) q)
            ((i :: rest, before, none), log)
            ((rest,before ++ [(i, q i)],none), log ++ [(i, q i)]) := by
          apply Relation.ReflTransGen.single
          simp only [step, program, if_neg stopped]
          rfl
        simpa only [StateTransition.Reaches, acquired, if_neg stopped, List.append_assoc,
          List.singleton_append]
          using one.trans (ih (before ++ [(i, q i)]) (log ++ [(i, q i)]))
private theorem acquired_view (stop : Bool) (xs : List ℕ) (q : ℕ → Bool) :
    (acquired stop xs q).map Prod.snd = view stop xs q := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      by_cases h : (stop && !q i) = true <;> simp [acquired, view, h, ih]
private theorem acquired_length (stop : Bool) (xs : List ℕ) (q : ℕ → Bool) :
    (acquired stop xs q).length ≤ xs.length := by
  induction xs with
  | nil => simp [acquired]
  | cons i xs ih =>
      by_cases h : (stop && !q i) = true
      · simp [acquired, h]
      · simpa [acquired, h] using ih
/-- The actual interpreter executes exactly the selected schedule (N) or its
first-zero prefix (O), charges every read, and hands the table's label onward. -/
private theorem scheduled_catalog_execution {L : ℕ} (stop : Bool) (xs : List ℕ)
    (f : (Fin L → Bool) → Fin (L + 1))
    (low : ∀ i ∈ xs, i < L) (budget : xs.length ≤ 2)
    (cell : ∀ b c, view stop xs (lowReply b) = view stop xs (lowReply c) → f b = f c)
    (q : ℕ → Bool) (b : Fin L → Bool) (same : ∀ i : Fin L, q i = b i) :
    (([], acquired stop xs q, some (f b)), acquired stop xs q) ∈
      StateTransition.eval (step (program stop xs f) q) ((xs, [], none), []) ∧
    (acquired stop xs q).length ≤ 2 ∧
    (acquired stop xs q).map Prod.snd = view stop xs q := by
  have matched : view stop xs (lowReply b) = (acquired stop xs q).map Prod.snd := by
    rw [acquired_view]
    symm
    apply view_congr
    intro i hi
    have hil := low i hi
    simpa [lowReply, hil] using same ⟨i, hil⟩
  have label : cellLabel stop xs f (acquired stop xs q) = f b := by
    have ex : ∃ c, view stop xs (lowReply c) = (acquired stop xs q).map Prod.snd := ⟨b,matched⟩
    rw [cellLabel, dif_pos ex]
    exact cell _ b (ex.choose_spec.trans matched.symm)
  refine ⟨?_, (acquired_length stop xs q).trans budget, acquired_view stop xs q⟩
  apply StateTransition.mem_eval.mpr
  constructor
  · simpa [label] using run_reaches stop xs f q xs [] []
  · simp [step, program]

/-- The full disjoint union of original interval blocks, indexed by positive integers. -/
abbrev Tape := (PNat × Set.Ioo (0 : ℝ) 1) ⊕ (PNat × Set.Ioo (0 : ℝ) 1)
/-- A selected mark is an actual point in B_1, never a consumer proposal. -/
def mark (j : ℕ) : Tape :=
  Sum.inl (1, ⟨1 / ((j : ℝ) + 2), by
    constructor
    · positivity
    · apply (div_lt_one (by positivity : (0 : ℝ) < j + 2)).mpr
      have := Nat.cast_nonneg (α := ℝ) j
      linarith⟩)
/-- The original consumer returns unknown on B_j and proposes j on P_j. -/
def consumer : Tape → Option ℕ :=
  Sum.elim (fun _ => none) (fun z => some z.1.val)
/-- All original Fibonacci labels, with the canonical window and no distribution on sources. -/
abbrev Source := {x : ℕ × ℤ // Nat.Prime x.1 ∧
  ⌈(Nat.fib x.1 : ℚ) / 10⌉ ≤ x.2 ∧ x.2 ≤ ⌊(Nat.fib x.1 : ℚ) / 5⌋}
/-- Natural address i reads the original prime p_(i+1), on the same static source. -/
def reply (x : Source) (i : ℕ) : Bool :=
  decide ((Nat.nth Nat.Prime i : ℤ) ∣ 1 + (Nat.fib x.val.1 : ℤ) * x.val.2)
/-- Handoff retains the actual source and supplies only the original tape to its consumer. -/
def handoff {L : ℕ} (x : Source) (z : Config L) : Source × Tape :=
  (x, mark (z.2.2.getD 0).val)

/-- One source-independent schedule and program per complete finite table execute
on every actual original source, charge every read, and hand the table's actual
mark to the unchanged consumer on that same source. -/
theorem original_scheduled_realization (L : ℕ) (stop : Bool) :
    ∃ schedule : Catalog stop L → List ℕ,
      (∀ f, (schedule f).length ≤ 2 ∧ (∀ i ∈ schedule f, i < L) ∧
        (stop = true → (schedule f).Pairwise (· < ·))) ∧
      ∀ f x,
        let b : Fin L → Bool := fun i => reply x i
        let log := acquired stop (schedule f) (reply x)
        let last : Config L := ([], log, some (f.val b))
        (last, log) ∈ StateTransition.eval
          (step (program stop (schedule f) f.val) (reply x)) ((schedule f, [], none), []) ∧
        log.length ≤ 2 ∧ log.map Prod.snd = view stop (schedule f) (reply x) ∧
        handoff x last = (x, mark (f.val b).val) ∧
        consumer (handoff x last).2 = none := by
  classical
  choose schedule length low ordered cells using (fun f : Catalog stop L => f.property)
  refine ⟨schedule, fun f => ⟨length f, low f, ordered f⟩, ?_⟩
  intro f x
  dsimp only
  have executed := scheduled_catalog_execution stop (schedule f) f.val
    (low f) (length f) (cells f) (reply x) (fun i => reply x i) (fun _ => rfl)
  exact ⟨executed.1, executed.2.1, executed.2.2, rfl, rfl⟩

#print axioms original_scheduled_realization

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization
