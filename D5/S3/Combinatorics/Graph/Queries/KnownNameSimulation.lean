/- GID: D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/KnownNameSimulation
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: Known-name simulation reduces any change of success to a hit at a previously unknown name. -/

import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Known-name simulation for deterministic complete-neighborhood queries. -/

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation

variable {N : Type*}

attribute [local instance] Classical.propDecidable

abbrev Reply (N : Type*) := Option (Set N)
abbrev Protocol (N : Type*) := PassiveProtocol N (fun _ => Reply N)
abbrev Record (N : Type*) := List (Σ _ : N, Reply N)

def namesAfter (known : Set N) (name : N) : Reply N → Set N
  | none => known
  | some neighbors => insert name (known ∪ neighbors)

noncomputable def simulate (read : N → Reply N) : Protocol N → Set N → Record N
  | .stop, _ => []
  | .query name next, known =>
    let reply := if name ∈ known then read name else none
    ⟨name, reply⟩ :: simulate read (next reply) (namesAfter known name reply)

/-- Every successful query uses a name already seen at the time of the query. -/
def noGuessedHit (known : Set N) : Record N → Prop
  | [] => True
  | entry :: tail => (entry.2.isSome → entry.1 ∈ known) ∧
    noGuessedHit (namesAfter known entry.1 entry.2) tail

/-- The labels sent to the oracle, omitting queries answered by a synthetic miss. -/
noncomputable def sentNames (known : Set N) : Record N → List N
  | [] => []
  | entry :: tail =>
    let rest := sentNames (namesAfter known entry.1 entry.2) tail
    if entry.1 ∈ known then entry.1 :: rest else rest

/-- A uniform bound on every branch of a deterministic strategy. -/
def depthBound : Protocol N → ℕ → Prop
  | .stop, _ => True
  | .query _ _, 0 => False
  | .query _ next, n + 1 => ∀ reply, depthBound (next reply) n

private theorem sentNames_length_le (record : Record N) (known : Set N) :
    (sentNames known record).length ≤ record.length := by
  induction record generalizing known with
  | nil => simp [sentNames]
  | cons entry tail ih =>
    simp only [sentNames, List.length_cons]
    split
    · simpa only [List.length_cons, Nat.add_le_add_iff_right] using
        ih (namesAfter known entry.1 entry.2)
    · exact (ih _).trans (Nat.le_succ _)

private theorem simulation_length_le (read : N → Reply N) (p : Protocol N)
    (known : Set N) (n : ℕ) (hn : depthBound p n) :
    (simulate read p known).length ≤ n := by
  induction p generalizing known n with
  | stop => simp [simulate]
  | query name next ih =>
    cases n with
    | zero => exact False.elim hn
    | succ n =>
      simp only [simulate, List.length_cons, Nat.add_le_add_iff_right]
      exact ih _ _ _ (hn _)

/-- Synthetic misses preserve the query budget and restrict all actual calls to
the names known at the time of the call. -/
theorem simulated_sent_names_bound (read : N → Reply N) (p : Protocol N)
    (known : Set N) (n : ℕ) (hn : depthBound p n) :
    let callCount := (sentNames known (simulate read p known)).length
    callCount ≤ n :=
  (sentNames_length_le _ _).trans (simulation_length_le read p known n hn)

private theorem simulate_eq_iff (read : N → Reply N) (p : Protocol N) (known : Set N) :
    simulate read p known = replayPassiveProtocol p read ↔
      noGuessedHit known (replayPassiveProtocol p read) := by
  classical
  induction p generalizing known with
  | stop => simp [simulate, replayPassiveProtocol, noGuessedHit]
  | query name next ih =>
    by_cases hx : name ∈ known
    · simp [simulate, replayPassiveProtocol, noGuessedHit, hx, ih]
    · cases hread : read name with
      | none => simp [simulate, replayPassiveProtocol, noGuessedHit, hx, hread, ih]
      | some neighbors =>
        simp [simulate, replayPassiveProtocol, noGuessedHit, hx, hread]

/-- Replacing an unknown-name query by a synthetic miss can change success only
on worlds where the unrestricted strategy hits a previously unknown name. -/
theorem success_mass_le_simulated_add_guessed_hit {W : Type*}
    (μ : PMF W) (read : W → N → Reply N) (p : Protocol N) (known : Set N)
    (wins : W → Record N → Prop) :
    let noGuessEvent := {w | noGuessedHit known (replayPassiveProtocol p (read w))}
    let guessedHit := noGuessEventᶜ
    μ.toOuterMeasure {w | wins w (replayPassiveProtocol p (read w))} ≤
      μ.toOuterMeasure {w | wins w (simulate (read w) p known)} +
        μ.toOuterMeasure guessedHit := by
  intro noGuessEvent guessedHit
  let realWin : Set W := {w | wins w (replayPassiveProtocol p (read w))}
  let simulatedWin : Set W := {w | wins w (simulate (read w) p known)}
  have hsubset : realWin ⊆ simulatedWin ∪ guessedHit := by
    intro w hw
    by_cases h : noGuessedHit known (replayPassiveProtocol p (read w))
    · left
      change wins w (simulate (read w) p known)
      rw [(simulate_eq_iff (read w) p known).2 h]
      exact hw
    · exact Or.inr h
  calc
    μ.toOuterMeasure realWin ≤ μ.toOuterMeasure (simulatedWin ∪ guessedHit) :=
      μ.toOuterMeasure.mono hsubset
    _ ≤ μ.toOuterMeasure simulatedWin + μ.toOuterMeasure guessedHit :=
      MeasureTheory.measure_union_le _ _

def truncate (p : Protocol N) (n : ℕ) : Protocol N :=
  match p, n with
  | _, 0 => .stop
  | .stop, _ + 1 => .stop
  | .query q next, n + 1 => .query q (fun reply => truncate (next reply) n)

private theorem replay_truncate (read : N → Reply N) (p : Protocol N) (n : ℕ) :
    replayPassiveProtocol (truncate p n) read = (replayPassiveProtocol p read).take n := by
  induction p generalizing n with
  | stop => cases n <;> rfl
  | query name next ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [truncate, replayPassiveProtocol, List.take_succ_cons]
      rw [ih]

def nextQuery (p : Protocol N) : Record N → Option N :=
  match p with
  | .stop => fun _ => none
  | .query name next => fun
    | [] => some name
    | entry :: rest => nextQuery (next entry.2) rest

/-- The next queried name is a function of the actual preceding transcript. -/
theorem nextQuery_of_prefix (read : N → Reply N) (p : Protocol N) (n : ℕ) :
    let recordedQuery := ((replayPassiveProtocol p read)[n]?).map Sigma.fst
    nextQuery p (replayPassiveProtocol (truncate p n) read) = recordedQuery := by
  change nextQuery p (replayPassiveProtocol (truncate p n) read) =
    ((replayPassiveProtocol p read)[n]?).map Sigma.fst
  rw [replay_truncate]
  induction p generalizing n with
  | stop => cases n <;> rfl
  | query name next ih =>
    cases n with
    | zero => simp [replayPassiveProtocol, nextQuery]
    | succ n =>
      simpa only [replayPassiveProtocol, List.take_succ_cons, nextQuery,
        List.getElem?_cons_succ] using ih (read name) n

end D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
