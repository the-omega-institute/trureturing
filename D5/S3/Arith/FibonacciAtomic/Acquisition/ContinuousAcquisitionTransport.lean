/- GID: D5/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous source-blind execution transports faithfully to reset histories. -/

import D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
import Mathlib.Computability.StateTransition

/-! Continuous controller semantics and transport of every terminating run. -/

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport

open D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization

universe u v

/-- A local step may include arbitrary finite public computation. The state
space includes unbounded writable memory; it is not assumed finite. Actions
complete with their fixed acknowledgement before entering their next state. -/
inductive Instruction (S : Type u) (L : Type v) where
  | compute : S → Instruction S L
  | action : Bool → S → Instruction S L
  | read : (ℕ → S) → Instruction S L
  | halt : L → Instruction S L

/-- The source cannot occur among the inputs of `code` or `initial`. This
semantic class even permits arbitrary transition functions, hence contains
finite effective programs with arbitrary finite configurations and local work. -/
structure Controller (S : Type u) (L : Type v) where
  code : S → Instruction S L
  initial : S
  fallback : L

/-- Completed events: only `reply` carries source-dependent information. -/
inductive Event where
  | compute
  | action : Bool → Event
  | reply : ℕ → Event
  deriving DecidableEq

/-- The actual single-source operational semantics. Reads are nondestructive;
true means R, false means G, exactly as in the reset supplier. -/
inductive Run {S : Type u} {L : Type v} (P : Controller S L) (H : ℕ) :
    S → (ℕ × ℕ) → List Event → S → (ℕ × ℕ) → L → Prop where
  | halt {s x l} : P.code s = .halt l → Run P H s x [] s x l
  | compute {s s' x es t y l} : P.code s = .compute s' →
      Run P H s' x es t y l → Run P H s x (.compute :: es) t y l
  | action {s s' x b es t y l} : P.code s = .action b s' →
      Run P H s' (step b x) es t y l →
      Run P H s x (.action b :: es) t y l
  | read {s k x es t y l} : P.code s = .read k →
      Run P H (k (Nat.gcd (quantity x) H)) x es t y l →
      Run P H s x (.reply (Nat.gcd (quantity x) H) :: es) t y l

/-- The reset simulator's public interpreter, retaining every local and action
step. Its sole external input at a read is the acquired answer, never a pair. -/
inductive PublicRun {S : Type u} {L : Type v} (P : Controller S L) :
    (S × List Bool) → List Event → (S × List Bool) → L → Prop where
  | halt {s A l} : P.code s = .halt l → PublicRun P (s, A) [] (s, A) l
  | compute {s s' A es t B l} : P.code s = .compute s' →
      PublicRun P (s', A) es (t, B) l →
      PublicRun P (s, A) (.compute :: es) (t, B) l
  | action {s s' A b es t B l} : P.code s = .action b s' →
      PublicRun P (s', A ++ [b]) es (t, B) l →
      PublicRun P (s, A) (.action b :: es) (t, B) l
  | read {s k A g es t B l} : P.code s = .read k →
      PublicRun P (k g, A) es (t, B) l →
      PublicRun P (s, A) (.reply g :: es) (t, B) l

/-- Exact reset records: each reply is paired with the entire cumulative
chronological action word. Repeated and empty words remain charged records. -/
def records : List Bool → List Event → Hist (fun _ : List Bool => ℕ)
  | _, [] => []
  | A, .compute :: es => records A es
  | A, .action b :: es => records (A ++ [b]) es
  | A, .reply g :: es => ⟨A, g⟩ :: records A es

/-- The cumulative word includes actions after the final reply. -/
def finalWord : List Bool → List Event → List Bool
  | A, [] => A
  | A, .compute :: es => finalWord A es
  | A, .action b :: es => finalWord (A ++ [b]) es
  | A, .reply _ :: es => finalWord A es

/-- Paid reads count events, not distinct words or distinct values. -/
def paidReads : List Event → ℕ
  | [] => 0
  | .reply _ :: es => paidReads es + 1
  | _ :: es => paidReads es

/-- Public execution between paid observations. No unknown source is present. -/
def silent {S : Type u} {L : Type v} (P : Controller S L) :
    S × List Bool → Option (S × List Bool)
  | (s, A) => match P.code s with
    | .compute s' => some (s', A)
    | .action b s' => some (s', A ++ [b])
    | _ => none

/-- Totalization of partial public computation. Its arbitrary value on
nonterminating, unreachable histories supplies no run-time observation. -/
noncomputable def normalize {S : Type u} {L : Type v} (P : Controller S L)
    (c : S × List Bool) : S × List Bool := by
  classical
  exact if h : (StateTransition.eval (silent P) c).Dom then
    (StateTransition.eval (silent P) c).get h else (P.initial, [])

/-- Replay one acquired answer after completing the preceding public interval.
The query component is retained by `records`; only its answer enters code. -/
noncomputable def advance {S : Type u} {L : Type v} (P : Controller S L)
    (c : S × List Bool) (a : Sigma (fun _ : List Bool => ℕ)) : S × List Bool :=
  let d := normalize P c
  match P.code d.1 with
  | .read k => (k a.2, d.2)
  | _ => d

/-- Replay uses only public code and previously acquired history. -/
noncomputable def replay {S : Type u} {L : Type v} (P : Controller S L)
    (h : Hist (fun _ : List Bool => ℕ)) : S × List Bool :=
  h.foldl (advance P) (P.initial, [])

/-- One selector shared by all natural-pair entries. It has no source, fuel,
termination witness, time, capacity or tariff argument. -/
noncomputable def selector {S : Type u} {L : Type v} (P : Controller S L)
    (h : Hist (fun _ : List Bool => ℕ)) : Sum (List Bool) L :=
  let c := normalize P (replay P h)
  match P.code c.1 with
  | .read _ => .inl c.2
  | .halt l => .inr l
  | _ => .inr P.fallback

private theorem normalize_terminal {S : Type u} {L : Type v} (P : Controller S L)
    (c : S × List Bool) (hc : silent P c = none) : normalize P c = c := by
  classical
  have hm : c ∈ StateTransition.eval (silent P) c :=
    StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hc⟩
  unfold normalize
  rw [dite_eq_left (Part.dom_iff_mem.mpr ⟨c, hm⟩)]
  exact Part.get_eq_of_mem hm _

private theorem normalize_step {S : Type u} {L : Type v} (P : Controller S L)
    (c d : S × List Bool) (hc : silent P c = some d) :
    normalize P c = normalize P d := by
  have he := StateTransition.reaches_eval
    (show StateTransition.Reaches (silent P) c d from Relation.ReflTransGen.single hc)
  classical
  exact congrArg (fun z : Part (S × List Bool) =>
    if h : z.Dom then z.get h else (P.initial, [])) he

private theorem word_snoc (A : List Bool) (b : Bool) (x : ℕ × ℕ) :
    runWord (A ++ [b]) x = step b (runWord A x) := by
  induction A generalizing x with
  | nil => rfl
  | cons a A ih => simpa only [List.cons_append, runWord] using ih (step a x)

private theorem record_count (A : List Bool) (es : List Event) :
    (records A es).length = paidReads es := by
  induction es generalizing A with
  | nil => rfl
  | cons e es ih => cases e <;> simp [records, paidReads, ih, Nat.add_comm]

private theorem run_endpoint {S : Type u} {L : Type v} {P : Controller S L} {H : ℕ}
    {s t : S} {x y : ℕ × ℕ} {es : List Event} {l : L}
    (hr : Run P H s x es t y l) :
    ∀ A v, x = runWord A v → y = runWord (finalWord A es) v := by
  induction hr with
  | halt _ => intro A v hx; exact hx
  | compute _ _ ih => intro A v hx; exact ih A v hx
  | action _ _ ih =>
    intro A v hx
    exact ih (A ++ [_]) v (by rw [word_snoc, ← hx])
  | read _ _ ih => intro A v hx; exact ih A v hx

private theorem public_trace {S : Type u} {L : Type v} {P : Controller S L} {H : ℕ}
    {s t : S} {x y : ℕ × ℕ} {es : List Event} {l : L}
    (hr : Run P H s x es t y l) :
    ∀ A, PublicRun P (s, A) es (t, finalWord A es) l := by
  induction hr with
  | halt hs => intro A; exact .halt hs
  | compute hs _ ih => intro A; exact .compute hs (ih A)
  | action hs _ ih => intro A; exact .action hs (ih (A ++ [_]))
  | read hs _ ih => intro A; exact .read hs (ih A)

private theorem simulate {S : Type u} {L : Type v} {P : Controller S L} {H : ℕ}
    {s t : S} {x y : ℕ × ℕ} {es : List Event} {l : L}
    (hr : Run P H s x es t y l) :
    ∀ (A : List Bool) (v : ℕ × ℕ) (h : Hist (fun _ : List Bool => ℕ)),
      x = runWord A v → normalize P (replay P h) = normalize P (s, A) →
      execute (terminalGcd H) (selector P) (paidReads es + 1) h v =
        some (records A es, l) ∧
      normalize P (replay P (h ++ records A es)) = (t, finalWord A es) := by
  induction hr with
  | @halt s x l hs =>
    intro A v h hx he
    have hn : normalize P (s, A) = (s, A) :=
      normalize_terminal P _ (by simp [silent, hs])
    have hp : selector P h = .inr l := by simp [selector, he, hn, hs]
    simp [records, finalWord, execute, hp, he, hn]
  | @compute s s' x es t y l hs hr ih =>
    intro A v h hx he
    have hn := normalize_step P (s, A) (s', A) (by simp [silent, hs])
    exact ih A v h hx (he.trans hn)
  | @action s s' x b es t y l hs hr ih =>
    intro A v h hx he
    have hn := normalize_step P (s, A) (s', A ++ [b]) (by simp [silent, hs])
    exact ih (A ++ [b]) v h (by rw [word_snoc, ← hx]) (he.trans hn)
  | @read s k x es t y l hs hr ih =>
    intro A v h hx he
    have hn : normalize P (s, A) = (s, A) :=
      normalize_terminal P _ (by simp [silent, hs])
    have hp : selector P h = .inl A := by simp [selector, he, hn, hs]
    have hg : terminalGcd H A v = Nat.gcd (quantity x) H := by rw [terminalGcd, ← hx]
    have ha : replay P (h ++ [⟨A, terminalGcd H A v⟩]) =
        (k (Nat.gcd (quantity x) H), A) := by
      have append : replay P (h ++ [⟨A, terminalGcd H A v⟩]) =
          advance P (replay P h) ⟨A, terminalGcd H A v⟩ := by
        simp [replay, List.foldl_append]
      rw [append]
      simp only [advance, he, hn, hs, hg]
    obtain ⟨hi, hf⟩ := ih A v (h ++ [⟨A, terminalGcd H A v⟩]) hx (by rw [ha])
    constructor
    · change execute (terminalGcd H) (selector P) (paidReads es + 1 + 1) h v =
          some (⟨A, Nat.gcd (quantity x) H⟩ :: records A es, l)
      rw [execute, hp]
      dsimp only
      rw [hi]
      simp only [Option.map_some, hg]
    · simpa [records, finalWord, List.append_assoc, hg] using hf

/-- Every actual terminating run has exactly its reset execution, terminal
public state, cumulative action word and number of paid queries. The entire
original event tape, including arbitrary local intervals and post-read
operations, determines the displayed records and terminal configuration. -/
theorem continuous_transport {S : Type u} {L : Type v} (P : Controller S L) (H : ℕ)
    (es : List Event) (v : ℕ × ℕ) (t : S) (y : ℕ × ℕ) (l : L)
    (hr : Run P H P.initial v es t y l) :
    execute (terminalGcd H) (selector P) (paidReads es + 1) [] v =
        some (records [] es, l) ∧
    normalize P (replay P (records [] es)) = (t, finalWord [] es) ∧
    y = runWord (finalWord [] es) v ∧
    (records [] es).length = paidReads es ∧
    PublicRun P (P.initial, []) es (t, finalWord [] es) l := by
  obtain ⟨he, hf⟩ := simulate hr [] v [] rfl rfl
  exact ⟨he, hf, run_endpoint hr [] v rfl, record_count [] es, public_trace hr []⟩

/-- Full-class read lower bound. Only exact entry identification is needed;
behavior return and retained service may impose additional obligations. No
uniform bound on local work, source actions or termination time is assumed. -/
theorem continuous_acquisition_lower_bound {S : Type u}
    (H : ℕ) (hH : 1 ≤ H)
    (P : Controller S (ZMod H × ZMod H)) (J : ℕ)
    (successful : ∀ v : ℕ × ℕ, ∃ es t y,
      Run P H P.initial v es t y (residueSource H v) ∧ paidReads es ≤ J) :
    (if H = 1 then 0 else 2 * costBound H) ≤ J := by
  classical
  choose es t y run bound using successful
  have hm : J ∈ acquisitionBudgets H := by
    refine ⟨selector P, fun v => records [] (es v), fun v => paidReads (es v) + 1, ?_, ?_⟩
    · intro v
      exact (continuous_transport P H (es v) v (t v) (y v) _ (run v)).1
    · intro v
      rw [record_count]
      exact bound v
  exact (terminal_gcd_acquisition_cost H hH).1.2 hm

end D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
