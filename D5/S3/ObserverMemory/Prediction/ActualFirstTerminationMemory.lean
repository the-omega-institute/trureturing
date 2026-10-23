/- GID: D5/S3/ObserverMemory/Prediction/ActualFirstTerminationMemory
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/ActualFirstTerminationMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Operational first-termination pulses have finite minima without a computable uniform bound. -/

import Mathlib.Computability.TuringMachine.Config
import Mathlib.Computability.Halting
import D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap
import Mathlib.Computability.RE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Oldest8330Proposal.UniformFirstHitMemory

open D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap

/-- State counts of single-start unary Boolean output machines.
The start witnesses nonemptiness; there is no extra cardinality assumption. -/
def unarySizes (b : ℕ → Bool) : Set ℕ :=
  {k | ∃ (Q : Type) (_ : Fintype Q) (start : Q) (update : Q → Q)
    (readout : Q → Bool), Fintype.card Q = k ∧
      ∀ n, readout (update^[n] start) = b n}

/-- A single-start Boolean pulse and DP's all-tail, real-valued, zero-error
updater have exactly the same attainable state counts. -/
theorem single_start_dp_sizes (t : ℕ) :
    unarySizes (fun n => decide (n = t)) = updaterSizes t 0 := by
  classical
  ext k
  constructor
  · rintro ⟨Q, hQ, start, update, readout, hk, hc⟩
    letI : Fintype Q := hQ
    refine ⟨Q, hQ, (fun n => update^[n] start), update,
      (fun q => if readout q then (1 : ℝ) else 0), hk, ?_⟩
    intro n u
    have hiter : update^[u] (update^[n] start) = update^[n + u] start := by
      rw [← Function.iterate_add_apply, Nat.add_comm]
    rw [hiter]
    dsimp only
    rw [hc (n + u)]
    by_cases hn : n + u = t <;> simp [pulse, hn]
  · rintro ⟨Q, hQ, encode, update, readout, hk, hc⟩
    letI : Fintype Q := hQ
    refine ⟨Q, hQ, encode 0, update,
      (fun q => decide (readout q = 1)), hk, ?_⟩
    intro n
    have h := hc 0 n
    have heq : readout (update^[n] (encode 0)) = pulse t n := by
      have hz : |readout (update^[n] (encode 0)) - pulse t n| ≤ 0 := by
        simpa using h
      exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)
    dsimp only
    rw [heq]
    by_cases hn : n = t <;> simp [pulse, hn]

/-- Consumed DP specialization; the fixed-pulse count is not reproved. -/
private theorem pulse_minimum (t : ℕ) :
    IsLeast (unarySizes (fun n => decide (n = t))) (t + 2) := by
  rw [single_start_dp_sizes]
  exact (delayed_pulse_memory_gap t 0 0 (by norm_num) (by norm_num)).2.2

/-- The all-false stream has an attained one-state minimum. -/
private theorem zero_minimum :
    IsLeast (unarySizes (fun _ => false)) 1 := by
  constructor
  · exact ⟨Unit, inferInstance, (), id, (fun _ => false), by simp, by simp⟩
  · rintro k ⟨Q, hQ, start, update, readout, hk, hc⟩
    letI : Fintype Q := hQ
    have hpos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨start⟩
    omega

/-- Pointwise uniqueness identifies the entire Boolean stream from one hit. -/
private theorem single_pulse_shape (b : ℕ → Bool)
    (unique : ∀ i j, b i = true → b j = true → i = j)
    {t : ℕ} (hit : b t = true) : ∀ n, b n = decide (n = t) := by
  intro n
  by_cases hn : n = t
  · subst n
    simpa using hit
  · have hz : b n = false := by
      cases hb : b n with
      | false => rfl
      | true => exact False.elim (hn (unique n t hb hit))
    simp [hn, hz]

/-- Consumed transport of the DP minimum, with the pulse at the same index. -/
private theorem minimum_at_hit (b : ℕ → Bool)
    (unique : ∀ i j, b i = true → b j = true → i = j)
    {t : ℕ} (hit : b t = true) : IsLeast (unarySizes b) (t + 2) := by
  have hb : b = (fun n => decide (n = t)) := funext (single_pulse_shape b unique hit)
  rw [hb]
  exact pulse_minimum t

/-- Classical case distinction proves pointwise existence, without a computable
termination-time or automaton selector. The hit-zero case is included. -/
private theorem single_pulse_has_minimum (b : ℕ → Bool)
    (unique : ∀ i j, b i = true → b j = true → i = j) :
    ∃ k, IsLeast (unarySizes b) k := by
  classical
  by_cases hh : ∃ t, b t = true
  · obtain ⟨t, ht⟩ := hh
    exact ⟨t + 2, minimum_at_hit b unique ht⟩
  · have hz : b = (fun _ => false) := by
      funext n
      cases hn : b n with
      | false => rfl
      | true => exact False.elim (hh ⟨n, hn⟩)
    rw [hz]
    exact ⟨1, zero_minimum⟩

/-- Boolean search of indices strictly below the length. The user-facing cutoff
is inclusive, so the reduction uses length N(e)+1. -/
def prefixHit (b : ℕ → ℕ → Bool) (e : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => cond (b e n) true (prefixHit b e n)

private theorem prefix_hit_spec (b : ℕ → ℕ → Bool) (e N : ℕ) :
    prefixHit b e N = true ↔ ∃ n, n < N ∧ b e n = true := by
  induction N with
  | zero => simp [prefixHit]
  | succ N ih =>
    change cond (b e N) true (prefixHit b e N) = true ↔ _
    cases hb : b e N with
    | false =>
      change prefixHit b e N = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨n, hn, hbn⟩
        exact ⟨n, Nat.lt_succ_of_lt hn, hbn⟩
      · rintro ⟨n, hn, hbn⟩
        refine ⟨n, ?_, hbn⟩
        have hne : n ≠ N := by
          intro heq
          subst n
          simp [hb] at hbn
        omega
    | true =>
      change true = true ↔ _
      constructor
      · intro _
        exact ⟨N, Nat.lt_succ_self N, hb⟩
      · intro _
        rfl

private theorem prefix_hit_computable (b : ℕ → ℕ → Bool)
    (hb : Computable₂ b) : Computable₂ (prefixHit b) := by
  have hs : Computable₂ (fun (p : ℕ × ℕ) (q : ℕ × Bool) =>
      cond (b p.1 q.1) true q.2) := by
    exact Computable.cond
      (hb.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))
      (Computable.const true) (Computable.snd.comp Computable.snd)
  change Computable (fun p : ℕ × ℕ => prefixHit b p.1 p.2)
  apply (Computable.nat_rec (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ => false)
    (h := fun (p : ℕ × ℕ) (q : ℕ × Bool) => cond (b p.1 q.1) true q.2)
    Computable.snd (Computable.const false) hs).of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun z => cond (b p.1 n) true z) ih

/-- The same inclusive prefix property as in original section 6.4. -/
def ExhaustiveZeroPrefix (b : ℕ → ℕ → Bool) (N : ℕ → ℕ) : Prop :=
  ∀ e, (∀ n, n ≤ N e → b e n = false) → ∀ n, b e n = false

/-- A computable exhaustive cutoff would decide the existential predicate.
This is a class lemma, not a claim that an interpreter has been instantiated. -/
private theorem no_computable_prefix_cutoff (b : ℕ → ℕ → Bool)
    (hb : Computable₂ b)
    (undecidable : ¬ComputablePred (fun e => ∃ n, b e n = true)) :
    ¬∃ N : ℕ → ℕ, Computable N ∧ ExhaustiveZeroPrefix b N := by
  rintro ⟨N, hN, cut⟩
  have hp : Computable (fun e => prefixHit b e (N e + 1)) :=
    Computable.comp (prefix_hit_computable b hb)
      (Computable.id.pair (Computable.succ.comp hN))
  have hpred : ComputablePred (fun e => prefixHit b e (N e + 1) = true) := by
    apply Computable.computablePred
    exact hp.of_eq (fun e => by cases prefixHit b e (N e + 1) <;> rfl)
  apply undecidable
  apply hpred.of_eq
  intro e
  constructor
  · intro h
    obtain ⟨n, _, hn⟩ := (prefix_hit_spec b e (N e + 1)).mp h
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    by_contra hnone
    have hzero : ∀ k, k ≤ N e → b e k = false := by
      intro k hk
      cases hbk : b e k with
      | false => rfl
      | true =>
        exact False.elim (hnone ((prefix_hit_spec b e (N e + 1)).mpr
          ⟨k, by omega, hbk⟩))
    have hz := cut e hzero n
    simp [hn] at hz

/-- A bound on every attained minimum. No computable selector is asserted. -/
def MinimumStateBound (b : ℕ → ℕ → Bool) (s : ℕ → ℕ) : Prop :=
  ∀ e k, IsLeast (unarySizes (b e)) k → k ≤ s e

/-- General obstruction for uniformly computable, at-most-one-hit families.
The actual operational program family must separately establish ALL three
premises. In particular, this theorem does not close original section 6.4.

The finite machine is obtained per instance. The same index t is used in the
pulse, the DP minimum t+2, and the inclusive cutoff contradiction. -/
theorem uniform_single_pulse_obstruction (b : ℕ → ℕ → Bool)
    (hb : Computable₂ b)
    (unique : ∀ e i j, b e i = true → b e j = true → i = j)
    (undecidable : ¬ComputablePred (fun e => ∃ n, b e n = true)) :
    (∀ e, ∃ k, IsLeast (unarySizes (b e)) k) ∧
    (¬∃ s : ℕ → ℕ, Computable s ∧ MinimumStateBound b s) ∧
    (¬∃ N : ℕ → ℕ, Computable N ∧ ExhaustiveZeroPrefix b N) := by
  have noCut := no_computable_prefix_cutoff b hb undecidable
  constructor
  · intro e
    exact single_pulse_has_minimum (b e) (unique e)
  constructor
  · rintro ⟨s, hs, bound⟩
    apply noCut
    refine ⟨s, hs, ?_⟩
    intro e hzero n
    cases hn : b e n with
    | false => rfl
    | true =>
      have hmin := minimum_at_hit (b e) (unique e) hn
      have hcount : n + 2 ≤ s e := bound e (n + 2) hmin
      have hz := hzero n (by omega)
      simp [hn] at hz
  · exact noCut

end Oldest8330Proposal.UniformFirstHitMemory


/- Actual finite-data list program. Native time is one ToPartrec.step.
The exact 233-line supplier remains above, unchanged. No evaln fuel is used. -/
namespace Oldest8330Proposal.OperationalFirstTermination
open Nat.Partrec (Code)
open StateTransition
open Oldest8330Proposal.UniformFirstHitMemory
abbrev Data := List ℕ
abbrev Frame := (Code × Data) ⊕ (Data ⊕ (Code ⊕ Code))
abbrev Stack := List Frame
abbrev Cfg := Data ⊕ (Stack × Data)
abbrev NormalState := Code × Stack × Data
abbrev ReturnState := Stack × Data

def decodeCode : Code → Turing.ToPartrec.Code
  | .zero => .zero'
  | .succ => .succ
  | .left => .tail
  | .right => .zero'
  | .pair f g => .cons (decodeCode f) (decodeCode g)
  | .comp f g => .comp (decodeCode f) (decodeCode g)
  | .prec f g => .case (decodeCode f) (decodeCode g)
  | .rfind' f => .fix (decodeCode f)

def encodeCode : Turing.ToPartrec.Code → Code
  | .zero' => .zero
  | .succ => .succ
  | .tail => .left
  | .cons f g => .pair (encodeCode f) (encodeCode g)
  | .comp f g => .comp (encodeCode f) (encodeCode g)
  | .case f g => .prec (encodeCode f) (encodeCode g)
  | .fix f => .rfind' (encodeCode f)

private theorem decode_encode (c : Turing.ToPartrec.Code) :
    decodeCode (encodeCode c) = c := by
  induction c <;> simp_all [encodeCode, decodeCode]

def decodeStack : Stack → Turing.ToPartrec.Cont
  | [] => .halt
  | .inl (f, v) :: k => .cons₁ (decodeCode f) v (decodeStack k)
  | .inr (.inl v) :: k => .cons₂ v (decodeStack k)
  | .inr (.inr (.inl f)) :: k => .comp (decodeCode f) (decodeStack k)
  | .inr (.inr (.inr f)) :: k => .fix (decodeCode f) (decodeStack k)

def decodeCfg : Cfg → Turing.ToPartrec.Cfg
  | .inl v => .halt v
  | .inr (k, v) => .ret (decodeStack k) v

def normal : Code → Stack → Data → Cfg
  | .zero, k, v => .inr (k, 0 :: v)
  | .succ, k, v => .inr (k, [v.headI + 1])
  | .left, k, v => .inr (k, v.tail)
  | .right, k, v => .inr (k, 0 :: v)
  | .pair f g, k, v => normal f (.inl (g, v) :: k) v
  | .comp f g, k, v => normal g (.inr (.inr (.inl f)) :: k) v
  | .prec f g, k, v =>
      if v.headI = 0 then normal f k v.tail
      else normal g k (v.headI.pred :: v.tail)
  | .rfind' f, k, v => normal f (.inr (.inr (.inr f)) :: k) v

def returning : Stack → Data → Cfg
  | [], v => .inl v
  | .inl (f, saved) :: k, v => normal f (.inr (.inl v) :: k) saved
  | .inr (.inl saved) :: k, v => returning k (saved.headI :: v)
  | .inr (.inr (.inl f)) :: k, v => normal f k v
  | .inr (.inr (.inr f)) :: k, v =>
      if v.headI = 0 then returning k v.tail
      else normal f (.inr (.inr (.inr f)) :: k) v.tail

def step : Cfg → Option Cfg
  | .inl _ => none
  | .inr (k, v) => some (returning k v)

private theorem normal_decode (c : Code) (k : Stack) (v : Data) :
    decodeCfg (normal c k v) =
      Turing.ToPartrec.stepNormal (decodeCode c) (decodeStack k) v := by
  induction c generalizing k v with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair f g ihf ihg => simpa [normal, decodeCode, decodeStack, Turing.ToPartrec.stepNormal] using ihf (.inl (g,v)::k) v
  | comp f g ihf ihg => simpa [normal, decodeCode, decodeStack, Turing.ToPartrec.stepNormal] using ihg (.inr (.inr (.inl f))::k) v
  | prec f g ihf ihg =>
      cases hv : v.headI with
      | zero => simpa [normal, decodeCode, Turing.ToPartrec.stepNormal, hv] using ihf k v.tail
      | succ n => simpa [normal, decodeCode, Turing.ToPartrec.stepNormal, hv] using ihg k (n::v.tail)
  | rfind' f ih => simpa [normal, decodeCode, decodeStack, Turing.ToPartrec.stepNormal] using ih (.inr (.inr (.inr f))::k) v

private theorem returning_decode (k : Stack) (v : Data) :
    decodeCfg (returning k v) = Turing.ToPartrec.stepRet (decodeStack k) v := by
  induction k generalizing v with
  | nil => rfl
  | cons frame k ih =>
    rcases frame with ⟨f,saved⟩ | saved | f | f
    · simpa [returning, decodeStack, Turing.ToPartrec.stepRet]
        using normal_decode f (.inr (.inl v)::k) saved
    · simpa [returning, decodeStack, Turing.ToPartrec.stepRet] using ih (saved.headI::v)
    · simpa [returning, decodeStack, Turing.ToPartrec.stepRet] using normal_decode f k v
    · by_cases h : v.headI = 0
      · simpa [returning, decodeStack, Turing.ToPartrec.stepRet, h] using ih v.tail
      · simpa [returning, decodeStack, Turing.ToPartrec.stepRet, h]
          using normal_decode f (.inr (.inr (.inr f))::k) v.tail

/-- One encoded transition is one native transition, including the terminal case. -/
theorem step_decode (q : Cfg) :
    (step q).map decodeCfg = Turing.ToPartrec.step (decodeCfg q) := by
  rcases q with v | ⟨k,v⟩
  · rfl
  · simpa [step, decodeCfg, Turing.ToPartrec.step] using congrArg some (returning_decode k v)

/-- The infinite numbering: stop, then run fixed u on literal e. -/
def initial (u : Code) : ℕ → Cfg
  | 0 => .inl []
  | e + 1 => normal u [] [e]

def run (u : Code) (e : ℕ) : ℕ → Option Cfg
  | 0 => some (initial u e)
  | n + 1 => (run u e n).bind step

/-- Successful transitions before the terminal state; initial termination is t=0. -/
def pulse (u : Code) (e n : ℕ) : Bool :=
  (run u e n).isSome && !(run u e (n+1)).isSome

private theorem pulse_iff (u : Code) (e n : ℕ) :
    pulse u e n = true ↔ ∃ q, run u e n = some q ∧ step q = none := by
  cases h : run u e n with
  | none => simp [pulse, run, h]
  | some q => cases hs : step q <;> simp [pulse, run, h, hs]

private theorem run_none_after (u : Code) (e : ℕ) {n : ℕ}
    (h : run u e n = none) (d : ℕ) : run u e (n+d) = none := by
  induction d with
  | zero => simpa using h
  | succ d ih => simpa [Nat.add_succ, run, ih]

private theorem unique_pulse (u : Code) (e i j : ℕ)
    (hi : pulse u e i = true) (hj : pulse u e j = true) : i = j := by
  obtain ⟨qi,hi,hsi⟩ := (pulse_iff u e i).mp hi
  obtain ⟨qj,hj,hsj⟩ := (pulse_iff u e j).mp hj
  have ni : run u e (i+1) = none := by simp [run, hi, hsi]
  have nj : run u e (j+1) = none := by simp [run, hj, hsj]
  rcases lt_trichotomy i j with h | h | h
  · have hz := run_none_after u e ni (j-(i+1))
    have he : i+1+(j-(i+1)) = j := by omega
    rw [he, hj] at hz
    cases hz
  · exact h
  · have hz := run_none_after u e nj (i-(j+1))
    have he : j+1+(i-(j+1)) = i := by omega
    rw [he, hi] at hz
    cases hz

private theorem run_reaches (u : Code) (e n : ℕ) {q : Cfg}
    (h : run u e n = some q) : Reaches step (initial u e) q := by
  induction n generalizing q with
  | zero => cases Option.some.inj h; exact Relation.ReflTransGen.refl
  | succ n ih =>
      cases hn : run u e n with
      | none => simp [run, hn] at h
      | some r => exact (ih hn).tail (by simpa [run, hn] using h)

private theorem reaches_run (u : Code) (e : ℕ) {q : Cfg}
    (h : Reaches step (initial u e) q) : ∃ n, run u e n = some q := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | @tail q r hqr hstep ih =>
      obtain ⟨n,hn⟩ := ih
      exact ⟨n+1, by simpa [run, hn] using hstep⟩

private theorem eventually_pulse (u : Code) (e : ℕ) :
    (∃ n, pulse u e n = true) ↔ (eval step (initial u e)).Dom := by
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨q,hq,hs⟩ := (pulse_iff u e n).mp hn
    exact (mem_eval.mpr ⟨run_reaches u e n hq,hs⟩).1
  · intro h
    have hmem : (eval step (initial u e)).get h ∈ eval step (initial u e) := ⟨h,rfl⟩
    obtain ⟨hr,hs⟩ := mem_eval.mp hmem
    obtain ⟨n,hn⟩ := reaches_run u e hr
    exact ⟨n,(pulse_iff u e n).mpr ⟨_,hn,hs⟩⟩

/-- Bounded simulation preserves the native clock at every index. -/
private theorem run_decode (u : Code) (e n : ℕ) :
    (run u e n).map decodeCfg =
      (fun q : Option Turing.ToPartrec.Cfg => q.bind Turing.ToPartrec.step)^[n]
        (some (decodeCfg (initial u e))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ← ih]
      change ((run u e n).bind step).map decodeCfg =
        ((run u e n).map decodeCfg).bind Turing.ToPartrec.step
      cases h : run u e n with
      | none => rfl
      | some q => exact step_decode q

/-- First terminal state at exactly t, never an arbitrary later none witness. -/
theorem first_terminal (u : Code) (e t : ℕ) :
    pulse u e t = true ↔
      (∃ q, run u e t = some q ∧ step q = none) ∧
      ∀ n, n < t → pulse u e n = false := by
  constructor
  · intro h
    refine ⟨(pulse_iff u e t).mp h, ?_⟩
    intro n hn
    cases hb : pulse u e n with
    | false => rfl
    | true => have := unique_pulse u e n t hb h; omega
  · exact fun h => (pulse_iff u e t).mpr h.1

private theorem stop_zero (u : Code) : pulse u 0 0 = true := by rfl

private theorem decoded_eval (q : Cfg) :
    eval Turing.ToPartrec.step (decodeCfg q) = decodeCfg <$> eval step q := by
  apply StateTransition.tr_eval' step Turing.ToPartrec.step decodeCfg
  intro a b hab
  subst b
  have hc := step_decode a
  cases hs : step a with
  | none => simpa [hs] using hc.symm
  | some r =>
      refine ⟨decodeCfg r,rfl,Relation.TransGen.single ?_⟩
      simpa [hs] using hc.symm

private theorem actual_domain (u : Code) (e : ℕ) :
    (eval step (initial u (e+1))).Dom ↔ ((decodeCode u).eval [e]).Dom := by
  have h := congrArg Part.Dom (decoded_eval (initial u (e+1)))
  simpa [initial, normal_decode, decodeStack, Turing.ToPartrec.stepNormal_eval]
    using (Iff.of_eq h).symm


/- Each proof below concerns the standard effective encodings of sums,
products, lists and Nat.Partrec.Code. No arbitrary countability encoding. -/
syntax "data_comp" : tactic
macro_rules
  | `(tactic| data_comp) => `(tactic|
    first
    | exact Computable.id
    | exact Computable.fst
    | exact Computable.snd
    | exact Computable.const _
    | apply Computable.pair <;> data_comp
    | apply Computable.sumInl.comp <;> data_comp
    | apply Computable.sumInr.comp <;> data_comp
    | apply Computable.option_some.comp <;> data_comp
    | apply Computable.succ.comp <;> data_comp
    | apply Computable.pred.comp <;> data_comp
    | apply Primrec.list_headI.to_comp.comp <;> data_comp
    | apply Primrec.list_tail.to_comp.comp <;> data_comp
    | apply Primrec.list_head?.to_comp.comp <;> data_comp
    | apply Primrec.option_isSome.to_comp.comp <;> data_comp
    | apply Primrec.not.to_comp.comp <;> data_comp
    | apply Primrec.and.to_comp.comp <;> data_comp
    | apply Primrec.beq.to_comp.comp <;> data_comp
    | apply Computable.list_cons.comp <;> data_comp
    | apply Computable.fst.comp <;> data_comp
    | apply Computable.snd.comp <;> data_comp
    | apply Computable.cond <;> data_comp
    | apply Computable.nat_casesOn <;> data_comp
    | apply Computable.sumCasesOn <;> data_comp
    | apply Computable.option_casesOn <;> data_comp)

set_option backward.isDefEq.respectTransparency false

/-- One constructor layer of the standard effective code encoding. -/
def view : Code → ℕ × Code × Code
  | .zero => (0,.zero,.zero)
  | .succ => (1,.zero,.zero)
  | .left => (2,.zero,.zero)
  | .right => (3,.zero,.zero)
  | .pair f g => (4,f,g)
  | .comp f g => (5,f,g)
  | .prec f g => (6,f,g)
  | .rfind' f => (7,f,.zero)

private theorem view_computable : Computable view := by
  have h := Nat.Partrec.Code.computable_recOn (c := id) Computable.id
    (Computable.const (0,Code.zero,Code.zero))
    (Computable.const (1,Code.zero,Code.zero))
    (Computable.const (2,Code.zero,Code.zero))
    (Computable.const (3,Code.zero,Code.zero))
    (pr := fun _ p => (4,p.1,p.2.1))
      ((Computable.const 4).pair ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd))))
    (co := fun _ p => (5,p.1,p.2.1))
      ((Computable.const 5).pair ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd))))
    (pc := fun _ p => (6,p.1,p.2.1))
      ((Computable.const 6).pair ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd))))
    (rf := fun _ p => (7,p.1,Code.zero))
      ((Computable.const 7).pair ((Computable.fst.comp Computable.snd).pair
        (Computable.const Code.zero)))
  exact h.of_eq (fun c => by cases c <;> rfl)

abbrev NormalResult := Cfg ⊕ NormalState

def normalDispatch (p : (ℕ × Code × Code) × Stack × Data) : NormalResult :=
  let f := p.1.2.1
  let g := p.1.2.2
  let k := p.2.1
  let v := p.2.2
  match p.1.1 with
  | 0 => .inl (.inr (k,0::v))
  | 1 => .inl (.inr (k,[v.headI.succ]))
  | 2 => .inl (.inr (k,v.tail))
  | 3 => .inl (.inr (k,0::v))
  | 4 => .inr (f,.inl (g,v)::k,v)
  | 5 => .inr (g,.inr (.inr (.inl f))::k,v)
  | 6 => cond (v.headI == 0) (.inr (f,k,v.tail))
      (.inr (g,k,v.headI.pred::v.tail))
  | _ => .inr (f,.inr (.inr (.inr f))::k,v)

def normalBody (p : NormalState) : NormalResult :=
  normalDispatch (view p.1,p.2)

private theorem normal_body_computable : Computable normalBody := by
  let P := (ℕ × Code × Code) × Stack × Data
  have hn : Computable (fun p : P => p.1.1) := Computable.fst.comp Computable.fst
  have hf : Computable (fun p : P => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hg : Computable (fun p : P => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hk : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have hv : Computable (fun p : P => p.2.2) := Computable.snd.comp Computable.snd
  have hh : Computable (fun p : P => p.2.2.headI) := Primrec.list_headI.to_comp.comp hv
  have ht : Computable (fun p : P => p.2.2.tail) := Primrec.list_tail.to_comp.comp hv
  have h0 : Computable (fun p : P => (Sum.inl (Sum.inr (p.2.1,0::p.2.2)) : NormalResult)) :=
    Computable.sumInl.comp (Computable.sumInr.comp
      (hk.pair (Computable.list_cons.comp (Computable.const 0) hv)))
  have h1 : Computable (fun p : P =>
      (Sum.inl (Sum.inr (p.2.1,[p.2.2.headI.succ])) : NormalResult)) :=
    Computable.sumInl.comp (Computable.sumInr.comp
      (hk.pair (Computable.list_cons.comp (Computable.succ.comp hh) (Computable.const []))))
  have h2 : Computable (fun p : P => (Sum.inl (Sum.inr (p.2.1,p.2.2.tail)) : NormalResult)) :=
    Computable.sumInl.comp (Computable.sumInr.comp (hk.pair ht))
  have h4 : Computable (fun p : P =>
      (Sum.inr (p.1.2.1,Sum.inl (p.1.2.2,p.2.2)::p.2.1,p.2.2) : NormalResult)) :=
    Computable.sumInr.comp (hf.pair
      ((Computable.list_cons.comp (Computable.sumInl.comp (hg.pair hv)) hk).pair hv))
  have h5 : Computable (fun p : P =>
      (Sum.inr (p.1.2.2,Sum.inr (Sum.inr (Sum.inl p.1.2.1))::p.2.1,p.2.2) : NormalResult)) :=
    Computable.sumInr.comp (hg.pair
      ((Computable.list_cons.comp
        (Computable.sumInr.comp (Computable.sumInr.comp (Computable.sumInl.comp hf))) hk).pair hv))
  have h6 : Computable ((fun p : P =>
      cond (p.2.2.headI == 0) (Sum.inr (p.1.2.1,p.2.1,p.2.2.tail))
        (Sum.inr (p.1.2.2,p.2.1,p.2.2.headI.pred::p.2.2.tail))) : P → NormalResult) :=
    Computable.cond (Primrec.beq.to_comp.comp hh (Computable.const 0))
      (Computable.sumInr.comp (hf.pair (hk.pair ht)))
      (Computable.sumInr.comp (hg.pair
        (hk.pair (Computable.list_cons.comp (Computable.pred.comp hh) ht))))
  have h7 : Computable (fun p : P =>
      (Sum.inr (p.1.2.1,Sum.inr (Sum.inr (Sum.inr p.1.2.1))::p.2.1,p.2.2) : NormalResult)) :=
    Computable.sumInr.comp (hf.pair
      ((Computable.list_cons.comp
        (Computable.sumInr.comp (Computable.sumInr.comp (Computable.sumInr.comp hf))) hk).pair hv))
  let F : P → NormalResult := fun p =>
    cond (p.1.1 == 0) (.inl (.inr (p.2.1,0::p.2.2)))
    (cond (p.1.1 == 1) (.inl (.inr (p.2.1,[p.2.2.headI.succ])))
    (cond (p.1.1 == 2) (.inl (.inr (p.2.1,p.2.2.tail)))
    (cond (p.1.1 == 3) (.inl (.inr (p.2.1,0::p.2.2)))
    (cond (p.1.1 == 4) (.inr (p.1.2.1,.inl (p.1.2.2,p.2.2)::p.2.1,p.2.2))
    (cond (p.1.1 == 5) (.inr (p.1.2.2,.inr (.inr (.inl p.1.2.1))::p.2.1,p.2.2))
    (cond (p.1.1 == 6)
      (cond (p.2.2.headI == 0) (.inr (p.1.2.1,p.2.1,p.2.2.tail))
        (.inr (p.1.2.2,p.2.1,p.2.2.headI.pred::p.2.2.tail)))
      (.inr (p.1.2.1,.inr (.inr (.inr p.1.2.1))::p.2.1,p.2.2))))))))
  have hF : Computable F :=
    Computable.cond (Primrec.beq.to_comp.comp hn (Computable.const 0)) h0
      (Computable.cond (Primrec.beq.to_comp.comp hn (Computable.const 1)) h1
      (Computable.cond (Primrec.beq.to_comp.comp hn (Computable.const 2)) h2
      (Computable.cond (Primrec.beq.to_comp.comp hn (Computable.const 3)) h0
      (Computable.cond (Primrec.beq.to_comp.comp hn (Computable.const 4)) h4
      (Computable.cond (Primrec.beq.to_comp.comp hn (Computable.const 5)) h5
      (Computable.cond (Primrec.beq.to_comp.comp hn (Computable.const 6)) h6 h7))))))
  have hd : Computable normalDispatch := by
    apply hF.of_eq
    intro p
    rcases p with ⟨⟨n,f,g⟩,k,v⟩
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
            cases n with
            | zero => rfl
            | succ n =>
              cases n with
              | zero => rfl
              | succ n =>
                cases n with
                | zero => rfl
                | succ n =>
                  rfl
  exact hd.comp ((view_computable.comp Computable.fst).pair Computable.snd)

/-- Structural normalization is a total computable unbounded loop. It costs
zero native transitions, as in the pinned operational semantics. -/
private theorem normal_fix (c : Code) (k : Stack) (v : Data) :
    normal c k v ∈ PFun.fix (fun p => Part.some (normalBody p)) (c,k,v) := by
  induction c generalizing k v with
  | zero => apply PFun.mem_fix_iff.mpr; exact Or.inl (by simp [normalBody,normalDispatch,view,normal])
  | succ => apply PFun.mem_fix_iff.mpr; exact Or.inl (by simp [normalBody,normalDispatch,view,normal])
  | left => apply PFun.mem_fix_iff.mpr; exact Or.inl (by simp [normalBody,normalDispatch,view,normal])
  | right => apply PFun.mem_fix_iff.mpr; exact Or.inl (by simp [normalBody,normalDispatch,view,normal])
  | pair f g ihf ihg =>
      apply PFun.mem_fix_iff.mpr
      exact Or.inr ⟨_,by simp [normalBody,normalDispatch,view],ihf _ _⟩
  | comp f g ihf ihg =>
      apply PFun.mem_fix_iff.mpr
      exact Or.inr ⟨_,by simp [normalBody,normalDispatch,view],ihg _ _⟩
  | prec f g ihf ihg =>
      apply PFun.mem_fix_iff.mpr
      by_cases h : v.headI = 0
      · exact Or.inr ⟨(f,k,v.tail),by simp [normalBody,normalDispatch,view,h],by simpa [normal,h] using ihf k v.tail⟩
      · exact Or.inr ⟨(g,k,v.headI.pred::v.tail),by simp [normalBody,normalDispatch,view,h],by simpa [normal,h] using ihg k (v.headI.pred::v.tail)⟩
  | rfind' f ih =>
      apply PFun.mem_fix_iff.mpr
      exact Or.inr ⟨_,by simp [normalBody,normalDispatch,view],ih _ _⟩

private theorem normal_computable : Computable (fun p : NormalState => normal p.1 p.2.1 p.2.2) := by
  exact (Partrec.fix normal_body_computable.partrec).of_eq_tot
    (fun p => normal_fix p.1 p.2.1 p.2.2)

abbrev ReturnResult := Cfg ⊕ ReturnState

def returnFrame (p : Frame × Stack × Data) : ReturnResult :=
  let k := p.2.1
  let v := p.2.2
  match p.1 with
  | .inl (f,saved) => .inl (normal f (.inr (.inl v)::k) saved)
  | .inr (.inl saved) => .inr (k,saved.headI::v)
  | .inr (.inr (.inl f)) => .inl (normal f k v)
  | .inr (.inr (.inr f)) => cond (v.headI == 0) (.inr (k,v.tail))
      (.inl (normal f (.inr (.inr (.inr f))::k) v.tail))

def returnBody (p : ReturnState) : ReturnResult :=
  match p.1.head? with
  | none => .inl (.inl p.2)
  | some frame => returnFrame (frame,p.1.tail,p.2)

private theorem return_frame_computable : Computable returnFrame := by
  have hfinish : Computable (fun p : NormalState =>
      (Sum.inl (normal p.1 p.2.1 p.2.2) : ReturnResult)) :=
    Computable.comp (f := @Sum.inl Cfg ReturnState)
      (g := fun p : NormalState => normal p.1 p.2.1 p.2.2)
      Computable.sumInl normal_computable
  let L := (Code × Data) × ReturnState
  have hlf : Computable (fun p : L => p.1.1) :=
    Computable.comp (f := Prod.fst) (g := Prod.fst) Computable.fst Computable.fst
  have hls : Computable (fun p : L => p.1.2) :=
    Computable.comp (f := Prod.snd) (g := Prod.fst) Computable.snd Computable.fst
  have hlk : Computable (fun p : L => p.2.1) :=
    Computable.comp (f := Prod.fst) (g := Prod.snd) Computable.fst Computable.snd
  have hlv : Computable (fun p : L => p.2.2) :=
    Computable.comp (f := Prod.snd) (g := Prod.snd) Computable.snd Computable.snd
  have hlframe : Computable (fun p : L => (Sum.inr (Sum.inl p.2.2) : Frame)) :=
    Computable.comp (f := @Sum.inr (Code × Data) (Data ⊕ (Code ⊕ Code)))
      (g := fun p : L => (Sum.inl p.2.2 : Data ⊕ (Code ⊕ Code)))
      Computable.sumInr
      (Computable.comp (f := @Sum.inl Data (Code ⊕ Code)) (g := fun p : L => p.2.2)
        Computable.sumInl hlv)
  have hlstack : Computable (fun p : L =>
      (Sum.inr (Sum.inl p.2.2) : Frame) :: p.2.1) :=
    Computable₂.comp Computable.list_cons hlframe hlk
  have hlargs : Computable (fun p : L =>
      (p.1.1, (Sum.inr (Sum.inl p.2.2) : Frame) :: p.2.1, p.1.2)) :=
    Computable.pair hlf (Computable.pair hlstack hls)
  let left : L → ReturnResult := fun p =>
    .inl (normal p.1.1 (.inr (.inl p.2.2) :: p.2.1) p.1.2)
  have hleft : Computable left :=
    Computable.comp
      (f := fun p : NormalState => (Sum.inl (normal p.1 p.2.1 p.2.2) : ReturnResult))
      (g := fun p : L => (p.1.1, (Sum.inr (Sum.inl p.2.2) : Frame) :: p.2.1, p.1.2))
      hfinish hlargs
  have hnk : Computable (fun p : NormalState => p.2.1) :=
    Computable.comp (f := Prod.fst) (g := Prod.snd) Computable.fst Computable.snd
  have hnv : Computable (fun p : NormalState => p.2.2) :=
    Computable.comp (f := Prod.snd) (g := Prod.snd) Computable.snd Computable.snd
  have hhead : Computable (fun p : NormalState => p.2.2.headI) :=
    Computable.comp (f := List.headI) (g := fun p : NormalState => p.2.2) Primrec.list_headI.to_comp hnv
  have htail : Computable (fun p : NormalState => p.2.2.tail) :=
    Computable.comp (f := List.tail) (g := fun p : NormalState => p.2.2) Primrec.list_tail.to_comp hnv
  have htest : Computable (fun p : NormalState => p.2.2.headI == 0) :=
    Computable₂.comp Primrec.beq.to_comp hhead (Computable.const 0)
  have hhalt : Computable (fun p : NormalState =>
      (Sum.inr (p.2.1, p.2.2.tail) : ReturnResult)) :=
    Computable.comp (f := @Sum.inr Cfg ReturnState)
      (g := fun p : NormalState => (p.2.1, p.2.2.tail))
      Computable.sumInr (Computable.pair hnk htail)
  have hfixframe : Computable (fun p : NormalState =>
      (Sum.inr (Sum.inr (Sum.inr p.1)) : Frame)) :=
    Computable.comp (f := @Sum.inr (Code × Data) (Data ⊕ (Code ⊕ Code)))
      (g := fun p : NormalState => (Sum.inr (Sum.inr p.1) : Data ⊕ (Code ⊕ Code)))
      Computable.sumInr
      (Computable.comp (f := @Sum.inr Data (Code ⊕ Code))
        (g := fun p : NormalState => (Sum.inr p.1 : Code ⊕ Code)) Computable.sumInr
        (Computable.comp (f := @Sum.inr Code Code) (g := fun p : NormalState => p.1)
          Computable.sumInr Computable.fst))
  have hfixstack : Computable (fun p : NormalState =>
      (Sum.inr (Sum.inr (Sum.inr p.1)) : Frame) :: p.2.1) :=
    Computable₂.comp Computable.list_cons hfixframe hnk
  have hfixargs : Computable (fun p : NormalState =>
      (p.1, (Sum.inr (Sum.inr (Sum.inr p.1)) : Frame) :: p.2.1, p.2.2.tail)) :=
    Computable.pair Computable.fst (Computable.pair hfixstack htail)
  let fixBranch : NormalState → ReturnResult := fun p =>
    cond (p.2.2.headI == 0) (.inr (p.2.1, p.2.2.tail))
      (.inl (normal p.1 (.inr (.inr (.inr p.1)) :: p.2.1) p.2.2.tail))
  have hfix : Computable fixBranch :=
    Computable.cond htest hhalt
      (Computable.comp
        (f := fun p : NormalState => (Sum.inl (normal p.1 p.2.1 p.2.2) : ReturnResult))
        (g := fun p : NormalState =>
          (p.1, (Sum.inr (Sum.inr (Sum.inr p.1)) : Frame) :: p.2.1, p.2.2.tail))
        hfinish hfixargs)
  let C := (Code ⊕ Code) × ReturnState
  have hcargs : Computable (fun p : C × Code => (p.2, p.1.2)) :=
    Computable.pair Computable.snd (Computable.comp (f := Prod.snd) (g := Prod.fst) Computable.snd Computable.fst)
  have hcplain : Computable (fun p : C × Code =>
      (Sum.inl (normal p.2 p.1.2.1 p.1.2.2) : ReturnResult)) :=
    Computable.comp
      (f := fun p : NormalState => (Sum.inl (normal p.1 p.2.1 p.2.2) : ReturnResult))
      (g := fun p : C × Code => (p.2, p.1.2)) hfinish hcargs
  have hcfix : Computable (fun p : C × Code => fixBranch (p.2, p.1.2)) :=
    Computable.comp (f := fixBranch)
      (g := fun p : C × Code => (p.2, p.1.2)) hfix hcargs
  let codes : C → ReturnResult := fun p =>
    Sum.casesOn (motive := fun _ => ReturnResult) p.1 (fun f => .inl (normal f p.2.1 p.2.2))
      (fun f => fixBranch (f, p.2))
  have hcodes : Computable codes :=
    Computable.sumCasesOn (σ := ReturnResult)
      (f := fun p : C => p.1)
      (g := fun (p : C) (f : Code) => (Sum.inl (normal f p.2.1 p.2.2) : ReturnResult))
      (h := fun (p : C) (f : Code) => fixBranch (f, p.2))
      Computable.fst hcplain.to₂ hcfix.to₂
  let S := Data × ReturnState
  have hsavedhead : Computable (fun p : S => p.1.headI) :=
    Computable.comp (f := List.headI) (g := Prod.fst) Primrec.list_headI.to_comp Computable.fst
  have hsavedk : Computable (fun p : S => p.2.1) :=
    Computable.comp (f := Prod.fst) (g := Prod.snd) Computable.fst Computable.snd
  have hsavedv : Computable (fun p : S => p.2.2) :=
    Computable.comp (f := Prod.snd) (g := Prod.snd) Computable.snd Computable.snd
  let saved : S → ReturnResult := fun p => .inr (p.2.1, p.1.headI :: p.2.2)
  have hsaved : Computable saved :=
    Computable.comp (f := @Sum.inr Cfg ReturnState)
      (g := fun p : S => (p.2.1, p.1.headI :: p.2.2))
      Computable.sumInr (Computable.pair hsavedk
        (Computable₂.comp Computable.list_cons hsavedhead hsavedv))
  let R := (Data ⊕ (Code ⊕ Code)) × ReturnState
  have hrsargs : Computable (fun p : R × Data => (p.2, p.1.2)) :=
    Computable.pair Computable.snd (Computable.comp (f := Prod.snd) (g := Prod.fst) Computable.snd Computable.fst)
  have hrcargs : Computable (fun p : R × (Code ⊕ Code) => (p.2, p.1.2)) :=
    Computable.pair Computable.snd (Computable.comp (f := Prod.snd) (g := Prod.fst) Computable.snd Computable.fst)
  have hrs : Computable (fun p : R × Data => saved (p.2, p.1.2)) :=
    Computable.comp (f := saved) (g := fun p : R × Data => (p.2, p.1.2)) hsaved hrsargs
  have hrc : Computable (fun p : R × (Code ⊕ Code) => codes (p.2, p.1.2)) :=
    Computable.comp (f := codes)
      (g := fun p : R × (Code ⊕ Code) => (p.2, p.1.2)) hcodes hrcargs
  let rest : R → ReturnResult := fun p =>
    Sum.casesOn (motive := fun _ => ReturnResult) p.1 (fun v => saved (v, p.2)) (fun c => codes (c, p.2))
  have hrest : Computable rest :=
    Computable.sumCasesOn (σ := ReturnResult)
      (f := fun p : R => p.1)
      (g := fun (p : R) (v : Data) => saved (v, p.2))
      (h := fun (p : R) (c : Code ⊕ Code) => codes (c, p.2))
      Computable.fst hrs.to₂ hrc.to₂
  let P := Frame × ReturnState
  have hplargs : Computable (fun p : P × (Code × Data) => (p.2, p.1.2)) :=
    Computable.pair Computable.snd (Computable.comp (f := Prod.snd) (g := Prod.fst) Computable.snd Computable.fst)
  have hprargs : Computable (fun p : P × (Data ⊕ (Code ⊕ Code)) => (p.2, p.1.2)) :=
    Computable.pair Computable.snd (Computable.comp (f := Prod.snd) (g := Prod.fst) Computable.snd Computable.fst)
  have hpl : Computable (fun p : P × (Code × Data) => left (p.2, p.1.2)) :=
    Computable.comp (f := left)
      (g := fun p : P × (Code × Data) => (p.2, p.1.2)) hleft hplargs
  have hpr : Computable (fun p : P × (Data ⊕ (Code ⊕ Code)) => rest (p.2, p.1.2)) :=
    Computable.comp (f := rest)
      (g := fun p : P × (Data ⊕ (Code ⊕ Code)) => (p.2, p.1.2)) hrest hprargs
  have h : Computable (fun p : P =>
      Sum.casesOn (motive := fun _ => ReturnResult) p.1 (fun fs => left (fs, p.2)) (fun r => rest (r, p.2))) :=
    Computable.sumCasesOn (σ := ReturnResult)
      (f := fun p : P => p.1)
      (g := fun (p : P) (fs : Code × Data) => left (fs, p.2))
      (h := fun (p : P) (r : Data ⊕ (Code ⊕ Code)) => rest (r, p.2))
      Computable.fst hpl.to₂ hpr.to₂
  exact h.of_eq (fun p => by
    rcases p with ⟨frame, k, v⟩
    rcases frame with ⟨f, s⟩ | s | f | f <;> rfl)

private theorem return_body_computable : Computable returnBody := by
  have hhead : Computable (fun p : ReturnState => p.1.head?) :=
    Computable.comp (f := List.head?) (g := Prod.fst) Primrec.list_head?.to_comp Computable.fst
  have hnone : Computable (fun p : ReturnState =>
      (Sum.inl (Sum.inl p.2) : ReturnResult)) :=
    Computable.comp (f := @Sum.inl Cfg ReturnState)
      (g := fun p : ReturnState => (Sum.inl p.2 : Cfg)) Computable.sumInl
      (Computable.comp (f := @Sum.inl Data ReturnState) (g := Prod.snd)
        Computable.sumInl Computable.snd)
  let P := ReturnState × Frame
  have hframe : Computable (fun p : P => p.2) := Computable.snd
  have htail : Computable (fun p : P => p.1.1.tail) :=
    Computable.comp (f := List.tail) (g := fun p : P => p.1.1) Primrec.list_tail.to_comp
      (Computable.comp (f := Prod.fst) (g := Prod.fst) Computable.fst Computable.fst)
  have hvalue : Computable (fun p : P => p.1.2) :=
    Computable.comp (f := Prod.snd) (g := Prod.fst) Computable.snd Computable.fst
  have hargs : Computable (fun p : P => (p.2, p.1.1.tail, p.1.2)) :=
    Computable.pair hframe (Computable.pair htail hvalue)
  have hsome : Computable (fun p : P => returnFrame (p.2, p.1.1.tail, p.1.2)) :=
    Computable.comp (f := returnFrame)
      (g := fun p : P => (p.2, p.1.1.tail, p.1.2)) return_frame_computable hargs
  have h : Computable (fun p : ReturnState =>
      Option.casesOn (motive := fun _ => ReturnResult) p.1.head? (Sum.inl (Sum.inl p.2) : ReturnResult)
        (fun frame => returnFrame (frame, p.1.tail, p.2))) :=
    Computable.option_casesOn (σ := ReturnResult)
      (o := fun p : ReturnState => p.1.head?)
      (f := fun p : ReturnState => (Sum.inl (Sum.inl p.2) : ReturnResult))
      (g := fun (p : ReturnState) (frame : Frame) => returnFrame (frame, p.1.tail, p.2))
      hhead hnone hsome.to₂
  exact h.of_eq (fun p => by
    rcases p with ⟨k, v⟩
    cases k <;> rfl)

private theorem returning_fix (k : Stack) (v : Data) :
    returning k v ∈ PFun.fix (fun p => Part.some (returnBody p)) (k,v) := by
  induction k generalizing v with
  | nil => apply PFun.mem_fix_iff.mpr; exact Or.inl (by simp [returnBody,returning])
  | cons frame k ih =>
    apply PFun.mem_fix_iff.mpr
    rcases frame with ⟨f,saved⟩ | saved | f | f
    · exact Or.inl (by simp [returnBody,returnFrame,returning])
    · exact Or.inr ⟨_,by simp [returnBody,returnFrame],ih _⟩
    · exact Or.inl (by simp [returnBody,returnFrame,returning])
    · by_cases h : v.headI = 0
      · exact Or.inr ⟨(k,v.tail),by simp [returnBody,returnFrame,h],by simpa [returning,h] using ih v.tail⟩
      · exact Or.inl (by simp [returnBody,returnFrame,returning,h])

private theorem returning_computable : Computable (fun p : ReturnState => returning p.1 p.2) := by
  exact (Partrec.fix return_body_computable.partrec).of_eq_tot
    (fun p => returning_fix p.1 p.2)

private theorem step_computable : Computable step := by
  have h : Computable ((fun q : Cfg => Sum.casesOn (motive := fun _ => Option Cfg) q
      (fun _ => (none : Option Cfg))
      (fun kv => some (returning kv.1 kv.2))) : (Cfg) → Option Cfg) := by
    apply Computable.sumCasesOn (σ := (Option Cfg)) Computable.id
    · exact Computable.const none
    · exact Computable.option_some.comp (returning_computable.comp Computable.snd)
  apply h.of_eq
  intro q
  rcases q with v | ⟨k,v⟩ <;> rfl

private theorem initial_computable (u : Code) : Computable (initial u) := by
  have hsingleton : Computable (fun p : ℕ × ℕ => [p.2]) :=
    Computable₂.comp Computable.list_cons Computable.snd (Computable.const [])
  have hargs : Computable (fun p : ℕ × ℕ => (u, ([] : Stack), [p.2])) :=
    Computable.pair (Computable.const u)
      (Computable.pair (Computable.const []) hsingleton)
  have hsucc : Computable (fun p : ℕ × ℕ => normal u [] [p.2]) :=
    Computable.comp (f := fun p : NormalState => normal p.1 p.2.1 p.2.2)
      (g := fun p : ℕ × ℕ => (u, ([] : Stack), [p.2])) normal_computable hargs
  have h : Computable (fun e : ℕ =>
      Nat.casesOn (motive := fun _ => Cfg) e (Sum.inl [] : Cfg)
        (fun n => normal u [] [n])) :=
    Computable.nat_casesOn (σ := Cfg) Computable.id
      (Computable.const (Sum.inl [] : Cfg)) hsucc.to₂
  exact h.of_eq (fun e => by cases e <;> rfl)

private theorem run_computable (u : Code) : Computable₂ (run u) := by
  have hs : Computable₂ (fun (_ : ℕ × ℕ) (q : ℕ × Option Cfg) => q.2.bind step) := by
    apply Computable.option_bind (Computable.snd.comp Computable.snd)
    exact step_computable.comp Computable.snd
  apply (Computable.nat_rec Computable.snd
    (Computable.option_some.comp (initial_computable u |>.comp Computable.fst)) hs).of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => exact congrArg (fun q => q.bind step) ih

private theorem pulse_computable (u : Code) : Computable₂ (pulse u) := by
  unfold pulse
  apply Primrec.and.to_comp.comp
  · exact Primrec.option_isSome.to_comp.comp (run_computable u)
  · apply Primrec.not.to_comp.comp
    apply Primrec.option_isSome.to_comp.comp
    exact (run_computable u).comp Computable.fst (Computable.succ.comp Computable.snd)


/-- Choose one universal list code, then use e only as finite input data. -/
private theorem universal_exists : ∃ u : Code, ∀ e : ℕ,
    (decodeCode u).eval [e] = List.singleton <$> (Nat.Partrec.Code.ofNatCode e).eval 0 := by
  have hp : Partrec (fun e => (Nat.Partrec.Code.ofNatCode e).eval 0) :=
    Nat.Partrec.Code.eval_part.comp
      ((Computable.ofNat Code).of_eq (fun _ => rfl)) (Computable.const 0)
  obtain ⟨c, hc⟩ := Turing.ToPartrec.Code.exists_code
    (Nat.Partrec'.part_iff₁.mpr hp)
  refine ⟨encodeCode c, ?_⟩
  intro e
  have hsingleton : (pure : ℕ → List ℕ) = List.singleton := by
    funext n
    exact List.pure_def n
  have he : c.eval [e] =
      Part.map (pure : ℕ → List ℕ) ((Nat.Partrec.Code.ofNatCode e).eval 0) := by
    simpa only [List.Vector.head, Part.map_eq_map] using
      hc (⟨[e], rfl⟩ : List.Vector ℕ 1)
  rw [hsingleton] at he
  calc
    (decodeCode (encodeCode c)).eval [e] = c.eval [e] :=
      congrArg (fun d : Turing.ToPartrec.Code => d.eval [e]) (decode_encode c)
    _ = Part.map List.singleton ((Nat.Partrec.Code.ofNatCode e).eval 0) := he
    _ = List.singleton <$> (Nat.Partrec.Code.ofNatCode e).eval 0 :=
      (Part.map_eq_map List.singleton ((Nat.Partrec.Code.ofNatCode e).eval 0)).symm

private theorem actual_undecidable (u : Code)
    (hu : ∀ e : ℕ, (decodeCode u).eval [e] =
      List.singleton <$> (Nat.Partrec.Code.ofNatCode e).eval 0) :
    ¬ComputablePred (fun e => ∃ n, pulse u e n = true) := by
  rintro ⟨d,hd⟩
  letI := d
  apply ComputablePred.halting_problem 0
  have hc : Computable (fun c : Code => Encodable.encode c + 1) :=
    Computable.succ.comp Computable.encode
  have hpred : ComputablePred (fun c : Code =>
      ∃ n, pulse u (Encodable.encode c + 1) n = true) :=
    ⟨inferInstance,hd.comp hc⟩
  apply hpred.of_eq
  intro c
  rw [eventually_pulse,actual_domain,hu]
  simp [← Nat.Partrec.Code.ofNatCode_eq]

/-- Full original root: a concrete infinite program numbering with exact native
first-termination pulse, uniform total computability, finite unary realization,
sharp minima (one or t+2), and both universal computable-bound obstructions. -/
theorem original_section_6_4 : ∃ u : Code,
    (∀ e : ℕ, (decodeCode u).eval [e] =
      List.singleton <$> (Nat.Partrec.Code.ofNatCode e).eval 0) ∧
    Computable₂ (pulse u) ∧
    (∀ e n, (run u e n).map decodeCfg =
      (fun q : Option Turing.ToPartrec.Cfg => q.bind Turing.ToPartrec.step)^[n]
        (some (decodeCfg (initial u e)))) ∧
    (∀ e t, pulse u e t = true ↔
      (∃ q, run u e t = some q ∧ step q = none) ∧
      ∀ n, n < t → pulse u e n = false) ∧
    pulse u 0 0 = true ∧
    (∀ e, (∀ n, pulse u e n = false) → IsLeast (unarySizes (pulse u e)) 1) ∧
    (∀ e t, pulse u e t = true → IsLeast (unarySizes (pulse u e)) (t+2)) ∧
    (∀ e, ∃ k, IsLeast (unarySizes (pulse u e)) k) ∧
    (¬∃ s : ℕ → ℕ, Computable s ∧ MinimumStateBound (pulse u) s) ∧
    (¬∃ N : ℕ → ℕ, Computable N ∧ ExhaustiveZeroPrefix (pulse u) N) := by
  obtain ⟨u,hu⟩ := universal_exists
  have hc := pulse_computable u
  have hunique := unique_pulse u
  have hroot := uniform_single_pulse_obstruction (pulse u) hc hunique
    (actual_undecidable u hu)
  refine ⟨u,hu,hc,run_decode u,first_terminal u,stop_zero u,?_,?_,hroot⟩
  · intro e hz
    have he : pulse u e = (fun _ => false) := funext hz
    rw [he]
    exact Oldest8330Proposal.UniformFirstHitMemory.zero_minimum
  · intro e t ht
    exact Oldest8330Proposal.UniformFirstHitMemory.minimum_at_hit
      (pulse u e) (unique_pulse u e) ht

end Oldest8330Proposal.OperationalFirstTermination
