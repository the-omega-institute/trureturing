/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalStopping
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalStopping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual renewal bits and arbitrary raw updates give the stopped epoch and paid tick bound. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical Finset
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping
open FreshServiceRestart

/-- Number of bits through the n-th tick, with the first tick indexed by zero.
    The gap coordinate is a zero count, and may itself be zero. -/
def clock (wait : ℕ) (gaps : ℕ → ℕ) : ℕ → ℕ
  | 0 => wait + 1
  | n + 1 => clock wait gaps n + gaps n + 1

theorem clock_strict (wait : ℕ) (gaps : ℕ → ℕ) :
    StrictMono (clock wait gaps) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [clock]
  omega

private theorem clock_lower (wait : ℕ) (gaps : ℕ → ℕ) (n : ℕ) :
    n + 1 ≤ clock wait gaps n := by
  induction n with
  | zero => simp [clock]
  | succ n ih => simp only [clock]; omega

/-- A bounded search generates the actual source bit at absolute index t.
    Only tick positions at most t are examined; this is not an epoch kernel. -/
def sourceBit (wait : ℕ) (gaps : ℕ → ℕ) (t : ℕ) : Bool :=
  decide (∃ n ∈ range (t + 1), clock wait gaps n = t + 1)

private theorem bit_iff (wait : ℕ) (gaps : ℕ → ℕ) (t : ℕ) :
    sourceBit wait gaps t = true ↔ ∃ n, clock wait gaps n = t + 1 := by
  simp only [sourceBit, decide_eq_true_eq]
  constructor
  · rintro ⟨n, _, hn⟩; exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, mem_range.mpr (by have := clock_lower wait gaps n; omega), hn⟩

private theorem tick_bit (wait : ℕ) (gaps : ℕ → ℕ) (n : ℕ) :
    sourceBit wait gaps (clock wait gaps n - 1) = true := by
  apply (bit_iff wait gaps _).mpr
  exact ⟨n, by have := clock_lower wait gaps n; omega⟩

/-- The generated bits are the literal initial zeros/tick and every subsequent
    zeros/tick word, including an empty zero word. -/
theorem source_words (wait : ℕ) (gaps : ℕ → ℕ) :
    (∀ t < wait, sourceBit wait gaps t = false) ∧
    sourceBit wait gaps wait = true ∧
    (∀ n k, k ≤ gaps n → sourceBit wait gaps (clock wait gaps n + k) =
      decide (k = gaps n)) ∧
    (∀ n, sourceBit wait gaps (clock wait gaps n - 1) = true) := by
  have hs := clock_strict wait gaps
  refine ⟨?_, ?_, ?_, tick_bit wait gaps⟩
  · intro t ht
    apply Bool.eq_false_iff.mpr
    intro hb
    obtain ⟨n, hn⟩ := (bit_iff wait gaps t).mp hb
    have h := hs.monotone (Nat.zero_le n)
    simp only [clock] at h
    omega
  · simpa only [clock, Nat.add_sub_cancel] using tick_bit wait gaps 0
  · intro n k hk
    by_cases he : k = gaps n
    · subst k
      have hb := tick_bit wait gaps (n + 1)
      simpa only [clock, Nat.add_sub_cancel, decide_true] using hb
    · have hzero : sourceBit wait gaps (clock wait gaps n + k) = false := by
        apply Bool.eq_false_iff.mpr
        intro hb
        obtain ⟨j, hj⟩ := (bit_iff wait gaps _).mp hb
        by_cases hjn : j ≤ n
        · have h := hs.monotone hjn
          omega
        · have h := hs.monotone (show n + 1 ≤ j by omega)
          simp only [clock] at h
          omega
      simpa only [he, decide_false] using hzero

variable {S R : Type*}

/-- Initialization has already selected its actual state. Each live step reads
    precisely the next source bit and the next raw update coin. After an emitted
    label, the analytical continuation holds that same state fixed. -/
def run (labels : Set S) (update : S → Bool → R → S) (initial : S)
    (coins : ℕ → R) (wait : ℕ) (gaps : ℕ → ℕ) : ℕ → S
  | 0 => initial
  | t + 1 =>
    let s := run labels update initial coins wait gaps t
    if s ∈ labels then s else update s (sourceBit wait gaps t) (coins t)

/-- Analytical sampling of the very same per-bit run after each actual tick. -/
def epoch (labels : Set S) (update : S → Bool → R → S) (initial : S)
    (coins : ℕ → R) (wait : ℕ) (gaps : ℕ → ℕ) (n : ℕ) : S :=
  run labels update initial coins wait gaps (clock wait gaps n)

/-- Actual paid ticks: bit T and every later bit are excluded. -/
def paidTicks (wait : ℕ) (gaps : ℕ → ℕ) (T : ℕ) : ℕ :=
  ∑ t ∈ range T, if sourceBit wait gaps t then 1 else 0

private theorem run_absorbed (labels : Set S) (update : S → Bool → R → S)
    (initial : S) (coins : ℕ → R) (wait : ℕ) (gaps : ℕ → ℕ)
    (T : ℕ) (hT : run labels update initial coins wait gaps T ∈ labels) :
    ∀ t, T ≤ t → run labels update initial coins wait gaps t =
      run labels update initial coins wait gaps T := by
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction k with
  | zero => rfl
  | succ k ih =>
    change run labels update initial coins wait gaps ((T + k) + 1) = _
    rw [run, ih (by omega), if_pos hT]

private theorem paid_card (wait : ℕ) (gaps : ℕ → ℕ) (T : ℕ) :
    paidTicks wait gaps T =
      ((range T).filter fun t => sourceBit wait gaps t = true).card := by
  simp only [paidTicks, card_filter]

private theorem paid_le (wait : ℕ) (gaps : ℕ → ℕ) (T : ℕ) :
    paidTicks wait gaps T ≤ T := by
  rw [paid_card]
  exact (card_filter_le _ _).trans_eq (card_range T)

/-- Each live preterminal epoch identifies a distinct already read actual tick.
    This is derived from the generated source, rather than a count hypothesis. -/
private theorem live_ticks_paid (wait : ℕ) (gaps : ℕ → ℕ) (T N : ℕ)
    (hlive : ∀ n < N, clock wait gaps n < T) : N ≤ paidTicks wait gaps T := by
  rw [paid_card, ← card_range N]
  apply card_le_card_of_injOn (fun n => clock wait gaps n - 1)
  · intro n hn
    have h := hlive n (mem_range.mp hn)
    refine mem_filter.mpr ⟨mem_range.mpr ?_, (source_words wait gaps).2.2.2 n⟩
    change clock wait gaps n - 1 < T
    omega
  · intro i hi j hj hij
    have hi' := clock_lower wait gaps i
    have hj' := clock_lower wait gaps j
    change clock wait gaps i - 1 = clock wait gaps j - 1 at hij
    exact (clock_strict wait gaps).injective (by omega)

/-- Finite actual first stopping gives the first terminal analytical epoch with
    the same emitted state, N ≤ Q_T ≤ T, and exact endpoint information. The
    labels, updates, initial state and raw coin stream are arbitrary. No eventual
    stopping assumption is imposed on the auxiliary continuation. -/
theorem stopping_correspondence (labels : Set S) (update : S → Bool → R → S)
    (initial : S) (coins : ℕ → R) (wait : ℕ) (gaps : ℕ → ℕ) :
    (∀ T, firstHit labels (run labels update initial coins wait gaps) = some T →
      ∃ N, firstHit labels (epoch labels update initial coins wait gaps) = some N ∧
        epoch labels update initial coins wait gaps N =
          run labels update initial coins wait gaps T ∧
        T ≤ clock wait gaps N ∧
        (∀ n < N, clock wait gaps n < T) ∧
        N ≤ paidTicks wait gaps T ∧ paidTicks wait gaps T ≤ T ∧
        (N = 0 ↔ T ≤ wait + 1)) ∧
    (firstHit labels (run labels update initial coins wait gaps) = none ↔
      firstHit labels (epoch labels update initial coins wait gaps) = none) := by
  letI : MeasurableSpace S := ⊤
  let Z := run labels update initial coins wait gaps
  let Y := epoch labels update initial coins wait gaps
  have finite (T : ℕ) (hT : firstHit labels Z = some T) :
      ∃ N, firstHit labels Y = some N ∧ Y N = Z T ∧
        T ≤ clock wait gaps N ∧ (∀ n < N, clock wait gaps n < T) ∧
        N ≤ paidTicks wait gaps T ∧ paidTicks wait gaps T ≤ T ∧
        (N = 0 ↔ T ≤ wait + 1) := by
    obtain ⟨hterm, hpre⟩ := (first_hit_some labels Z T).mp hT
    have hex : ∃ n, T ≤ clock wait gaps n :=
      ⟨T, by have := clock_lower wait gaps T; omega⟩
    let N := Nat.find hex
    have hafter : T ≤ clock wait gaps N := Nat.find_spec hex
    have hbefore : ∀ n < N, clock wait gaps n < T := by
      intro n hn
      exact lt_of_not_ge (Nat.find_min hex hn)
    have hsame : Y N = Z T := run_absorbed labels update initial coins wait gaps T
      hterm _ hafter
    have hfirst : firstHit labels Y = some N := by
      apply (first_hit_some labels Y N).mpr
      refine ⟨hsame.symm ▸ hterm, ?_⟩
      intro n hn
      exact hpre _ (hbefore n hn)
    refine ⟨N, hfirst, hsame, hafter, hbefore,
      live_ticks_paid wait gaps T N hbefore, paid_le wait gaps T, ?_⟩
    constructor
    · intro hn
      simpa only [hn, clock] using hafter
    · intro ht
      by_contra hn
      have h := hbefore 0 (Nat.pos_of_ne_zero hn)
      simp only [clock] at h
      omega
  refine ⟨finite, ?_⟩
  constructor
  · intro hnone
    by_contra hepoch
    cases hy : firstHit labels Y with
    | none => exact hepoch hy
    | some n =>
      have hmem := ((first_hit_some labels Y n).mp hy).1
      have hex : ∃ t, Z t ∈ labels := ⟨clock wait gaps n, hmem⟩
      unfold firstHit at hnone
      split at hnone
      · cases hnone
      · rename_i hn
        exact hn hex
  · intro hnone
    by_contra hrun
    cases hz : firstHit labels Z with
    | none => exact hrun hz
    | some T =>
      obtain ⟨N, hN, _⟩ := finite T hz
      rw [hnone] at hN
      cases hN

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalStopping
