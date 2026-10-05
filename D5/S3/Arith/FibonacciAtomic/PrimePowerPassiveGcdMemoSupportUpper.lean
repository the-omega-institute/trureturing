/- GID: D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdMemoSupportUpper
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdMemoSupportUpper
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Cached and general parent supports count all original prime-power lifts. -/

import D5.S3.Arith.FibonacciAtomic.PrimePowerPassiveGcdController
import D5.S3.ConceptDynamics.Experiment.PassiveQueryMemoization
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PrimePowerPassiveGcdMemoSupportUpper

open D5.S3.Arith.FibonacciAtomic.TimeSampling
open D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
open D5.S3.Arith.FibonacciAtomic.PrimePowerPassiveGcdController
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassiveQueryMemoization (memo)

/-- Numerical addresses actually queried by the original, unmemoized tree. -/
private def support (p e : ℕ) (T : Tree) (v : ℕ × ℕ) : Finset ℕ :=
  ((runPassiveProtocol (read p e) T v).map (fun a => a.1.val)).toFinset

/-- Move the current query into the finite set of already accounted addresses. -/
private theorem query_union (p e : ℕ) (q : PositiveTime) (next : ℕ → Tree)
    (v : ℕ × ℕ) (S : Finset ℕ) :
    support p e (.query q next) v ∪ S =
      support p e (next (read p e q v)) v ∪ insert q.val S := by
  simp [support, runPassiveProtocol]

/-- The child scan adds at most its remaining number of tests. The selected
omitted child is passed to an arbitrary-parent continuation, without being
silently counted as queried. -/
private theorem children_union_bound (p e threshold rank phase bound : ℕ)
    (next : ℕ → Tree)
    (hnext : ∀ t v S, (support p e (next t) v ∪ S).card ≤ S.card + bound) :
    ∀ n j v S,
      (support p e (children threshold rank phase next n j) v ∪ S).card ≤
        S.card + n + bound := by
  intro n
  induction n with
  | zero =>
    intro j v S
    simpa [children] using hnext (phase + j * rank) v S
  | succ n ih =>
    intro j v S
    rw [children, query_union]
    simp only
    have inserted := Finset.card_insert_le (phase + j * rank + 1) S
    split
    · have h := hnext (phase + j * rank) v (insert (phase + j * rank + 1) S)
      omega
    · have h := ih (j + 1) v (insert (phase + j * rank + 1) S)
      omega

/-- Simultaneous arbitrary-fuel counting against any prior finite support.
The first inequality assumes nothing about the surviving representative.
The second uses only that its address has already been accounted for. -/
private theorem continuation_union_bound (p e content : ℕ) (hp : 2 ≤ p) :
    ∀ fuel d phase v S,
      (support p e (continuation p content fuel d phase) v ∪ S).card ≤
        S.card + fuel * (p - 1) ∧
      (phase + 1 ∈ S →
        (support p e (continuation p content fuel d phase) v ∪ S).card ≤
          S.card + (fuel * (p - 1) - 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d phase v S
    simp [continuation, support, runPassiveProtocol]
  | succ fuel ih =>
    intro d phase v S
    have hp1 : 1 ≤ p - 1 := by omega
    have budget : (fuel + 1) * (p - 1) = fuel * (p - 1) + (p - 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    by_cases stagnant : zeroRank (p ^ (d + 1)) = zeroRank (p ^ d)
    · constructor
      · simp only [continuation, stagnant, ite_true]
        rw [query_union]
        simp only
        have inserted := Finset.card_insert_le (phase + 1) S
        split
        · have h := (ih (d + 1) phase v (insert (phase + 1) S)).1
          omega
        · simp only [support, runPassiveProtocol, List.map_nil, List.toFinset_nil,
            Finset.empty_union]
          omega
      · intro cached
        simp only [continuation, stagnant, ite_true]
        rw [query_union, Finset.insert_eq_of_mem cached]
        split
        · have h := (ih (d + 1) phase v S).1
          omega
        · simp [support, runPassiveProtocol]
    · constructor
      · simp only [continuation, stagnant, ite_false]
        have h := children_union_bound p e (p ^ (content + d + 1))
          (zeroRank (p ^ d)) phase (fuel * (p - 1))
          (continuation p content fuel (d + 1))
          (fun t v S => (ih (d + 1) t v S).1) (p - 1) 0 v S
        omega
      · intro cached
        simp only [continuation, stagnant, ite_false]
        have tests : p - 1 = (p - 2) + 1 := by omega
        conv_lhs => rw [tests]
        rw [children, query_union]
        simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add]
        rw [Finset.insert_eq_of_mem cached]
        split
        · have h := (ih (d + 1) phase v S).1
          omega
        · have h := children_union_bound p e (p ^ (content + d + 1))
            (zeroRank (p ^ d)) phase (fuel * (p - 1))
            (continuation p content fuel (d + 1))
            (fun t v S => (ih (d + 1) t v S).1) (p - 2) 1 v S
          omega

/-- All first-layer scan addresses are already in the initial interval.
A queried hit, including either content time, supplies a cached parent. -/
private theorem first_layer_union_bound (p e threshold r bound : ℕ)
    (next : ℕ → Tree)
    (hnext : ∀ phase, phase < r → ∀ v,
      (support p e (next phase) v ∪ Finset.Icc 1 r).card ≤ r + bound) :
    ∀ n phase, n + phase = r → ∀ v,
      (support p e (firstLayer threshold next n phase) v ∪ Finset.Icc 1 r).card ≤
        r + bound := by
  intro n
  induction n with
  | zero =>
    intro phase _ v
    simp [firstLayer, support, runPassiveProtocol]
  | succ n ih =>
    intro phase hphase v
    have cached : phase + 1 ∈ Finset.Icc 1 r :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [firstLayer, query_union, Finset.insert_eq_of_mem cached]
    split
    · exact hnext phase (by omega) v
    · exact ih (phase + 1) (by omega) v

/-- Content queries, the complete first scan, and every actual continuation
share one uniform support bound, including saturated and malformed labels. -/
private theorem protocol_support_bound (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    ∀ v : ℕ × ℕ, (support p e (protocol p e) v).card ≤
      if e = 1 then zeroRank p else zeroRank p + (e - 1) * (p - 1) - 1 := by
  let r := zeroRank p
  let S := Finset.Icc 1 r
  have hr : 3 ≤ r := by simpa [r] using (rank_facts p hp 1 le_rfl).1
  have hS : S.card = r := by simp [S]
  have one : 1 ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have two : 2 ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hp1 : 1 ≤ p - 1 := by have h := hp.two_le; omega
  have base : r ≤ if e = 1 then r else r + (e - 1) * (p - 1) - 1 := by
    by_cases h : e = 1
    · simp [h]
    · rw [if_neg h]
      have pos := Nat.mul_pos (show 0 < e - 1 by omega) (show 0 < p - 1 by omega)
      omega
  have budget (c : ℕ) (hc : c < e) :
      r + ((e - c - 1) * (p - 1) - 1) ≤
        if e = 1 then r else r + (e - 1) * (p - 1) - 1 := by
    by_cases h : e = 1
    · subst e
      have hc0 : c = 0 := by omega
      simp [hc0]
    · rw [if_neg h]
      have mul := Nat.mul_le_mul_right (p - 1) (show e - c - 1 ≤ e - 1 by omega)
      have pos := Nat.mul_pos (show 0 < e - 1 by omega) (show 0 < p - 1 by omega)
      omega
  have scan (c : ℕ) (hc : c < e) (v : ℕ × ℕ) :
      (support p e (firstLayer (p ^ (c + 1))
        (continuation p c (e - c - 1) 1) r 0) v ∪ S).card ≤
        r + ((e - c - 1) * (p - 1) - 1) := by
    apply first_layer_union_bound p e (p ^ (c + 1)) r
      ((e - c - 1) * (p - 1) - 1) (continuation p c (e - c - 1) 1)
    · intro phase hphase w
      have cached : phase + 1 ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have h := (continuation_union_bound p e c hp.two_le
        (e - c - 1) 1 phase w S).2 cached
      simpa only [hS] using h
    · omega
  intro v
  have contained : (support p e (protocol p e) v).card ≤
      (support p e (protocol p e) v ∪ S).card :=
    Finset.card_le_card Finset.subset_union_left
  apply contained.trans
  change (support p e (protocol p e) v ∪ S).card ≤
    if e = 1 then r else r + (e - 1) * (p - 1) - 1
  simp only [protocol]
  rw [query_union, Finset.insert_eq_of_mem one, query_union,
    Finset.insert_eq_of_mem two]
  split
  · simpa only [support, runPassiveProtocol, List.map_nil, List.toFinset_nil,
      Finset.empty_union, hS] using base
  · split
    · rename_i depth
      have hc := (Classical.choose_spec depth).1
      exact (scan (Classical.choose depth) hc v).trans (budget _ hc)
    · simpa only [support, runPassiveProtocol, List.map_nil, List.toFinset_nil,
        Finset.empty_union, hS] using base

/-- Empty-cache memoization of the exact original tree bounds all natural
source histories and retains the full positive numerical gcd future. -/
theorem result (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    (∀ v : ℕ × ℕ,
      (runPassiveProtocol (read p e) (memo (protocol p e) (fun _ => none)) v).length ≤
        if e = 1 then zeroRank p else zeroRank p + (e - 1) * (p - 1) - 1) ∧
    (∀ v w : ℕ × ℕ,
      runPassiveProtocol (read p e) (memo (protocol p e) (fun _ => none)) v =
        runPassiveProtocol (read p e) (memo (protocol p e) (fun _ => none)) w →
      ∀ k : ℕ, 0 < k → actualGcd (p ^ e) k v = actualGcd (p ^ e) k w) := by
  classical
  let : DecidableEq PositiveTime := Classical.decEq PositiveTime
  have memoLaw := D5.S3.ConceptDynamics.Experiment.PassiveQueryMemoization.result
    (protocol p e) (read p e)
  refine ⟨?_, ?_⟩
  · intro v
    let Q := ((runPassiveProtocol (read p e) (protocol p e) v).map Sigma.fst).toFinset
    have projected : support p e (protocol p e) v = Q.image (fun q => q.val) := by
      ext k
      simp only [support, Q, Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨a, ha, hak⟩
        exact ⟨a.1, ⟨a, ha, rfl⟩, hak⟩
      · rintro ⟨q, ⟨a, ha, haq⟩, hqk⟩
        subst q
        exact ⟨a, ha, hqk⟩
    have cardImage : (Q.image (fun q => q.val)).card = Q.card :=
      Finset.card_image_of_injective Q Subtype.val_injective
    have bound := protocol_support_bound p e hp he v
    rw [projected, cardImage] at bound
    rw [(memoLaw.1 v).2.2.2]
    simpa only [Q] using bound
  · intro v w same
    exact (protocol_spec p e hp he).2 v w ((memoLaw.2 v w).mp same)

/- Rank-dependent budgets and bounded attainment for the original tree. -/

/-- General-parent and cached-parent budgets follow the actual rank decisions. -/
private noncomputable def rank_budgets (p : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | n + 1, d =>
      let next := rank_budgets p n (d + 1)
      if zeroRank (p ^ (d + 1)) = zeroRank (p ^ d) then
        (next.1, next.1 + 1)
      else (p - 2 + next.2, p - 1 + next.2)

private theorem rank_budgets_order (p : ℕ) (hp : 2 ≤ p) (n d : ℕ) :
    (rank_budgets p n d).1 ≤ (rank_budgets p n d).2 := by
  cases n with
  | zero => simp [rank_budgets]
  | succ n =>
    simp only [rank_budgets]
    split <;> simp only <;> omega

private theorem rank_budgets_step (p : ℕ) (_hp : 2 ≤ p) :
    ∀ n d, (rank_budgets p n d).1 ≤ (rank_budgets p (n + 1) d).1 ∧
      (rank_budgets p n d).2 ≤ (rank_budgets p (n + 1) d).2 := by
  intro n
  induction n with
  | zero => intro d; simp [rank_budgets]
  | succ n ih =>
    intro d
    have h := ih (d + 1)
    by_cases stagnant : zeroRank (p ^ (d + 1)) = zeroRank (p ^ d)
    · rw [rank_budgets, rank_budgets]
      simp only [stagnant, ite_true]
      constructor <;> omega
    · rw [rank_budgets, rank_budgets]
      simp only [stagnant, ite_false]
      constructor <;> omega

private theorem rank_continuation_bound (p e content : ℕ) (hp : 2 ≤ p) :
    ∀ n d phase v S,
      (support p e (continuation p content n d phase) v ∪ S).card ≤
        S.card + (rank_budgets p n d).2 ∧
      (phase + 1 ∈ S →
        (support p e (continuation p content n d phase) v ∪ S).card ≤
          S.card + (rank_budgets p n d).1) := by
  intro n
  induction n with
  | zero => intro d phase v S; simp [continuation, support, runPassiveProtocol, rank_budgets]
  | succ n ih =>
    intro d phase v S
    have order := rank_budgets_order p hp n (d + 1)
    by_cases stagnant : zeroRank (p ^ (d + 1)) = zeroRank (p ^ d)
    · simp only [rank_budgets, stagnant, ite_true]
      constructor
      · simp only [continuation, stagnant, ite_true]
        rw [query_union]
        simp only
        have inserted := Finset.card_insert_le (phase + 1) S
        have cached : phase + 1 ∈ insert (phase + 1) S := Finset.mem_insert_self _ _
        split
        · have h := (ih (d + 1) phase v (insert (phase + 1) S)).2 cached
          omega
        · simp only [support, runPassiveProtocol, List.map_nil, List.toFinset_nil,
            Finset.empty_union]
          omega
      · intro cached
        simp only [continuation, stagnant, ite_true]
        rw [query_union, Finset.insert_eq_of_mem cached]
        split
        · exact (ih (d + 1) phase v S).2 cached
        · simp [support, runPassiveProtocol]
    · simp only [rank_budgets, stagnant, ite_false]
      constructor
      · simp only [continuation, stagnant, ite_false]
        have h := children_union_bound p e (p ^ (content + d + 1))
          (zeroRank (p ^ d)) phase (rank_budgets p n (d + 1)).2
          (continuation p content n (d + 1))
          (fun t v S => (ih (d + 1) t v S).1) (p - 1) 0 v S
        omega
      · intro cached
        simp only [continuation, stagnant, ite_false]
        have tests : p - 1 = (p - 2) + 1 := by omega
        conv_lhs => rw [tests]
        rw [children, query_union]
        simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add]
        rw [Finset.insert_eq_of_mem cached]
        split
        · have h := (ih (d + 1) phase v S).2 cached
          omega
        · have h := children_union_bound p e (p ^ (content + d + 1))
            (zeroRank (p ^ d)) phase (rank_budgets p n (d + 1)).2
            (continuation p content n (d + 1))
            (fun t v S => (ih (d + 1) t v S).1) (p - 2) 1 v S
          omega

private theorem rank_protocol_bound (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    ∀ v, (support p e (protocol p e) v).card ≤
      zeroRank p + (rank_budgets p (e - 1) 1).1 := by
  let r := zeroRank p
  let S := Finset.Icc 1 r
  have hr : 3 ≤ r := by simpa [r] using (rank_facts p hp 1 le_rfl).1
  have hS : S.card = r := by simp [S]
  have one : 1 ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have two : 2 ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have mono (d : ℕ) : Monotone (fun n => (rank_budgets p n d).1) :=
    monotone_nat_of_le_succ (fun n => (rank_budgets_step p hp.two_le n d).1)
  have scan (c : ℕ) (hc : c < e) (v : ℕ × ℕ) :
      (support p e (firstLayer (p ^ (c + 1))
        (continuation p c (e - c - 1) 1) r 0) v ∪ S).card ≤
        r + (rank_budgets p (e - 1) 1).1 := by
    apply first_layer_union_bound p e (p ^ (c + 1)) r
      (rank_budgets p (e - 1) 1).1 (continuation p c (e - c - 1) 1)
    · intro phase hphase w
      have cached : phase + 1 ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have h := (rank_continuation_bound p e c hp.two_le
        (e - c - 1) 1 phase w S).2 cached
      have m := mono 1 (show e - c - 1 ≤ e - 1 by omega)
      change (support p e (continuation p c (e - c - 1) 1 phase) w ∪ S).card ≤ _
      change (rank_budgets p (e - c - 1) 1).1 ≤ (rank_budgets p (e - 1) 1).1 at m
      rw [hS] at h
      omega
    · omega
  intro v
  have contained : (support p e (protocol p e) v).card ≤
      (support p e (protocol p e) v ∪ S).card :=
    Finset.card_le_card Finset.subset_union_left
  apply contained.trans
  change (support p e (protocol p e) v ∪ S).card ≤ r + (rank_budgets p (e - 1) 1).1
  simp only [protocol]
  rw [query_union, Finset.insert_eq_of_mem one, query_union,
    Finset.insert_eq_of_mem two]
  split
  · simp [support, runPassiveProtocol, hS]
  · split
    · rename_i depth
      exact scan (Classical.choose depth) (Classical.choose_spec depth).1 v
    · simp [support, runPassiveProtocol, hS]

/-- Existing public observation inversion realizes the Fibonacci source within
one natural residue box. This is a consumed supplier bridge, not new content. -/
private theorem fibonacci_source (p e : ℕ) (hp : p.Prime) (_he : 1 ≤ e) :
    ∃ v : ℕ × ℕ, v.1 < p ^ e ∧ v.2 < p ^ e ∧
      ∀ k : ℕ, ∀ hk : 0 < k, read p e ⟨k, hk⟩ v = Nat.gcd (Nat.fib k) (p ^ e) := by
  classical
  let H := p ^ e
  have hH : 0 < H := pow_pos hp.pos e
  obtain ⟨_, _, _, _, _, _, _, _, _, bounded, _, _, _, _, _, _, inverse, _⟩ :=
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.result.2 H hH (0, 0)
  let z : ZMod H × ZMod H := (0, 1)
  let w : ZMod H × ZMod H := (5 * z.1 - 3 * z.2, -3 * z.1 + 2 * z.2)
  obtain ⟨v, hv1, hv2, hv⟩ := bounded w
  have obs : D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.observe
      (D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.residue H v) = z := by
    rw [hv]
    exact inverse z
  refine ⟨v, hv1, hv2, ?_⟩
  intro k hk
  have castQty :
      (D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.quantity (A := ℕ)
        (D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.step^[k] v) : ZMod H) =
        (Nat.fib k : ZMod H) := by
    have h := congrArg (fun u : ZMod H × ZMod H =>
      (Nat.fib (k - 1) : ZMod H) * u.1 + Nat.fib k * u.2) obs
    rw [← Int.cast_natCast, actual_signed_quantity k v hk]
    simpa [signedValue, D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.observe,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.quantity,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.step,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.residue, z] using h
  exact (ZMod.natCast_eq_natCast_iff _ _ H).mp castQty |>.gcd_eq

private theorem support_query (p e : ℕ) (q : PositiveTime) (next : ℕ → Tree)
    (v : ℕ × ℕ) :
    support p e (.query q next) v = insert q.val (support p e (next (read p e q v)) v) := by
  simpa using query_union p e q next v ∅

private theorem interval_head (a b : ℕ) (h : a ≤ b) :
    Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

private theorem fib_threshold (p e : ℕ) (hp : p.Prime) (v : ℕ × ℕ)
    (fib : ∀ k (hk : 0 < k), read p e ⟨k, hk⟩ v = Nat.gcd (Nat.fib k) (p ^ e))
    (d : ℕ) (hd : 1 ≤ d) (hde : d ≤ e) (k : ℕ) (hk : 0 < k) :
    p ^ d ∣ read p e ⟨k, hk⟩ v ↔ zeroRank (p ^ d) ∣ k := by
  rw [fib k hk, Nat.dvd_gcd_iff]
  simpa only [and_iff_left (pow_dvd_pow p hde)] using (rank_facts p hp d hd).2.2 k

/-- The Fibonacci witness exhausts every tested child of a growing rank. -/
private theorem fib_children_support (p e d : ℕ) (hp : p.Prime) (hd : 1 ≤ d)
    (hde : d + 1 ≤ e)
    (growth : zeroRank (p ^ (d + 1)) = p * zeroRank (p ^ d))
    (v : ℕ × ℕ)
    (fib : ∀ k (hk : 0 < k), read p e ⟨k, hk⟩ v = Nat.gcd (Nat.fib k) (p ^ e))
    (next : ℕ → Tree) :
    support p e (children (p ^ (d + 1)) (zeroRank (p ^ d))
      (zeroRank (p ^ d) - 1) next (p - 1) 0) v =
      (Finset.Icc 1 (p - 1)).image (fun q => q * zeroRank (p ^ d)) ∪
        support p e (next (zeroRank (p ^ (d + 1)) - 1)) v := by
  let r := zeroRank (p ^ d)
  have hr : 3 ≤ r := (rank_facts p hp d hd).1
  have mul := Nat.mul_le_mul_right r hp.two_le
  have addr (j : ℕ) : r - 1 + j * r + 1 = (j + 1) * r := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have endPhase : r - 1 + (p - 1) * r = zeroRank (p ^ (d + 1)) - 1 := by
    rw [growth]
    change r - 1 + (p - 1) * r = p * r - 1
    rw [Nat.sub_mul, Nat.one_mul]
    omega
  have misses (j : ℕ) (hj : j < p - 1) :
      ¬ p ^ (d + 1) ∣ read p e ⟨r - 1 + j * r + 1, by omega⟩ v := by
    rw [fib_threshold p e hp v fib (d + 1) (by omega) hde _ (by omega), growth]
    change ¬ p * r ∣ r - 1 + j * r + 1
    rw [addr]
    intro divides
    have qdiv : p ∣ j + 1 := (Nat.mul_dvd_mul_iff_left (show 0 < r by omega)).mp
      (by simpa only [Nat.mul_comm] using divides)
    have low := Nat.le_of_dvd (show 0 < j + 1 by omega) qdiv
    omega
  have scan : ∀ n j, n + j = p - 1 →
      support p e (children (p ^ (d + 1)) r (r - 1) next n j) v =
        (Finset.Icc (j + 1) (p - 1)).image (fun q => q * r) ∪
          support p e (next (zeroRank (p ^ (d + 1)) - 1)) v := by
    intro n
    induction n with
    | zero =>
      intro j hj
      have last : j = p - 1 := by omega
      subst j
      rw [children, endPhase]
      simp
    | succ n ih =>
      intro j hj
      have miss := misses j (by omega)
      rw [children, support_query]
      simp only
      rw [if_neg miss, ih (j + 1) (by omega)]
      rw [interval_head (j + 1) (p - 1) (by omega), Finset.image_insert]
      simp only [Finset.insert_union, addr]
  simpa only [r, Nat.zero_add] using scan (p - 1) 0 (by omega)

private theorem band_union_count (p r : ℕ) (hp : 2 ≤ p) (hr : 0 < r)
    (S : Finset ℕ) :
    (r ∈ S → (∀ k ∈ S, k ≤ r) →
      ((Finset.Icc 1 (p - 1)).image (fun q => q * r) ∪ S).card = S.card + (p - 2)) ∧
    ((∀ k ∈ S, k < r) →
      ((Finset.Icc 1 (p - 1)).image (fun q => q * r) ∪ S).card = S.card + (p - 1)) := by
  let A := (Finset.Icc 1 (p - 1)).image (fun q => q * r)
  have inj : Function.Injective (fun q : ℕ => q * r) := fun _ _ h => Nat.mul_right_cancel hr h
  have card : A.card = p - 1 := by
    rw [Finset.card_image_of_injective _ inj]
    simp
  constructor
  · intro cached bounded
    have inter : A ∩ S = {r} := by
      ext k
      constructor
      · intro hk
        obtain ⟨ha, hs⟩ := Finset.mem_inter.mp hk
        obtain ⟨q, hq, hqk⟩ := Finset.mem_image.mp ha
        have hq1 := (Finset.mem_Icc.mp hq).1
        have hkr := bounded k hs
        have qone : q = 1 := by
          by_contra h
          have hq2 : 2 ≤ q := by omega
          have multiple := Nat.mul_le_mul_right r hq2
          simp only [Nat.two_mul] at multiple
          omega
        apply Finset.mem_singleton.mpr
        simpa only [qone, Nat.one_mul] using hqk.symm
      · intro hk
        have equal := Finset.mem_singleton.mp hk
        subst k
        apply Finset.mem_inter.mpr
        exact ⟨Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          by simp⟩, cached⟩
    have equation := Finset.card_union_add_card_inter A S
    rw [inter, Finset.card_singleton, card] at equation
    change (A ∪ S).card = _
    omega
  · intro bounded
    have inter : A ∩ S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      obtain ⟨ha, hs⟩ := Finset.mem_inter.mp hk
      obtain ⟨q, hq, hqk⟩ := Finset.mem_image.mp ha
      have hq1 := (Finset.mem_Icc.mp hq).1
      have multiple := Nat.mul_le_mul_right r hq1
      simp only [Nat.one_mul] at multiple
      have hkr := bounded k hs
      omega
    have equation := Finset.card_union_add_card_inter A S
    rw [inter, Finset.card_empty, card] at equation
    change (A ∪ S).card = _
    omega

/-- Exact support increments of the fixed Fibonacci source. Old supports are
bounded by the selected rank; exhaustion leaves its next representative fresh. -/
private theorem fib_continuation_count (p e : ℕ) (hp : p.Prime) (v : ℕ × ℕ)
    (fib : ∀ k (hk : 0 < k), read p e ⟨k, hk⟩ v = Nat.gcd (Nat.fib k) (p ^ e)) :
    ∀ n d, 1 ≤ d → d + n ≤ e → ∀ S : Finset ℕ,
      ((zeroRank (p ^ d) ∈ S) → (∀ k ∈ S, k ≤ zeroRank (p ^ d)) →
        (support p e (continuation p 0 n d (zeroRank (p ^ d) - 1)) v ∪ S).card =
          S.card + (rank_budgets p n d).1) ∧
      ((∀ k ∈ S, k < zeroRank (p ^ d)) →
        (support p e (continuation p 0 n d (zeroRank (p ^ d) - 1)) v ∪ S).card =
          S.card + (rank_budgets p n d).2) := by
  intro n
  induction n with
  | zero => intro d hd hde S; simp [continuation, support, runPassiveProtocol, rank_budgets]
  | succ n ih =>
    intro d hd hde S
    let r := zeroRank (p ^ d)
    have hr : 3 ≤ r := (rank_facts p hp d hd).1
    have next := ih (d + 1) (by omega) (by omega)
    have timeEq : zeroRank (p ^ d) - 1 + 1 = zeroRank (p ^ d) := by
      change r - 1 + 1 = r
      omega
    by_cases stagnant : zeroRank (p ^ (d + 1)) = zeroRank (p ^ d)
    · have hit : p ^ (d + 1) ∣ read p e ⟨r - 1 + 1, by omega⟩ v := by
        rw [fib_threshold p e hp v fib (d + 1) (by omega) (by omega) _ (by omega), stagnant]
        change r ∣ r - 1 + 1
        simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using dvd_refl r
      simp only [rank_budgets, stagnant, ite_true]
      constructor
      · intro cached bounded
        simp only [continuation, stagnant, ite_true, Nat.zero_add]
        rw [query_union]
        rw [if_pos hit]
        simp only [timeEq]
        rw [Finset.insert_eq_of_mem cached]
        have h := (next S).1 (by simpa only [stagnant, r] using cached)
          (by simpa only [stagnant, r] using bounded)
        simpa only [stagnant] using h
      · intro bounded
        simp only [continuation, stagnant, ite_true, Nat.zero_add]
        rw [query_union]
        rw [if_pos hit]
        simp only [timeEq]
        have fresh : r ∉ S := by intro h; have := bounded r h; omega
        have b : ∀ k ∈ insert r S, k ≤ r := by
          intro k hk
          rcases Finset.mem_insert.mp hk with h | h
          · omega
          · have := bounded k h; omega
        have h := (next (insert r S)).1
          (by simpa only [stagnant, r] using Finset.mem_insert_self r S)
          (by simpa only [stagnant, r] using b)
        rw [Finset.card_insert_of_notMem fresh] at h
        simpa only [stagnant, r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · have dichotomy :=
        (D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon
          p (d + 1) hp (by omega)).2.1
      simp only [show d + 1 - 1 = d by omega] at dichotomy
      have growth : zeroRank (p ^ (d + 1)) = p * r :=
        dichotomy.resolve_left stagnant
      let A := (Finset.Icc 1 (p - 1)).image (fun q => q * r)
      let S' := A ∪ S
      have supportEq := fib_children_support p e d hp hd (by omega) growth v fib
        (continuation p 0 n (d + 1))
      have mul := Nat.mul_le_mul_right r hp.two_le
      have parentBound : r < p * r := by simp only [Nat.two_mul] at mul; omega
      have nextFresh (bounded : ∀ k ∈ S, k ≤ r) :
          ∀ k ∈ S', k < zeroRank (p ^ (d + 1)) := by
        intro k hk
        rcases Finset.mem_union.mp hk with ha | hs
        · obtain ⟨q, hq, hqk⟩ := Finset.mem_image.mp ha
          have hqtop : q ≤ p - 1 := (Finset.mem_Icc.mp hq).2
          have hqp : q < p := by have := hp.two_le; omega
          have hmul := Nat.mul_lt_mul_of_pos_right hqp (show 0 < r by omega)
          rw [growth]
          omega
        · have hkr := bounded k hs
          rw [growth]
          omega
      have unionEq :
          (A ∪ support p e (continuation p 0 n (d + 1)
            (zeroRank (p ^ (d + 1)) - 1)) v) ∪ S =
          support p e (continuation p 0 n (d + 1)
            (zeroRank (p ^ (d + 1)) - 1)) v ∪ S' := by
        simp only [S', Finset.union_comm, Finset.union_left_comm]
      simp only [rank_budgets, stagnant, ite_false]
      constructor
      · intro cached bounded
        simp only [continuation, stagnant, ite_false, Nat.zero_add]
        rw [supportEq, unionEq]
        have h := (next S').2 (nextFresh bounded)
        have card := (band_union_count p r hp.two_le (by omega) S).1 cached bounded
        change S'.card = S.card + (p - 2) at card
        rw [card] at h
        simpa only [Nat.add_assoc] using h
      · intro bounded
        simp only [continuation, stagnant, ite_false, Nat.zero_add]
        rw [supportEq, unionEq]
        have weak : ∀ k ∈ S, k ≤ r := by intro k hk; exact Nat.le_of_lt (bounded k hk)
        have h := (next S').2 (nextFresh weak)
        have card := (band_union_count p r hp.two_le (by omega) S).2 bounded
        change S'.card = S.card + (p - 1) at card
        rw [card] at h
        simpa only [Nat.add_assoc] using h


private theorem fib_first_layer_support (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (v : ℕ × ℕ)
    (fib : ∀ k (hk : 0 < k), read p e ⟨k, hk⟩ v = Nat.gcd (Nat.fib k) (p ^ e))
    (next : ℕ → Tree) :
    support p e (firstLayer p next (zeroRank p) 0) v =
      Finset.Icc 1 (zeroRank p) ∪ support p e (next (zeroRank p - 1)) v := by
  let r := zeroRank p
  have hr : 3 ≤ r := by simpa only [pow_one] using (rank_facts p hp 1 le_rfl).1
  have test (k : ℕ) (hk : 0 < k) :
      p ∣ read p e ⟨k, hk⟩ v ↔ r ∣ k := by
    simpa only [pow_one] using fib_threshold p e hp v fib 1 le_rfl he k hk
  have scan : ∀ n phase, n + 1 + phase = r →
      support p e (firstLayer p next (n + 1) phase) v =
        Finset.Icc (phase + 1) r ∪ support p e (next (r - 1)) v := by
    intro n
    induction n with
    | zero =>
      intro phase hphase
      have time : phase + 1 = r := by omega
      have phaseEq : phase = r - 1 := by omega
      have hit : p ∣ read p e ⟨phase + 1, by omega⟩ v := (test _ (by omega)).mpr (by rw [time])
      rw [firstLayer, support_query]
      rw [if_pos hit]
      simp only [phaseEq, Nat.sub_add_cancel (show 1 ≤ r by omega),
        Finset.Icc_self, Finset.singleton_union]
    | succ n ih =>
      intro phase hphase
      have miss : ¬ p ∣ read p e ⟨phase + 1, by omega⟩ v := by
        rw [test]
        intro divides
        have low := Nat.le_of_dvd (show 0 < phase + 1 by omega) divides
        omega
      rw [firstLayer, support_query]
      simp only [if_neg miss]
      rw [ih (phase + 1) (by omega), interval_head (phase + 1) r (by omega)]
      simp only [Finset.insert_union]
  simpa only [Nat.add_zero, Nat.zero_add, show r - 1 + 1 = r by omega] using
    scan (r - 1) 0 (by omega)

private theorem fib_protocol_support (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (v : ℕ × ℕ)
    (fib : ∀ k (hk : 0 < k), read p e ⟨k, hk⟩ v = Nat.gcd (Nat.fib k) (p ^ e)) :
    support p e (protocol p e) v = Finset.Icc 1 (zeroRank p) ∪
      support p e (continuation p 0 (e - 1) 1 (zeroRank p - 1)) v := by
  have hr : 3 ≤ zeroRank p := by simpa only [pow_one] using (rank_facts p hp 1 le_rfl).1
  have a : read p e ⟨1, by omega⟩ v = 1 := by rw [fib]; norm_num
  have b : read p e ⟨2, by omega⟩ v = 1 := by rw [fib]; norm_num
  have power : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
  have unsaturated : Nat.gcd 1 1 ≠ p ^ e := by simp only [Nat.gcd_self]; omega
  have depth : ∃ c, c < e ∧ Nat.gcd 1 1 = p ^ c := ⟨0, by omega, by simp⟩
  have chooseZero : Classical.choose depth = 0 := by
    apply Nat.pow_right_injective hp.two_le
    simpa only [Nat.gcd_self, pow_zero] using (Classical.choose_spec depth).2.symm
  simp only [protocol]
  rw [support_query, a, support_query, b]
  simp only [if_neg unsaturated, dif_pos depth, chooseZero, Nat.zero_add, Nat.sub_zero, pow_one,
    fib_first_layer_support p e hp he v fib]
  have one : 1 ∈ Finset.Icc 1 (zeroRank p) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have two : 2 ∈ Finset.Icc 1 (zeroRank p) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [Finset.insert_eq_of_mem (Finset.mem_union_left _ two),
    Finset.insert_eq_of_mem (Finset.mem_union_left _ one)]

/-- Number of strictly growing lifts among depths d through d+n-1. -/
noncomputable def growthCount (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, d =>
      (if zeroRank (p ^ (d + 1)) = zeroRank (p ^ d) then 0 else 1) +
        growthCount p n (d + 1)

private noncomputable def lastGrowth (p n d : ℕ) : ℕ :=
  if n = 0 then 0 else
    if zeroRank (p ^ (d + n)) = zeroRank (p ^ (d + n - 1)) then 0 else 1

private theorem rank_budget_gap (p n d : ℕ) (hp : 2 ≤ p) :
    (rank_budgets p (n + 1) d).2 = (rank_budgets p (n + 1) d).1 + 1 := by
  rw [rank_budgets]
  split <;> simp only <;> omega

private theorem rank_budget_closed (p : ℕ) (hp : 2 ≤ p) :
    ∀ n d, (rank_budgets p n d).1 + lastGrowth p n d = growthCount p n d * (p - 1) := by
  intro n
  induction n with
  | zero => intro d; simp [rank_budgets, lastGrowth, growthCount]
  | succ n ih =>
    intro d
    cases n with
    | zero =>
      by_cases stagnant : zeroRank (p ^ (d + 1)) = zeroRank (p ^ d)
      · simp [rank_budgets, growthCount, lastGrowth, stagnant]
      · simp [rank_budgets, growthCount, lastGrowth, stagnant]
        omega
    | succ n =>
      have h := ih (d + 1)
      have gap := rank_budget_gap p n (d + 1) hp
      have last : lastGrowth p (n + 1 + 1) d = lastGrowth p (n + 1) (d + 1) := by
        simp only [lastGrowth, Nat.add_comm, Nat.add_left_comm,
          show n + 1 + 1 ≠ 0 by omega,
          show n + 1 ≠ 0 by omega, if_false]
      rw [rank_budgets, growthCount, last]
      split <;> simp only [zero_add, one_mul, Nat.add_mul] <;> omega

private theorem memo_length_support (p e : ℕ) (T : Tree) (v : ℕ × ℕ) :
    (runPassiveProtocol (read p e) (memo T (fun _ => none)) v).length =
      (support p e T v).card := by
  classical
  let : DecidableEq PositiveTime := Classical.decEq PositiveTime
  have law := D5.S3.ConceptDynamics.Experiment.PassiveQueryMemoization.result T (read p e)
  rw [(law.1 v).2.2.2]
  let Q := ((runPassiveProtocol (read p e) T v).map Sigma.fst).toFinset
  have projected : support p e T v = Q.image (fun q => q.val) := by
    ext k
    simp only [support, Q, Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨a, ha, hak⟩
      exact ⟨a.1, ⟨a, ha, rfl⟩, hak⟩
    · rintro ⟨q, ⟨a, ha, haq⟩, hqk⟩
      subst q
      exact ⟨a, ha, hqk⟩
  rw [projected, Finset.card_image_of_injective Q Subtype.val_injective]

/-- Exact worst completed length of the original empty-cache prime-power tree.
The growth count ranges over depths 1 through e-1; the final growing lift
subtracts one because its omitted representative is never queried. -/
theorem rank_pattern_exact (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    let B := zeroRank p + growthCount p (e - 1) 1 * (p - 1) -
      (if e = 1 then 0 else
        if zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) then 0 else 1)
    (∀ v : ℕ × ℕ,
      (runPassiveProtocol (read p e) (memo (protocol p e) (fun _ => none)) v).length ≤ B) ∧
    (∃ v : ℕ × ℕ, v.1 < p ^ e ∧ v.2 < p ^ e ∧
      (runPassiveProtocol (read p e) (memo (protocol p e) (fun _ => none)) v).length = B) := by
  classical
  dsimp only
  have final : lastGrowth p (e - 1) 1 =
      (if e = 1 then 0 else
        if zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) then 0 else 1) := by
    by_cases h : e = 1
    · subst e; simp [lastGrowth]
    · simp only [lastGrowth, show e - 1 ≠ 0 by omega, if_false, if_neg h,
        show 1 + (e - 1) = e by omega]
  have closed := rank_budget_closed p hp.two_le (e - 1) 1
  rw [final] at closed
  have budget : zeroRank p + (rank_budgets p (e - 1) 1).1 =
      zeroRank p + growthCount p (e - 1) 1 * (p - 1) -
        (if e = 1 then 0 else
          if zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) then 0 else 1) := by omega
  constructor
  · intro v
    rw [memo_length_support, ← budget]
    exact rank_protocol_bound p e hp he v
  · obtain ⟨v, hv1, hv2, fib⟩ := fibonacci_source p e hp he
    refine ⟨v, hv1, hv2, ?_⟩
    rw [memo_length_support, ← budget, fib_protocol_support p e hp he v fib,
      Finset.union_comm]
    have h := (fib_continuation_count p e hp v fib (e - 1) 1 le_rfl (by omega)
      (Finset.Icc 1 (zeroRank p))).1
    simp only [pow_one] at h
    have hr : 3 ≤ zeroRank p := by simpa only [pow_one] using (rank_facts p hp 1 le_rfl).1
    have h' := h (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      (fun k hk => (Finset.mem_Icc.mp hk).2)
    simpa using h'

end D5.S3.Arith.FibonacciAtomic.PrimePowerPassiveGcdMemoSupportUpper
