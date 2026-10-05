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

end D5.S3.Arith.FibonacciAtomic.PrimePowerPassiveGcdMemoSupportUpper
