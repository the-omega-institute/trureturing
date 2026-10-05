/- GID: D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PositiveGraftShortWords
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Positive Fibonacci coefficients compile bounded chronological graft words. -/

import D5.S0.Conventions.WDigits
import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PositiveGraftShortWords

open D5.S0.Conventions
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
open scoped BigOperators

/-- A representative avoiding the unavailable unit graft weight. -/
def offset (H c : ℕ) : ℕ := if c = 0 then 0 else if c = 1 then H + 1 else c

/-- The least positive step count whose Fibonacci cutoff reaches the modulus. -/
def horizon (H : ℕ) : ℕ := Nat.find (show ∃ k : ℕ, 1 ≤ k ∧ H ≤ Nat.fib (k + 4) from
  ⟨H + 1, by omega, by have hf := Nat.le_fib_add_one (H + 1 + 4); omega⟩)

/-- One reserved graft plus the ceiling of half the available positions. -/
def graftBound (K : ℕ) : ℕ := 1 + (K + 2) / 2

/-- Remove the auxiliary unit weight from an occupied Fibonacci support. -/
def graftCoefficients (s : Finset ℕ) : ℕ → ℕ
  | 0 => (if 3 ∈ s then 1 else 0) + 1 - (if 2 ∈ s then 1 else 0)
  | 1 => (if 4 ∈ s then 1 else 0) + (if 2 ∈ s then 1 else 0)
  | j + 2 => if j + 5 ∈ s then 1 else 0

/-- Descending graft blocks, separated by single forward steps. -/
def blockWord (d : ℕ → ℕ) : ℕ → List Bool
  | 0 => List.replicate (d 0) true
  | k + 1 => List.replicate (d (k + 1)) true ++ false :: blockWord d k

private theorem support_data (u K : ℕ) (hu : u < Nat.fib (K + 4)) :
    let s := (wdigits u).toFinset
    (∀ i ∈ s, 2 ≤ i ∧ i ≤ K + 3) ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → i + 2 ≤ j ∨ j + 2 ≤ i) ∧
    (∑ i ∈ s, Nat.fib i) = u := by
  classical
  let : IsTrans ℕ (fun a b => b + 2 ≤ a) := ⟨by intros; omega⟩
  have hc := List.isChain_iff_pairwise.mp (wdigits_isCanonical u)
  have hp := List.pairwise_append.mp hc
  have hn : (wdigits u).Nodup := hp.1.imp (by intros; omega)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have him := List.mem_toFinset.mp hi
    have hlo := hp.2.2 i him 0 (by simp)
    have hval : Nat.fib i ≤ u := by
      rw [← decode_wdigits u]
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) _
        (List.mem_map.mpr ⟨i, him, rfl⟩)
    have hib : i < K + 4 := by
      by_contra h
      have hf := Nat.fib_mono (Nat.le_of_not_gt h)
      omega
    exact ⟨hlo, by omega⟩
  · intro i hi j hj hne
    let : Std.Symm (fun a b : ℕ => a + 2 ≤ b ∨ b + 2 ≤ a) :=
      ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
    have hsym : (wdigits u).Pairwise (fun a b => a + 2 ≤ b ∨ b + 2 ≤ a) :=
      hp.1.imp (fun h => Or.inr h)
    exact hsym.forall (List.mem_toFinset.mp hi) (List.mem_toFinset.mp hj) hne
  · rw [List.sum_toFinset Nat.fib hn, decode_wdigits]

private theorem spaced_card (K : ℕ) (s : Finset ℕ)
    (hb : ∀ i ∈ s, 3 ≤ i ∧ i ≤ K + 3)
    (hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → i + 2 ≤ j ∨ j + 2 ≤ i) :
    s.card ≤ (K + 2) / 2 := by
  classical
  have hm : Set.MapsTo (fun i : ℕ => (i - 3) / 2) s (Finset.range ((K + 2) / 2)) := by
    intro i hi
    have := hb i hi
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  have hin : Set.InjOn (fun i : ℕ => (i - 3) / 2) s := by
    intro i hi j hj heq
    have hi' := hb i hi
    have hj' := hb j hj
    change (i - 3) / 2 = (j - 3) / 2 at heq
    by_contra hne
    have := hs i hi j hj hne
    omega
  simpa using Finset.card_le_card_of_injOn _ hm hin

private theorem shifted_support_sum (K : ℕ) (s : Finset ℕ) (f : ℕ → ℕ)
    (hb : ∀ i ∈ s, i ≤ K + 3) :
    (∑ j ∈ Finset.range (K + 1), if j + 3 ∈ s then f (j + 3) else 0) =
      ∑ i ∈ s.filter (3 ≤ ·), f i := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => j + 3) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨hj.2, by omega⟩
  · intro i hi j hj hij
    omega
  · intro i hi
    simp only [Finset.mem_filter] at hi
    refine ⟨i - 3, ?_, by omega⟩
    have := hb i hi.1
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simpa [Nat.sub_add_cancel hi.2] using hi.1⟩
  · intro j hj
    rfl

private theorem coefficient_sums (K : ℕ) (hK : 1 ≤ K) (s : Finset ℕ)
    (hb : ∀ i ∈ s, 2 ≤ i ∧ i ≤ K + 3) :
    (∑ j ∈ Finset.range (K + 1), graftCoefficients s j * Nat.fib (j + 3)) =
        2 + ∑ i ∈ s, Nat.fib i ∧
    (∑ j ∈ Finset.range (K + 1), graftCoefficients s j) =
        1 + (s.filter (3 ≤ ·)).card := by
  classical
  let e := fun i : ℕ => if i ∈ s then 1 else 0
  have split_sum (f : ℕ → ℕ) :
      (∑ j ∈ Finset.range (K + 1), f j) =
        f 0 + f 1 + ∑ j ∈ Finset.range (K - 1), f (j + 2) := by
    rw [show K + 1 = (K - 1) + 1 + 1 by omega,
      Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.add_assoc]
    ac_rfl
  have hshift := shifted_support_sum K s Nat.fib (fun i hi => (hb i hi).2)
  have hcount := shifted_support_sum K s (fun _ => 1) (fun i hi => (hb i hi).2)
  have hcut : (∑ i ∈ s, Nat.fib i) = e 2 + ∑ i ∈ s.filter (3 ≤ ·), Nat.fib i := by
    calc
      (∑ i ∈ s, Nat.fib i) =
          ∑ i ∈ s, ((if i = 2 then 1 else 0) + (if 3 ≤ i then Nat.fib i else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have := (hb i hi).1
        by_cases he : i = 2
        · subst i; norm_num
        · simp only [if_neg he, if_pos (show 3 ≤ i by omega), zero_add]
      _ = e 2 + ∑ i ∈ s.filter (3 ≤ ·), Nat.fib i := by
        rw [Finset.sum_add_distrib]
        simp [e, Finset.sum_filter]
  have hdweight :
      (∑ j ∈ Finset.range (K + 1), graftCoefficients s j * Nat.fib (j + 3)) =
        2 + e 2 + ∑ j ∈ Finset.range (K + 1), e (j + 3) * Nat.fib (j + 3) := by
    rw [split_sum, split_sum]
    simp only [graftCoefficients, Nat.add_assoc]
    norm_num [Nat.fib_add_two]
    dsimp [e]
    split_ifs <;> norm_num <;> omega
  have hdcount :
      (∑ j ∈ Finset.range (K + 1), graftCoefficients s j) =
        1 + ∑ j ∈ Finset.range (K + 1), e (j + 3) := by
    rw [split_sum, split_sum]
    simp only [graftCoefficients, Nat.add_assoc]
    dsimp [e]
    split_ifs <;> omega
  constructor
  · rw [hdweight, hcut]
    have hw : (∑ j ∈ Finset.range (K + 1), e (j + 3) * Nat.fib (j + 3)) =
        ∑ i ∈ s.filter (3 ≤ ·), Nat.fib i := by
      simpa [e] using hshift
    rw [hw]
    omega
  · rw [hdcount]
    have hn : (∑ j ∈ Finset.range (K + 1), e (j + 3)) = (s.filter (3 ≤ ·)).card := by
      simpa [e] using hcount
    rw [hn]

private theorem run_grafts (n : ℕ) (v : ℕ × ℕ) :
    run (1, 0) (List.replicate n true) v = v + n • (1, 0) := by
  rw [show List.replicate n true = (List.replicate n ()).map (fun _ => true) by simp]
  unfold run
  rw [List.foldl_map]
  change (List.replicate n ()).foldl (fun u _ => u + (1, 0)) v = _
  apply Prod.ext
  · rw [← List.foldl_hom Prod.fst (g₂ := fun x (_ : Unit) => x + 1) (by intros; rfl)]
    simp
  · rw [← List.foldl_hom Prod.snd (g₂ := fun x (_ : Unit) => x + 0) (by intros; rfl)]
    simp

private theorem word_action (d : ℕ → ℕ) (k : ℕ) (v : ℕ × ℕ) :
    run (1, 0) (blockWord d k) v =
      step^[k] v + ∑ j ∈ Finset.range (k + 1), d j • atomicBlock j := by
  let M : (ℕ × ℕ) →+ (ℕ × ℕ) :=
    { toFun := step
      map_zero' := rfl
      map_add' := by intro x y; ext <;> simp [step, add_assoc, add_left_comm, add_comm] }
  induction k generalizing v with
  | zero =>
    simp only [blockWord, run_grafts, Function.iterate_zero, id_eq,
      Nat.zero_add, Finset.sum_range_one, atomicBlock]
  | succ k ih =>
    simp only [blockWord, run, List.foldl_append, List.foldl_cons, Bool.false_eq_true, if_false]
    change run (1, 0) (blockWord d k)
      (step (run (1, 0) (List.replicate (d (k + 1)) true) v)) = _
    rw [run_grafts, ih, ← Function.iterate_succ_apply]
    change M^[k + 1] (v + d (k + 1) • (1, 0)) + _ = _
    rw [iterate_map_add M, iterate_map_nsmul M]
    change step^[k + 1] v + d (k + 1) • atomicBlock (k + 1) +
      (∑ j ∈ Finset.range (k + 1), d j • atomicBlock j) =
      step^[k + 1] v + ∑ j ∈ Finset.range ((k + 1) + 1), d j • atomicBlock j
    rw [Finset.sum_range_succ _ (k + 1)]
    ac_rfl

private theorem word_counts (d : ℕ → ℕ) (k : ℕ) :
    (blockWord d k).count false = k ∧
    (blockWord d k).count true = ∑ j ∈ Finset.range (k + 1), d j := by
  induction k with
  | zero => simp [blockWord, List.count_replicate]
  | succ k ih =>
    constructor
    · simp [blockWord, List.count_replicate, ih.1]
    · rw [Finset.sum_range_succ]
      simp [blockWord, ih.2, Nat.add_comm]

private theorem positive_coefficients (H c : ℕ) (hH : 1 < H) (hc : c < H) :
    ∃ d : ℕ → ℕ,
      d = (if c = 0 then (fun _ => 0) else
        graftCoefficients (wdigits (offset H c - 2)).toFinset) ∧
      (∀ j, horizon H < j → d j = 0) ∧
      (∑ j ∈ Finset.range (horizon H + 1), d j * Nat.fib (j + 3)) = offset H c ∧
      d 0 ≤ 2 ∧ d 1 ≤ 2 ∧ (∀ j, 2 ≤ j → d j ≤ 1) ∧
      (∑ j ∈ Finset.range (horizon H + 1), d j) ≤ graftBound (horizon H) := by
  classical
  by_cases hz : c = 0
  · subst c
    refine ⟨fun _ => 0, ?_⟩
    simp [offset, graftBound]
  have ht : 2 ≤ offset H c ∧ offset H c ≤ H + 1 := by
    by_cases ho : c = 1 <;> simp [offset, hz, ho] <;> omega
  have hK : 1 ≤ horizon H ∧ H ≤ Nat.fib (horizon H + 4) := by
    unfold horizon
    exact Nat.find_spec (p := fun k : ℕ => 1 ≤ k ∧ H ≤ Nat.fib (k + 4)) _
  have hu : offset H c - 2 < Nat.fib (horizon H + 4) := by omega
  let s := (wdigits (offset H c - 2)).toFinset
  have hd := support_data (offset H c - 2) (horizon H) hu
  change (∀ i ∈ s, 2 ≤ i ∧ i ≤ horizon H + 3) ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → i + 2 ≤ j ∨ j + 2 ≤ i) ∧
    (∑ i ∈ s, Nat.fib i) = offset H c - 2 at hd
  have hsums := coefficient_sums (horizon H) hK.1 s hd.1
  refine ⟨graftCoefficients s, by simp [hz, s], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ j by omega)
    have hm : r + 5 ∉ s := by
      intro hm
      have := (hd.1 (r + 5) hm).2
      omega
    simp only [Nat.add_comm 2 r, graftCoefficients, if_neg hm]
  · rw [hsums.1, hd.2.2]
    omega
  · simp only [graftCoefficients]
    split_ifs <;> omega
  · simp only [graftCoefficients]
    split_ifs <;> omega
  · intro j hj
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
    simp only [Nat.add_comm 2 r, graftCoefficients]
    split_ifs <;> omega
  · rw [hsums.2]
    have hn := spaced_card (horizon H) (s.filter (3 ≤ ·))
      (by intro i hi; exact ⟨(Finset.mem_filter.mp hi).2,
        (hd.1 i (Finset.mem_filter.mp hi).1).2⟩)
      (by
        intro i hi j hj hne
        exact hd.2.1 i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne)
    unfold graftBound
    omega

private theorem word_quantity (d : ℕ → ℕ) (k : ℕ) (v : ℕ × ℕ) :
    quantity (run (1, 0) (blockWord d k) v) =
      quantity (step^[k] v) + ∑ j ∈ Finset.range (k + 1), d j * Nat.fib (j + 3) := by
  let Q : (ℕ × ℕ) →+ ℕ :=
    { toFun := quantity
      map_zero' := by simp [quantity]
      map_add' := by intro x y; simp [quantity]; ring }
  have hq (j : ℕ) : quantity (atomicBlock j) = Nat.fib (j + 3) := by
    have packet := GraftAffineClosure.result.2 1 (by decide) (atomicBlock j)
    rcases packet with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, atomic⟩
    exact (atomic j rfl).1.1
  rw [word_action]
  change Q (step^[k] v + ∑ j ∈ Finset.range (k + 1), d j • atomicBlock j) = _
  rw [map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_nsmul]
  change d j * quantity (atomicBlock j) = _
  rw [hq]

/-- Every offset has bounded positive coefficients and two exact chronological realizations. -/
theorem result (H : ℕ) (hH : 1 < H) :
    IsLeast {k : ℕ | 1 ≤ k ∧ H ≤ Nat.fib (k + 4)} (horizon H) ∧
    ∀ c : ℕ, c < H → ∃ d : ℕ → ℕ,
      d = (if c = 0 then (fun _ => 0) else
        graftCoefficients (wdigits (offset H c - 2)).toFinset) ∧
      (∀ j, horizon H < j → d j = 0) ∧
      (∑ j ∈ Finset.range (horizon H + 1), d j * Nat.fib (j + 3)) = offset H c ∧
      d 0 ≤ 2 ∧ d 1 ≤ 2 ∧ (∀ j, 2 ≤ j → d j ≤ 1) ∧
      (∑ j ∈ Finset.range (horizon H + 1), d j) ≤ graftBound (horizon H) ∧
      ∀ k : ℕ, k = horizon H ∨ k = horizon H + 1 →
        (blockWord d k).count false = k ∧
        (blockWord d k).count true ≤ graftBound (horizon H) ∧
        ∀ v : ℕ × ℕ,
          run (1, 0) (blockWord d k) v =
            step^[k] v + ∑ j ∈ Finset.range (k + 1), d j • atomicBlock j ∧
          quantity (run (1, 0) (blockWord d k) v) = quantity (step^[k] v) + offset H c ∧
          readout H (run (1, 0) (blockWord d k) v) =
            Nat.gcd (quantity (step^[k] v) + c) H := by
  classical
  have hK : 1 ≤ horizon H ∧ H ≤ Nat.fib (horizon H + 4) := by
    unfold horizon
    exact Nat.find_spec (p := fun k : ℕ => 1 ≤ k ∧ H ≤ Nat.fib (k + 4)) _
  refine ⟨⟨hK, ?_⟩, ?_⟩
  · intro k hk
    unfold horizon
    exact Nat.find_min' (p := fun k : ℕ => 1 ≤ k ∧ H ≤ Nat.fib (k + 4)) _ hk
  intro c hc
  obtain ⟨d, heq, hsupport, hweight, hzero, hone, hbinary, hcount⟩ :=
    positive_coefficients H c hH hc
  refine ⟨d, heq, hsupport, hweight, hzero, hone, hbinary, hcount, ?_⟩
  intro k hk
  have hsum (f : ℕ → ℕ) (h0 : f (horizon H + 1) = 0) :
      (∑ j ∈ Finset.range (k + 1), f j) = ∑ j ∈ Finset.range (horizon H + 1), f j := by
    rcases hk with rfl | rfl
    · rfl
    · rw [Finset.sum_range_succ, h0, Nat.add_zero]
  have hdnext := hsupport (horizon H + 1) (by omega)
  have hcw := word_counts d k
  refine ⟨hcw.1, ?_, ?_⟩
  · rw [hcw.2, hsum d hdnext]
    exact hcount
  intro v
  have hq : quantity (run (1, 0) (blockWord d k) v) = quantity (step^[k] v) + offset H c := by
    rw [word_quantity, hsum (fun j => d j * Nat.fib (j + 3)) (by rw [hdnext, zero_mul]), hweight]
  refine ⟨word_action d k v, hq, ?_⟩
  unfold readout
  rw [hq]
  by_cases hz : c = 0
  · simp [offset, hz]
  by_cases ho : c = 1
  · subst c
    change Nat.gcd (quantity (step^[k] v) + (H + 1)) H =
      Nat.gcd (quantity (step^[k] v) + 1) H
    rw [show quantity (step^[k] v) + (H + 1) = (quantity (step^[k] v) + 1) + H by omega,
      Nat.gcd_add_self_left]
  · simp [offset, hz, ho]

end D5.S3.Arith.FibonacciAtomic.PositiveGraftShortWords
