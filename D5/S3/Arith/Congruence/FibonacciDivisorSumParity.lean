/- GID: D5/S3/Arith/Congruence/FibonacciDivisorSumParity
   generality: G
   mirror-B: none(waiver:universal-finite-set-classification)
   mirror-E: none(waiver:all-positive-moduli)
   anchors: []
   digest: One-containing distinct Fibonacci sums have a forced alternating shape, settling A339621. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Congruence.FibonacciDivisorSumParity

open Finset

private abbrev w (i : ℕ) : ℕ := Nat.fib (i + 2)

/-- Indices of the unique one-containing representation of `F(2*r+2)`.
Index zero represents the single VALUE one; the duplicate `F(1)` is not used. -/
def alternatingIndices (r : ℕ) : Finset ℕ :=
  insert 0 ((range r).image fun j => 2 * j + 1)

/-- The actual finite set of positive divisors that are Fibonacci values. -/
noncomputable def fibonacciDivisors (N : ℕ) : Finset ℕ := by
  classical
  exact N.divisors.filter fun d => ∃ n : ℕ, Nat.fib n = d

/-- The sum of DISTINCT divisor values, so one contributes exactly once. -/
noncomputable def fibonacciDivisorSum (N : ℕ) : ℕ :=
  ∑ d ∈ fibonacciDivisors N, d

private lemma w_rec (i : ℕ) : w (i + 2) = w i + w (i + 1) := by
  simpa only [w, Nat.add_assoc] using (Nat.fib_add_two (n := i + 2))

private lemma prefix_sum (k : ℕ) : (∑ i ∈ range k, w i) + 2 = w (k + 1) := by
  induction k with
  | zero => norm_num [w, Nat.fib_add_two]
  | succ k ih =>
    have hr := w_rec k
    rw [sum_range_succ]
    change ((∑ i ∈ range k, w i) + w k) + 2 = w (k + 2)
    omega

private lemma pattern_succ (r : ℕ) :
    alternatingIndices (r + 1) = insert (2 * r + 1) (alternatingIndices r) := by
  simp only [alternatingIndices, range_succ, image_insert]
  exact insert_comm 0 (2 * r + 1) _

private lemma top_not_mem_pattern (r : ℕ) : 2 * r + 1 ∉ alternatingIndices r := by
  intro h
  simp only [alternatingIndices, mem_insert, mem_image, mem_range] at h
  rcases h with h | ⟨j, hj, heq⟩ <;> omega

private lemma pattern_sum (r : ℕ) :
    (∑ i ∈ alternatingIndices r, w i) = Nat.fib (2 * r + 2) := by
  induction r with
  | zero => simp [alternatingIndices, w]
  | succ r ih =>
    rw [pattern_succ, sum_insert (top_not_mem_pattern r), ih]
    have hr := Nat.fib_add_two (n := 2 * r + 2)
    have hleft : (2 * r + 1) + 2 = (2 * r + 2) + 1 := by omega
    have hright : 2 * (r + 1) + 2 = (2 * r + 2) + 2 := by omega
    change Nat.fib ((2 * r + 1) + 2) + Nat.fib (2 * r + 2) = _
    rw [hleft, hright, hr, Nat.add_comm]

/-- A nontrivial anchored sum cannot use a summand as large as its target. -/
private lemma indices_lt (s : Finset ℕ) (h0 : 0 ∈ s) (n : ℕ) (hn : 0 < n)
    (hs : (∑ i ∈ s, w i) = w n) : ∀ i ∈ s, i < n := by
  intro i hi
  by_contra h
  have hni : n ≤ i := by omega
  have hi0 : i ≠ 0 := by omega
  have hzero : 0 ∈ s.erase i := mem_erase.mpr ⟨Ne.symm hi0, h0⟩
  have hone : 1 ≤ ∑ j ∈ s.erase i, w j := by
    simpa only [w, Nat.zero_add, Nat.fib_two] using
      (single_le_sum (fun j (_ : j ∈ s.erase i) => Nat.zero_le (w j)) hzero)
  have hdecomp := sum_erase_add s w hi
  have hmono : w n ≤ w i := Nat.fib_add_two_strictMono.monotone hni
  omega

private lemma sum_one (s : Finset ℕ) (h0 : 0 ∈ s)
    (hs : (∑ i ∈ s, w i) = w 0) : s = {0} := by
  ext i
  simp only [mem_singleton]
  constructor
  · intro hi
    have hle : w i ≤ ∑ j ∈ s, w j :=
      single_le_sum (fun j (_ : j ∈ s) => Nat.zero_le (w j)) hi
    by_contra hi0
    have hlt : w 0 < w i := Nat.fib_add_two_strictMono (by omega)
    omega
  · rintro rfl
    exact h0

private lemma anchored_classification (n : ℕ) (s : Finset ℕ) (h0 : 0 ∈ s)
    (hs : (∑ i ∈ s, w i) = w n) :
    ∃ r : ℕ, n = 2 * r ∧ s = alternatingIndices r := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨0, by omega, ?_⟩
      simpa [alternatingIndices] using sum_one s h0 hs
    have hlt := indices_lt s h0 n (by omega) hs
    by_cases hn1 : n = 1
    · subst n
      have hset : s = {0} := by
        ext i
        simp only [mem_singleton]
        constructor
        · intro hi
          have := hlt i hi
          omega
        · rintro rfl
          exact h0
      rw [hset] at hs
      norm_num [w, Nat.fib_add_two] at hs
    let t := n - 2
    have hnt : n = t + 2 := by dsimp [t]; omega
    have hpred : t + 1 ∈ s := by
      by_contra hnot
      have hsub : s ⊆ range (t + 1) := by
        intro i hi
        apply mem_range.mpr
        have hi_bound := hlt i hi
        have hne : i ≠ t + 1 := by
          intro heq
          exact hnot (heq ▸ hi)
        omega
      have hbound : (∑ i ∈ s, w i) ≤ ∑ i ∈ range (t + 1), w i :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      have hprefix := prefix_sum (t + 1)
      have hw : w (t + 1 + 1) = w n := by congr 1; omega
      rw [hw] at hprefix
      omega
    have hzero : 0 ∈ s.erase (t + 1) := mem_erase.mpr ⟨by omega, h0⟩
    have hdecomp := sum_erase_add s w hpred
    have hrec : w n = w t + w (t + 1) := by rw [hnt]; exact w_rec t
    have hrest : (∑ i ∈ s.erase (t + 1), w i) = w t := by omega
    obtain ⟨r, htr, hr⟩ := ih t (by omega) (s.erase (t + 1)) hzero hrest
    refine ⟨r + 1, by omega, ?_⟩
    calc
      s = insert (t + 1) (s.erase (t + 1)) := (insert_erase hpred).symm
      _ = insert (2 * r + 1) (alternatingIndices r) := by rw [hr, htr]
      _ = alternatingIndices (r + 1) := (pattern_succ r).symm

/-- Complete classification, with no nonadjacency, divisibility or congruence assumption.
The finite set indexes the distinct values `F(2), F(3), ...` and must contain zero. -/
theorem one_containing_fibonacci_sum (s : Finset ℕ) (h0 : 0 ∈ s) (n : ℕ) :
    (∑ i ∈ s, Nat.fib (i + 2)) = Nat.fib (n + 2) ↔
      ∃ r : ℕ, n = 2 * r ∧ s = alternatingIndices r := by
  constructor
  · exact anchored_classification n s h0
  · rintro ⟨r, rfl, rfl⟩
    exact pattern_sum r

/-- This bound is proved complete below, rather than being a truncated search assumption. -/
private def divisorIndices (N : ℕ) : Finset ℕ :=
  (range N).filter fun i => w i ∣ N

private lemma shifted_witness {v : ℕ} (hv : 0 < v) (hf : ∃ n, Nat.fib n = v) :
    ∃ i, w i = v := by
  obtain ⟨n, hn⟩ := hf
  cases n with
  | zero => simp only [Nat.fib_zero] at hn; omega
  | succ n =>
    cases n with
    | zero => exact ⟨0, by simpa only [w, Nat.zero_add, Nat.fib_two, Nat.fib_one] using hn⟩
    | succ i => exact ⟨i, by simpa only [w, Nat.succ_eq_add_one, Nat.add_assoc] using hn⟩

private lemma indices_image (N : ℕ) (hN : 0 < N) :
    (divisorIndices N).image w = fibonacciDivisors N := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hd
    have hi' := (mem_filter.mp hi).2
    apply mem_filter.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨hi', by omega⟩, ⟨i + 2, rfl⟩⟩
  · intro hd
    obtain ⟨hdN, hf⟩ := mem_filter.mp hd
    have hdiv := (Nat.mem_divisors.mp hdN).1
    have hdpos : 0 < d := by
      by_contra hn
      have hz : d = 0 := by omega
      subst d
      have : N = 0 := by simpa using hdiv
      omega
    obtain ⟨i, hi⟩ := shifted_witness hdpos hf
    refine mem_image.mpr ⟨i, mem_filter.mpr ⟨?_, ?_⟩, hi⟩
    · apply mem_range.mpr
      have hle : w i ≤ N := by rw [hi]; exact Nat.le_of_dvd hN hdiv
      have hindex := Nat.le_fib_add_one (i + 2)
      change i + 2 ≤ w i + 1 at hindex
      omega
    · rwa [hi]

private lemma sum_indices (N : ℕ) (hN : 0 < N) :
    fibonacciDivisorSum N = ∑ i ∈ divisorIndices N, w i := by
  classical
  unfold fibonacciDivisorSum
  rw [← indices_image N hN]
  exact sum_image (fun i _ j _ hij => Nat.fib_add_two_strictMono.injective hij)

/-- Stronger than A339621: the exact divisor-set shape for EVERY positive integer. -/
theorem fibonacci_divisor_sum_rigidity (N : ℕ) (hN : 0 < N)
    (hf : ∃ n : ℕ, fibonacciDivisorSum N = Nat.fib n) :
    ∃ r : ℕ,
      fibonacciDivisorSum N = Nat.fib (2 * r + 2) ∧
      fibonacciDivisors N = (alternatingIndices r).image (fun i => Nat.fib (i + 2)) := by
  classical
  have hzero : 0 ∈ divisorIndices N := by
    simp [divisorIndices, w, hN]
  have hone : 1 ≤ ∑ i ∈ divisorIndices N, w i := by
    simpa only [w, Nat.zero_add, Nat.fib_two] using
      (single_le_sum (fun i (_ : i ∈ divisorIndices N) => Nat.zero_le (w i)) hzero)
  have hpos : 0 < fibonacciDivisorSum N := by rw [sum_indices N hN]; omega
  obtain ⟨n, hn⟩ := shifted_witness hpos (by
    obtain ⟨n, hn⟩ := hf
    exact ⟨n, hn.symm⟩)
  have hsum : (∑ i ∈ divisorIndices N, w i) = w n := by
    rw [← sum_indices N hN, hn]
  obtain ⟨r, hnr, hr⟩ := anchored_classification n (divisorIndices N) hzero hsum
  refine ⟨r, ?_, ?_⟩
  · rw [← hn, hnr]
  · rw [← indices_image N hN, hr]

/-- Michel Lagneau's OEIS A339621 conjecture, with the value one represented by F(2). -/
theorem a339621_conjecture (m : ℕ)
    (hf : ∃ n : ℕ, fibonacciDivisorSum (m ^ 2 + 1) = Nat.fib n) :
    ∃ r : ℕ, 0 < r ∧ fibonacciDivisorSum (m ^ 2 + 1) = Nat.fib (2 * r) := by
  obtain ⟨r, hr, _⟩ := fibonacci_divisor_sum_rigidity (m ^ 2 + 1) (by omega) hf
  refine ⟨r + 1, by omega, ?_⟩
  simpa only [Nat.mul_add, Nat.mul_one] using hr

end D5.S3.Arith.Congruence.FibonacciDivisorSumParity
