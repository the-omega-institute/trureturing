/- GID: D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: The least-unused one-common-Zeckendorf-term sequence is a permutation of the positive integers. -/
import D5.S0.Conventions.WDigits
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Push

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation
open D5.S0.Conventions

/-- Fibonacci indices, starting at index two, in the canonical representation. -/
def support (m : ℕ) : Finset ℕ := (wdigits m).toFinset

/-- Exactly one common canonical Fibonacci term. -/
def Adjacent (x y : ℕ) : Prop := (support x ∩ support y).card = 1

private instance gap_trans : IsTrans ℕ (fun a b => b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem support_ge {m i : ℕ} (hi : i ∈ support m) : 2 ≤ i := by
  have hc : (wdigits m ++ [0]).Pairwise (fun a b => b + 2 ≤ a) :=
    List.isChain_iff_pairwise.mp (wdigits_isCanonical m)
  have h := (List.pairwise_append.mp hc).2.2 i (List.mem_toFinset.mp hi) 0 (by simp)
  simpa using h

private theorem fib_le {m i : ℕ} (hi : i ∈ support m) : Nat.fib i ≤ m := by
  rw [← decode_wdigits m]
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) _
    (List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, rfl⟩)

private theorem index_bound {m i : ℕ} (hi : i ∈ support m) : i ≤ m + 1 := by
  have := fib_le hi
  have := Nat.le_fib_add_one i
  omega

private theorem support_nonempty (m : ℕ) (hm : 0 < m) : (support m).Nonempty := by
  by_contra hn
  have hz : wdigits m = [] := by
    simpa [support] using (Finset.not_nonempty_iff_eq_empty.mp hn)
  have hd := decode_wdigits m
  simp [hz] at hd
  omega

private theorem support_singleton (i : ℕ) (hi : 2 ≤ i) :
    support (Nat.fib i) = {i} := by
  have hc : [i].IsZeckendorfRep := by simp [List.IsZeckendorfRep, hi]
  have hz : [i] = wdigits (Nat.fib i) := wdigits_unique hc (by simp)
  simp [support, ← hz]

private theorem support_one : support 1 = {2} := by
  simpa using support_singleton 2 (by omega)

private theorem support_pair (i j : ℕ) (hi : 2 ≤ i) (hij : i + 2 ≤ j) :
    support (Nat.fib i + Nat.fib j) = {i, j} := by
  have hc : [j, i].IsZeckendorfRep := by
    simp [List.IsZeckendorfRep, hi, hij]
  have hz : [j, i] = wdigits (Nat.fib i + Nat.fib j) :=
    wdigits_unique hc (by simp; omega)
  simp [support, ← hz, Finset.pair_comm]

private theorem support_triple (r s t : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hrs : r + 2 ≤ s ∨ s + 2 ≤ r) (hrt : r + 2 ≤ t) (hst : s + 2 ≤ t) :
    support (Nat.fib r + Nat.fib s + Nat.fib t) = {r, s, t} := by
  rcases hrs with hrs | hrs
  · have hc : [t, s, r].IsZeckendorfRep := by
      simp [List.IsZeckendorfRep, hr, hrs, hst]
    have hz : [t, s, r] = wdigits (Nat.fib r + Nat.fib s + Nat.fib t) :=
      wdigits_unique hc (by simp; omega)
    simp [support, ← hz, Finset.insert_comm, Finset.pair_comm]
  · have hc : [t, r, s].IsZeckendorfRep := by
      simp [List.IsZeckendorfRep, hs, hrs, hrt]
    have hz : [t, r, s] = wdigits (Nat.fib r + Nat.fib s + Nat.fib t) :=
      wdigits_unique hc (by simp; omega)
    simp [support, ← hz, Finset.insert_comm, Finset.pair_comm]

private theorem pair_adjacent (c i j : ℕ) (hi : i ∈ support c)
    (hj : j ∉ support c) (hij : i + 2 ≤ j) :
    Adjacent c (Nat.fib i + Nat.fib j) := by
  unfold Adjacent
  rw [support_pair i j (support_ge hi) hij]
  have he : support c ∩ {i, j} = {i} := by
    ext k
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [he]
  simp

private theorem exists_next (l : List ℕ) (c : ℕ) (hc : 0 < c) :
    ∃ m, 0 < m ∧ m ∉ l ∧ Adjacent c m := by
  obtain ⟨i, hi⟩ := support_nonempty c hc
  let j := l.sum + c + i + 5
  have hij : i + 2 ≤ j := by dsimp [j]; omega
  have hj : j ∉ support c := by
    intro h
    have := index_bound h
    dsimp [j] at this
    omega
  have hfi : 0 < Nat.fib i := Nat.fib_pos.mpr (by have := support_ge hi; omega)
  have hfj := Nat.le_fib_add_one j
  have hlarge : l.sum < Nat.fib i + Nat.fib j := by dsimp [j] at hfj; omega
  refine ⟨Nat.fib i + Nat.fib j, by omega, ?_, pair_adjacent c i j hi hj hij⟩
  intro hm
  have := List.single_le_sum (fun _ _ => Nat.zero_le _) _ hm
  omega

private noncomputable def pick (l : List ℕ) (c : ℕ) (hc : 0 < c) : ℕ :=
  Nat.find (exists_next l c hc)

private theorem pick_spec (l : List ℕ) (c : ℕ) (hc : 0 < c) :
    0 < pick l c hc ∧ pick l c hc ∉ l ∧ Adjacent c (pick l c hc) :=
  Nat.find_spec (exists_next l c hc)

private noncomputable def history : ℕ → List ℕ × {c : ℕ // 0 < c}
  | 0 => ([1], ⟨1, by omega⟩)
  | n + 1 =>
    let m := pick (history n).1 (history n).2.1 (history n).2.2
    (m :: (history n).1, ⟨m, (pick_spec _ _ _).1⟩)

private noncomputable def terms (n : ℕ) : List ℕ := (history n).1
private noncomputable def v (n : ℕ) : ℕ := (history n).2.1

private theorem v_zero : v 0 = 1 := rfl
private theorem v_pos (n : ℕ) : 0 < v n := (history n).2.2

private theorem step_spec (n : ℕ) :
    0 < v (n + 1) ∧ v (n + 1) ∉ terms n ∧ Adjacent (v n) (v (n + 1)) :=
  pick_spec (terms n) (v n) (v_pos n)

private theorem greedy (n m : ℕ) (hp : 0 < m) (hu : m ∉ terms n)
    (ha : Adjacent (v n) m) : v (n + 1) ≤ m :=
  Nat.find_min' (exists_next (terms n) (v n) (v_pos n)) ⟨hp, hu, ha⟩

private theorem mem_terms (n m : ℕ) : m ∈ terms n ↔ ∃ i ≤ n, v i = m := by
  induction n with
  | zero => simp [terms, history, v, eq_comm]
  | succ n ih =>
      change m ∈ v (n + 1) :: terms n ↔ _
      rw [List.mem_cons, ih]
      constructor
      · rintro (he | ⟨i, hi, he⟩)
        · exact ⟨n + 1, le_rfl, he.symm⟩
        · exact ⟨i, by omega, he⟩
      · rintro ⟨i, hi, he⟩
        by_cases hn : i = n + 1
        · left; simpa [hn] using he.symm
        · right; exact ⟨i, by omega, he⟩

private theorem v_injective : Function.Injective v := by
  have distinct : ∀ i j, i < j → v i ≠ v j := by
    intro i j hij he
    cases j with
    | zero => omega
    | succ j =>
        exact (step_spec j).2.1 ((mem_terms j _).mpr ⟨i, by omega, he⟩)
  intro i j he
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (distinct i j h he)
  · exact h
  · exact False.elim (distinct j i h he.symm)

private def Visited (m : ℕ) : Prop := ∃ n, v n = m

private theorem omitted_not_mem {m : ℕ} (hm : ¬ Visited m) (n : ℕ) : m ∉ terms n := by
  rw [mem_terms]
  rintro ⟨i, _, hi⟩
  exact hm ⟨i, hi⟩

/-- OEIS indexing: `a 1 = 1`; the internal history at stage `n` gives `a (n+1)`. -/
noncomputable def a (n : ℕ) : ℕ := v (n - 1)

/-- The positive unused candidates after the complete one-based prefix. -/
def Eligible (s : ℕ → ℕ) (n m : ℕ) : Prop :=
  0 < m ∧ (∀ k, 1 ≤ k → k ≤ n → s k ≠ m) ∧ Adjacent (s n) m

/-- The whole totality, numerical leastness and positive-integer permutation assertion. -/
def IsGreedyPermutation (s : ℕ → ℕ) : Prop :=
  s 1 = 1 ∧
  (∀ n, 1 ≤ n → 0 < s n) ∧
  (∀ n, 1 ≤ n → Eligible s n (s (n + 1)) ∧
    ∀ m, Eligible s n m → s (n + 1) ≤ m) ∧
  (∀ i j, 1 ≤ i → 1 ≤ j → s i = s j → i = j) ∧
  ∀ m, 1 ≤ m → ∃ n, 1 ≤ n ∧ s n = m

end D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation
