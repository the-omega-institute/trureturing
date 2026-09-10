/- GID: D5/S3/Arith/SumInConcatenation
   generality: G
   mirror-B: D5/B/S3/Arith/SumInConcatenation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A359482 has no positive single-digit successor and is not a permutation. -/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Infix
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum

namespace D5.S3.Arith.SumInConcatenation

/-- Decimal digits, most significant first, with zero represented by [0]. -/
def D (x : ℕ) : List ℕ := if x = 0 then [0] else (Nat.digits 10 x).reverse

/-- The decimal sum occurs in the concatenation of the two decimal operands. -/
def Legal (x y : ℕ) : Prop := (D (x + y)).IsInfix (D x ++ D y)

instance (x y : ℕ) : Decidable (Legal x y) := inferInstanceAs
  (Decidable ((D (x + y)).IsInfix (D x ++ D y)))

private theorem legal_controls : Legal 1 10 ∧ Legal 10 99 ∧ Legal 99 889 := by decide

private theorem legal_reverse {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    Legal x y ↔ (Nat.digits 10 (x + y)).IsInfix
      (Nat.digits 10 y ++ Nat.digits 10 x) := by
  simp only [Legal, D, Nat.ne_of_gt hx, Nat.ne_of_gt hy,
    show x + y ≠ 0 by omega, ↓reduceIte]
  rw [← List.reverse_append, List.reverse_infix]

private theorem shifted_digits_impossible (x d a : ℕ) (r : List ℕ)
    (hx : 0 < x) (hxrep : Nat.digits 10 x = r ++ [a])
    (hsum : Nat.digits 10 (x + d) = d :: r) : False := by
  have ha : a < 10 := Nat.digits_lt_base (by norm_num)
    (hxrep ▸ List.mem_append_right r (by simp))
  have hr : Nat.ofDigits 10 r < 10 ^ r.length :=
    Nat.ofDigits_lt_base_pow_length (by norm_num) (fun z hz =>
      Nat.digits_lt_base (by norm_num) (hxrep ▸ List.mem_append_left [a] hz))
  have heq := congrArg (Nat.ofDigits 10) hxrep
  have hval := congrArg (Nat.ofDigits 10) hsum
  simp only [Nat.ofDigits_digits, Nat.ofDigits_append, Nat.ofDigits_cons,
    Nat.ofDigits_nil, mul_zero, add_zero] at heq hval
  have hrot : 10 ^ r.length * a = 9 * Nat.ofDigits 10 r := by omega
  have hm := congrArg (· % 9) hrot
  simp [Nat.mul_mod, Nat.pow_mod] at hm
  have ha' : a = 0 ∨ a = 9 := by omega
  rcases ha' with rfl | rfl
  · simp only [mul_zero] at heq
    omega
  · omega

/-- No positive one-digit number can follow a positive operand under the substring rule. -/
theorem no_small_successor (x d : ℕ) (hx : 0 < x) (hd : 0 < d ∧ d < 10) :
    ¬ Legal x d := by
  intro h
  have hlen := Nat.le_length_digits_le 10 x (x + d) (by omega)
  have hin := (legal_reverse hx hd.1).mp h
  simp only [Nat.digits_of_lt 10 d (by omega) hd.2, List.singleton_append] at hin
  rcases List.infix_cons_iff.mp hin with hp | hi
  · obtain ⟨t, ht⟩ := hp
    have htlen := congrArg List.length ht
    simp only [List.length_append, List.length_cons] at htlen
    have htshort : t.length ≤ 1 := by omega
    cases t with
    | nil =>
      have hv := congrArg (Nat.ofDigits 10) ht
      simp only [List.append_nil, Nat.ofDigits_digits, Nat.ofDigits_cons] at hv
      omega
    | cons a t =>
      have : t = [] := by simpa using htshort
      subst t
      cases hs : Nat.digits 10 (x + d) with
      | nil => have := Nat.digits_eq_nil_iff_eq_zero.mp hs; omega
      | cons c r =>
        simp only [hs, List.cons_append, List.cons.injEq] at ht
        obtain ⟨hc, hr⟩ := ht
        subst c
        exact shifted_digits_impossible x d a r hx hr.symm hs
  · have he := hi.eq_of_length_le hlen
    have := Nat.digits.injective 10 he
    omega

private def repeated (x : ℕ) : ℕ → ℕ
  | 0 => x
  | k + 1 => x + 10 ^ (Nat.digits 10 x).length * repeated x k

private theorem repeated_digits (x k : ℕ) :
    Nat.digits 10 (repeated x (k + 1)) =
      Nat.digits 10 x ++ Nat.digits 10 (repeated x k) :=
  (Nat.digits_append_digits (by norm_num : 0 < 10)).symm

private theorem repeated_commute (x k : ℕ) :
    Nat.digits 10 x ++ Nat.digits 10 (repeated x k) =
      Nat.digits 10 (repeated x k) ++ Nat.digits 10 x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [repeated_digits]
    calc
      _ = Nat.digits 10 x ++
          (Nat.digits 10 (repeated x k) ++ Nat.digits 10 x) := congrArg _ ih
      _ = _ := (List.append_assoc _ _ _).symm

private theorem repeated_lower (x k : ℕ) (hx : 0 < x) : k + 1 ≤ repeated x k := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    have hp : 1 ≤ 10 ^ (Nat.digits 10 x).length := Nat.one_le_pow _ _ (by norm_num)
    have := Nat.mul_le_mul_right (repeated x k) hp
    simp only [repeated]
    omega

private theorem arbitrarily_large_successor (x bound : ℕ) (hx : 0 < x) :
    ∃ y, bound < y ∧ Legal x y := by
  let y := 10 ^ (Nat.digits 10 x).length * repeated x bound
  have hr := repeated_lower x bound hx
  have hp : 1 ≤ 10 ^ (Nat.digits 10 x).length := Nat.one_le_pow _ _ (by norm_num)
  have hy : bound < y := by
    have := Nat.mul_le_mul_right (repeated x bound) hp
    dsimp [y]
    omega
  refine ⟨y, hy, (legal_reverse hx (by omega)).mpr ?_⟩
  change (Nat.digits 10 (repeated x (bound + 1))).IsInfix _
  rw [repeated_digits, repeated_commute]
  dsimp [y]
  rw [Nat.digits_base_pow_mul (by norm_num) (by omega)]
  exact ⟨List.replicate (Nat.digits 10 x).length 0, [], by simp [List.append_assoc]⟩

/-- The least positive unused successor satisfying the original substring rule. -/
noncomputable def next (x : ℕ) (used : Finset ℕ) : ℕ :=
  sInf {y | 0 < y ∧ y ∉ used ∧ Legal x y}

private theorem next_spec (x : ℕ) (used : Finset ℕ) (hx : 0 < x) :
    0 < next x used ∧ next x used ∉ used ∧ Legal x (next x used) := by
  apply Nat.sInf_mem (s := {y | 0 < y ∧ y ∉ used ∧ Legal x y})
  obtain ⟨y, hy, hl⟩ := arbitrarily_large_successor x (used.sup id) hx
  refine ⟨y, by omega, ?_, hl⟩
  intro hm
  have := Finset.le_sup (f := id) hm
  exact (not_le_of_gt hy) this

/-- Current term and all terms used so far; the initial state is (1,{1}). -/
noncomputable def state : ℕ → ℕ × Finset ℕ
  | 0 => (1, {1})
  | k + 1 =>
      let y := next (state k).1 (state k).2
      (y, insert y (state k).2)

/-- OEIS indexing starts at 1. Index 0 is the same initial value by convention. -/
noncomputable def seq (n : ℕ) : ℕ := (state (n - 1)).1

private theorem state_pos (k : ℕ) : 0 < (state k).1 := by
  induction k with
  | zero => decide
  | succ k ih => exact (next_spec _ _ ih).1

private theorem state_used (k : ℕ) :
    (state k).2 = (Finset.range (k + 1)).image (fun i => (state i).1) := by
  induction k with
  | zero => simp [state]
  | succ k ih => simp [state, Finset.range_add_one, ih]

/-- At each step the term is the least positive unused legal successor. -/
theorem sequence_greedy (k : ℕ) :
    seq (k + 2) = sInf {y | 0 < y ∧
      (∀ i ∈ Finset.range (k + 1), y ≠ seq (i + 1)) ∧ Legal (seq (k + 1)) y} := by
  simp only [seq, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega, state, next]
  rw [state_used]
  congr 1
  ext y
  simp [eq_comm]

/-- Every indexed term is positive. -/
theorem sequence_pos (n : ℕ) : 0 < seq n := state_pos _

/-- Every adjacent pair from the first term onwards satisfies decimal legality. -/
theorem sequence_legal (n : ℕ) (hn : 1 ≤ n) : Legal (seq n) (seq (n + 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [seq, state, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (next_spec (state k).1 (state k).2 (state_pos k)).2.2

/-- From the second term onwards A359482 has at least two decimal digits. -/
theorem sequence_tail_ge_ten (n : ℕ) (hn : 2 ≤ n) : 10 ≤ seq n := by
  by_contra h
  have hl := sequence_legal (n - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hl
  exact no_small_successor (seq (n - 1)) (seq n) (sequence_pos _)
    ⟨sequence_pos _, by omega⟩ hl

/-- The missing positive integer 2 prevents surjectivity onto the positive integers. -/
theorem not_positive_permutation : ¬ (∀ m : ℕ, 0 < m → ∃ n, 1 ≤ n ∧ seq n = m) := by
  intro h
  obtain ⟨n, hn, he⟩ := h 2 (by decide)
  by_cases hfirst : n = 1
  · subst n
    norm_num [seq, state] at he
  · have := sequence_tail_ge_ten n (by omega)
    omega

#print axioms no_small_successor
#print axioms sequence_greedy
#print axioms sequence_pos
#print axioms sequence_legal
#print axioms sequence_tail_ge_ten
#print axioms not_positive_permutation

end D5.S3.Arith.SumInConcatenation
