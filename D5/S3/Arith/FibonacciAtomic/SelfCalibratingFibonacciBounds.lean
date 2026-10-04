/- GID: D5/S3/Arith/FibonacciAtomic/SelfCalibratingFibonacciBounds
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SelfCalibratingFibonacciBounds
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal Fibonacci and swap words obey sharp absolute and signed Fibonacci bounds. -/

import D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords

set_option autoImplicit false
open scoped Matrix

namespace D5.S3.Arith.FibonacciAtomic.SelfCalibratingFibonacciBounds

open D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords (atomic word alt)
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (matrixM atomicBlock blockMatrix step)

/-- Five bounds at the literal word length, with common and conjugate sharpness words. -/
theorem raw_word_fibonacci_bounds :
    (∀ w : List Bool,
      word w 0 1 ≤ (Nat.fib w.length : ℤ) ∧
      word w 1 0 ≤ (Nat.fib w.length : ℤ) ∧
      |word w 1 1 - word w 0 0| ≤ (Nat.fib w.length : ℤ) ∧
      -(word w 1 1 - word w 0 0) ≤ (Nat.fib (w.length - 2) : ℤ) ∧
      (word w 1 1 - word w 0 0) - 2 * word w 0 1 ≤
        (Nat.fib (w.length - 2) : ℤ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      let v := List.replicate n false
      v.length = n ∧ word v 0 1 = (Nat.fib n : ℤ) ∧
      word v 1 0 = (Nat.fib n : ℤ) ∧
      |word v 1 1 - word v 0 0| = (Nat.fib n : ℤ)) ∧
    (∀ n : ℕ, 3 ≤ n →
      let v := [true] ++ List.replicate (n - 2) false ++ [true]
      v.length = n ∧ -(word v 1 1 - word v 0 0) = (Nat.fib (n - 2) : ℤ)) := by
  let F : ℕ → ℤ := fun n => Nat.fib n
  let K : ℕ → ℤ := fun n => Nat.fib (n - 2)
  let Good (n : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
    B 0 1 ≤ F n ∧ B 1 0 ≤ F n ∧
    -(F n) ≤ B 1 1 - B 0 0 ∧ B 1 1 - B 0 0 ≤ F n ∧
    -(B 1 1 - B 0 0) ≤ K n ∧ B 1 1 - B 0 0 - 2 * B 0 1 ≤ K n
  have wn : word [] = 1 := rfl
  have wc (a : Bool) (v : List Bool) : word (a :: v) = word v * atomic a := rfl
  have wa (p q : List Bool) : word (p ++ q) = word q * word p :=
    (SelfCalibratingRawWords.raw_word_signed_bound p).2.2.2.1 q
  have evens (j : ℕ) :
      word (alt false (2 * j)) = !![1, (j : ℤ); 0, 1] ∧
      word (alt true (2 * j)) = !![1, 0; (j : ℤ), 1] :=
    (SelfCalibratingRawWords.raw_word_signed_bound []).2.2.2.2.1 j
  have odds (j : ℕ) :
      word (alt false (2 * j + 1)) = !![0, 1; 1, (j : ℤ) + 1] ∧
      word (alt true (2 * j + 1)) = !![(j : ℤ), 1; 1, 0] :=
    (SelfCalibratingRawWords.raw_word_signed_bound []).2.2.2.2.2.1 j
  have mm : atomic false * atomic false = atomic false + 1 := by
    have packet := GraftAffineClosure.result.2 1 (by omega) (0, 0)
    have hsq : matrixM ^ 2 = matrixM + 1 := by tauto
    simpa [atomic, pow_two] using hsq
  have jj : atomic true * atomic true = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [atomic, Matrix.mul_apply, Fin.sum_univ_two]
  have fmono {m n : ℕ} (h : m ≤ n) : F m ≤ F n := by
    dsimp [F]
    exact_mod_cast Nat.fib_mono h
  have kmono {m n : ℕ} (h : m ≤ n) : K m ≤ K n := by
    dsimp [K]
    exact_mod_cast Nat.fib_mono (Nat.sub_le_sub_right h 2)
  have fsum (n : ℕ) (hn : 2 ≤ n) : F (n - 1) + F (n - 2) = F n := by
    have heq : n = (n - 2) + 2 := by omega
    conv_rhs => rw [heq]
    dsimp [F]
    rw [Nat.fib_add_two, Nat.cast_add]
    have hindex : n - 1 = (n - 2) + 1 := by omega
    rw [hindex]
    ring
  have ksum (n : ℕ) (hn : 2 ≤ n) : K (n - 1) + K (n - 2) ≤ K n := by
    by_cases h4 : 4 ≤ n
    · have heq : n = (n - 4) + 4 := by omega
      have h1 : n - 1 - 2 = (n - 4) + 1 := by omega
      have h2 : n - 2 - 2 = n - 4 := by omega
      have h3 : n - 2 = (n - 4) + 2 := by omega
      dsimp [K]
      rw [h1, h2, h3, Nat.fib_add_two, Nat.cast_add]
      omega
    · interval_cases n <;> norm_num [K]
  have widen {m n : ℕ} (B : Matrix (Fin 2) (Fin 2) ℤ)
      (hmn : m ≤ n) (hb : Good m B) : Good n B := by
    have hf := fmono hmn
    have hk := kmono hmn
    dsimp [Good] at hb ⊢
    rcases hb with ⟨hb, hc, hlo, hhi, hneg, hshift⟩
    exact ⟨hb.trans hf, hc.trans hf, by linarith, hhi.trans hf,
      hneg.trans hk, hshift.trans hk⟩
  have addGood (n : ℕ) (hn : 2 ≤ n) (A B : Matrix (Fin 2) (Fin 2) ℤ)
      (ha : Good (n - 1) A) (hb : Good (n - 2) B) : Good n (A + B) := by
    have hf := fsum n hn
    have hk := ksum n hn
    dsimp [Good] at ha hb ⊢
    rcases ha with ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩
    rcases hb with ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩
    change A 0 1 + B 0 1 ≤ F n ∧ A 1 0 + B 1 0 ≤ F n ∧
      -(F n) ≤ (A 1 1 + B 1 1) - (A 0 0 + B 0 0) ∧
      (A 1 1 + B 1 1) - (A 0 0 + B 0 0) ≤ F n ∧
      -((A 1 1 + B 1 1) - (A 0 0 + B 0 0)) ≤ K n ∧
      (A 1 1 + B 1 1) - (A 0 0 + B 0 0) - 2 * (A 0 1 + B 0 1) ≤ K n
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have alen : ∀ a n, (alt a n).length = n := by
    intro a n
    induction n generalizing a with
    | zero => rfl
    | succ n ih => simp [alt, ih]
  have split : ∀ v : List Bool,
      (∃ p a q, v = p ++ [a, a] ++ q) ∨ ∃ a n, v = alt a n := by
    intro v
    induction v with
    | nil => exact Or.inr ⟨false, 0, rfl⟩
    | cons a v ih =>
      rcases ih with ⟨p, b, q, hv⟩ | ⟨b, n, hv⟩
      · exact Or.inl ⟨a :: p, b, q, by
          simpa only [List.cons_append] using congrArg (List.cons a) hv⟩
      · subst v
        cases n with
        | zero => exact Or.inr ⟨a, 1, rfl⟩
        | succ n =>
          by_cases hab : a = b
          · subst b
            exact Or.inl ⟨[], a, alt (!a) n, rfl⟩
          · have hb : b = !a := by cases a <;> cases b <;> simp_all
            subst b
            exact Or.inr ⟨a, n + 2, rfl⟩
  have linearFib (j : ℕ) : (j : ℤ) ≤ (Nat.fib (2 * j - 1) : ℤ) := by
    by_cases hsmall : j ≤ 2
    · interval_cases j <;> norm_num [Nat.fib_add_two]
    · have h5 : 5 ≤ 2 * j - 1 := by omega
      have h := Nat.le_fib_self h5
      have hj : j ≤ 2 * j - 1 := by omega
      exact_mod_cast hj.trans h
  have altGood (a : Bool) (n : ℕ) : Good n (word (alt a n)) := by
    have hr := Nat.mod_lt n (by decide : 0 < 2)
    have hd := Nat.mod_add_div n 2
    have parity : (∃ j, n = 2 * j) ∨ (∃ j, n = 2 * j + 1) := by
      by_cases hz : n % 2 = 0
      · exact Or.inl ⟨n / 2, by omega⟩
      · exact Or.inr ⟨n / 2, by omega⟩
    rcases parity with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hj := linearFib j
      have hf : (Nat.fib (2 * j - 1) : ℤ) ≤ F (2 * j) := by
        exact fmono (Nat.sub_le _ _)
      have hF : 0 ≤ F (2 * j) := Int.natCast_nonneg _
      have hK : 0 ≤ K (2 * j) := Int.natCast_nonneg _
      cases a
      · rw [(evens j).1]
        dsimp [Good]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith
      · rw [(evens j).2]
        dsimp [Good]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith
    · have hj := linearFib j
      have hj1 := linearFib (j + 1)
      have hindex : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [hindex, Nat.cast_add, Nat.cast_one] at hj1
      have hKindex : 2 * j + 1 - 2 = 2 * j - 1 := by omega
      have hK : 0 ≤ K (2 * j + 1) := Int.natCast_nonneg _
      have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg _
      change (j : ℤ) + 1 ≤ F (2 * j + 1) at hj1
      have hjK : (j : ℤ) ≤ K (2 * j + 1) := by
        simpa only [K, hKindex] using hj
      cases a
      · rw [(odds j).1]
        dsimp [Good]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith
      · rw [(odds j).2]
        dsimp [Good]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith
  have all : ∀ n : ℕ, ∀ v : List Bool, v.length = n → Good n (word v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      rcases split v with ⟨p, a, q, rfl⟩ | ⟨a, m, rfl⟩
      · have hzero : (p ++ q).length < n := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hv ⊢
          omega
        have hn : 2 ≤ n := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hv
          omega
        have hz := ih _ hzero (p ++ q) rfl
        cases a
        · have hone : (p ++ [false] ++ q).length < n := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hv ⊢
            omega
          have ho := ih _ hone (p ++ [false] ++ q) rfl
          have hl0 : (p ++ q).length = n - 2 := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hv ⊢
            omega
          have hl1 : (p ++ [false] ++ q).length = n - 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hv ⊢
            omega
          rw [hl0] at hz
          rw [hl1] at ho
          have heq : word (p ++ [false, false] ++ q) =
              word (p ++ [false] ++ q) + word (p ++ q) := by
            simp only [wa, wc, wn, one_mul, mm, add_mul, mul_add]
          rw [heq]
          exact addGood n hn _ _ ho hz
        · have heq : word (p ++ [true, true] ++ q) = word (p ++ q) := by
            simp only [wa, wc, wn, one_mul, jj]
          rw [heq]
          exact widen _ (Nat.le_of_lt hzero) hz
      · have hm : m = n := by simpa only [alen] using hv
        simpa only [hm] using altGood a m
  have replicatePower : ∀ n : ℕ, word (List.replicate n false) = matrixM ^ n := by
    intro n
    induction n with
    | zero => simp [word]
    | succ n ih => simp [List.replicate_succ, wc, ih, atomic, pow_succ]
  have powerForm (n : ℕ) (hn : 1 ≤ n) :
      word (List.replicate n false) =
        !![(Nat.fib (n - 1) : ℤ), (Nat.fib n : ℤ);
          (Nat.fib n : ℤ), (Nat.fib (n - 1) : ℤ) + (Nat.fib n : ℤ)] := by
    have packet := GraftAffineClosure.result.2 1 (by omega) (atomicBlock n)
    rcases packet with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, atomicPacket⟩
    have ap := atomicPacket n rfl
    have block : blockMatrix n = matrixM ^ n := ap.2.2.2.2.2.1
    have coords : atomicBlock n = (Nat.fib (n - 1), Nat.fib n) :=
      ap.2.2.2.2.1 (by omega)
    rw [replicatePower, ← block]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMatrix, coords, step, Nat.cast_add]
  refine ⟨?_, ?_, ?_⟩
  · intro w
    have h := all w.length w rfl
    dsimp [Good, F, K] at h
    exact ⟨h.1, h.2.1, abs_le.mpr ⟨h.2.2.1, h.2.2.2.1⟩,
      h.2.2.2.2.1, h.2.2.2.2.2⟩
  · intro n hn
    dsimp
    rw [powerForm n hn]
    simp [List.length_replicate, abs_of_nonneg (Int.natCast_nonneg (Nat.fib n))]
  · intro n hn
    dsimp
    have hm : 1 ≤ n - 2 := by omega
    constructor
    · simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate]
      omega
    · simp only [wc, wa, powerForm (n - 2) hm, wn, one_mul]
      norm_num [atomic, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms raw_word_fibonacci_bounds

end D5.S3.Arith.FibonacciAtomic.SelfCalibratingFibonacciBounds
