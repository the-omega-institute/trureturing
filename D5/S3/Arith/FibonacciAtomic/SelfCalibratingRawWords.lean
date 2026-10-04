/- GID: D5/S3/Arith/FibonacciAtomic/SelfCalibratingRawWords
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SelfCalibratingRawWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every chronological Fibonacci and swap word obeys both signed length bounds. -/

import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import Mathlib.Tactic

set_option autoImplicit false
open scoped Matrix
namespace D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords

def atomic (a : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  if a then !![0, 1; 1, 0]
  else D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM

def word (w : List Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  w.foldr (fun a B => B * atomic a) 1

/-- The alternating chronological word beginning with the supplied operation. -/
def alt : Bool → ℕ → List Bool
  | _, 0 => []
  | a, n + 1 => a :: alt (!a) n

/-- Both signed bounds and the chronological integral matrix structure. -/
theorem raw_word_signed_bound (w : List Bool) :
    (∀ i j : Fin 2, i ≠ j →
      -((((w.length - 1) / 2 : ℕ) : ℤ)) * word w i j ≤
        word w 1 1 - word w 0 0 ∧
      word w 1 1 - word w 0 0 ≤
        (((w.length + 1) / 2 : ℕ) : ℤ) * word w i j) ∧
    (∀ i j, 0 ≤ word w i j) ∧
    Matrix.det (word w) = (-1 : ℤ) ^ w.length ∧
    (∀ q, word (w ++ q) = word q * word w) ∧
    (∀ n : ℕ,
      word (alt false (2 * n)) = !![1, (n : ℤ); 0, 1] ∧
      word (alt true (2 * n)) = !![1, 0; (n : ℤ), 1]) ∧
    (∀ n : ℕ,
      word (alt false (2 * n + 1)) = !![0, 1; 1, (n : ℤ) + 1] ∧
      word (alt true (2 * n + 1)) = !![(n : ℤ), 1; 1, 0]) ∧
    (∀ (upper : Bool) (k : ℕ), 0 < k →
      word w = (if upper then !![1, (k : ℤ); 0, 1] else !![1, 0; (k : ℤ), 1]) →
      2 * k ≤ w.length) := by
  let L : ℕ → ℤ := fun n => ((n - 1) / 2 : ℕ)
  let H : ℕ → ℤ := fun n => ((n + 1) / 2 : ℕ)
  let Good (n : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
    ∀ i j : Fin 2, i ≠ j →
      -(L n) * B i j ≤ B 1 1 - B 0 0 ∧
      B 1 1 - B 0 0 ≤ H n * B i j
  have wn : word [] = 1 := rfl
  have wc (a : Bool) (v : List Bool) : word (a :: v) = word v * atomic a := rfl
  have wa (p q : List Bool) : word (p ++ q) = word q * word p := by
    induction p with
    | nil => simp [word]
    | cons a p ih => rw [List.cons_append, wc, ih, wc, mul_assoc]
  have mm : atomic false * atomic false = atomic false + 1 := by
    have packet := D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.result.2
      1 (by omega) (0, 0)
    have hsq : D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM ^ 2 =
        D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM + 1 := by
      tauto
    simpa [atomic, pow_two] using hsq
  have jj : atomic true * atomic true = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [atomic, Matrix.mul_apply, Fin.sum_univ_two]
  have an (a : Bool) (i j : Fin 2) : 0 ≤ atomic a i j := by
    cases a <;> fin_cases i <;> fin_cases j <;>
      norm_num [atomic, D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM]
  have nonneg : ∀ v : List Bool, ∀ i j : Fin 2, 0 ≤ word v i j := by
    intro v
    induction v with
    | nil =>
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [word]
    | cons a v ih =>
      intro i j
      rw [wc, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (an a k j))
  have widen (m n : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ)
      (hmn : m ≤ n) (hB : ∀ i j, 0 ≤ B i j) (hb : Good m B) : Good n B := by
    have hlN : (m - 1) / 2 ≤ (n - 1) / 2 :=
      Nat.div_le_div_right (Nat.sub_le_sub_right hmn 1)
    have hhN : (m + 1) / 2 ≤ (n + 1) / 2 :=
      Nat.div_le_div_right (Nat.add_le_add_right hmn 1)
    have hl : L m ≤ L n := by
      change (((m - 1) / 2 : ℕ) : ℤ) ≤ (((n - 1) / 2 : ℕ) : ℤ)
      exact_mod_cast hlN
    have hh : H m ≤ H n := by
      change (((m + 1) / 2 : ℕ) : ℤ) ≤ (((n + 1) / 2 : ℕ) : ℤ)
      exact_mod_cast hhN
    intro i j hij
    have lo := mul_le_mul_of_nonneg_right hl (hB i j)
    have hi := mul_le_mul_of_nonneg_right hh (hB i j)
    have h := hb i j hij
    constructor <;> nlinarith [h.1, h.2]
  have addGood (n : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℤ)
      (ha : Good n A) (hb : Good n B) : Good n (A + B) := by
    intro i j hij
    have a := ha i j hij
    have b := hb i j hij
    change -(L n) * (A i j + B i j) ≤
        (A 1 1 + B 1 1) - (A 0 0 + B 0 0) ∧
      (A 1 1 + B 1 1) - (A 0 0 + B 0 0) ≤ H n * (A i j + B i j)
    constructor <;> nlinarith [a.1, a.2, b.1, b.2]
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
  have pair (a : Bool) (n : ℕ) :
      word (alt a (n + 2)) = word (alt a n) * (atomic (!a) * atomic a) := by
    cases a <;> simp [alt, wc, mul_assoc]
  have evens : ∀ n : ℕ,
      word (alt false (2 * n)) = !![1, (n : ℤ); 0, 1] ∧
      word (alt true (2 * n)) = !![1, 0; (n : ℤ), 1] := by
    intro n
    induction n with
    | zero =>
      constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [alt, word]
    | succ n ih =>
      have hn : 2 * (n + 1) = 2 * n + 2 := by omega
      constructor
      · rw [hn, pair, ih.1]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [atomic, D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
            Matrix.mul_apply, Fin.sum_univ_two] <;> ring
      · rw [hn, pair, ih.2]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [atomic, D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
            Matrix.mul_apply, Fin.sum_univ_two]
  have odds (n : ℕ) :
      word (alt false (2 * n + 1)) = !![0, 1; 1, (n : ℤ) + 1] ∧
      word (alt true (2 * n + 1)) = !![(n : ℤ), 1; 1, 0] := by
    constructor
    · change word (alt true (2 * n)) * atomic false = _
      rw [(evens n).2]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [atomic, D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
          Matrix.mul_apply, Fin.sum_univ_two]
    · change word (alt false (2 * n)) * atomic true = _
      rw [(evens n).1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [atomic, Matrix.mul_apply, Fin.sum_univ_two]
  have altGood (a : Bool) (n : ℕ) : Good n (word (alt a n)) := by
    have hr := Nat.mod_lt n (by decide : 0 < 2)
    have hd := Nat.mod_add_div n 2
    have parity : (∃ j, n = 2 * j) ∨ (∃ j, n = 2 * j + 1) := by
      by_cases hz : n % 2 = 0
      · exact Or.inl ⟨n / 2, by omega⟩
      · exact Or.inr ⟨n / 2, by omega⟩
    rcases parity with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hz : word (alt a (2 * j)) 1 1 - word (alt a (2 * j)) 0 0 = 0 := by
        cases a <;> simp [(evens j).1, (evens j).2]
      intro i k hik
      simp only [hz]
      exact ⟨mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (Int.natCast_nonneg _)) (nonneg _ i k),
        mul_nonneg (Int.natCast_nonneg _) (nonneg _ i k)⟩
    · have hl : L (2 * j + 1) = (j : ℤ) := by
        dsimp [L]
        omega
      have hh : H (2 * j + 1) = ((j + 1 : ℕ) : ℤ) := by
        dsimp [H]
        omega
      cases a
      · rw [(odds j).1]
        intro i k hik
        rw [hl, hh]
        fin_cases i <;> fin_cases k <;> simp_all <;> omega
      · rw [(odds j).2]
        intro i k hik
        rw [hl, hh]
        fin_cases i <;> fin_cases k <;> simp_all <;> omega
  have all : ∀ n : ℕ, ∀ v : List Bool, v.length = n → Good n (word v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      rcases split v with ⟨p, a, q, rfl⟩ | ⟨a, m, rfl⟩
      · have hzero : (p ++ q).length < n := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hv ⊢
          omega
        have hz := widen (p ++ q).length n (word (p ++ q))
          (Nat.le_of_lt hzero) (nonneg _) (ih _ hzero _ rfl)
        cases a
        · have hone : (p ++ [false] ++ q).length < n := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hv ⊢
            omega
          have ho := widen (p ++ [false] ++ q).length n
            (word (p ++ [false] ++ q)) (Nat.le_of_lt hone)
            (nonneg _) (ih _ hone _ rfl)
          have heq : word (p ++ [false, false] ++ q) =
              word (p ++ [false] ++ q) + word (p ++ q) := by
            simp only [wa, wc, wn, one_mul, mm, add_mul, mul_add]
          rw [heq]
          exact addGood n _ _ ho hz
        · have heq : word (p ++ [true, true] ++ q) = word (p ++ q) := by
            simp only [wa, wc, wn, one_mul, jj]
          rw [heq]
          exact hz
      · have hm : m = n := by simpa only [alen] using hv
        simpa only [hm] using altGood a m
  have determinant : ∀ v : List Bool,
      Matrix.det (word v) = (-1 : ℤ) ^ v.length := by
    intro v
    induction v with
    | nil => simp [word]
    | cons a v ih =>
      rw [wc, Matrix.det_mul, ih]
      have ha : Matrix.det (atomic a) = -1 := by
        cases a <;> norm_num [atomic,
          D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM, Matrix.det_fin_two]
      simp [ha, pow_succ]
  have rows (v : List Bool) (i : Fin 2) : ∃ j : Fin 2, 0 < word v i j := by
    by_contra h
    have hz : ∀ j, word v i j = 0 := by
      intro j
      have : ¬ 0 < word v i j := fun hj => h ⟨j, hj⟩
      exact le_antisymm (le_of_not_gt this) (nonneg v i j)
    have hd := determinant v
    have hp : (-1 : ℤ) ^ v.length ≠ 0 := pow_ne_zero _ (by norm_num)
    have h0 := hz 0
    have h1 := hz 1
    fin_cases i
    · change word v 0 0 = 0 at h0
      change word v 0 1 = 0 at h1
      simp [Matrix.det_fin_two, h0, h1] at hd
      exact hp hd.symm
    · change word v 1 0 = 0 at h0
      change word v 1 1 = 0 at h1
      simp [Matrix.det_fin_two, h0, h1] at hd
      exact hp hd.symm
  have cols (v : List Bool) (j : Fin 2) : ∃ i : Fin 2, 0 < word v i j := by
    by_contra h
    have hz : ∀ i, word v i j = 0 := by
      intro i
      have : ¬ 0 < word v i j := fun hi => h ⟨i, hi⟩
      exact le_antisymm (le_of_not_gt this) (nonneg v i j)
    have hd := determinant v
    have hp : (-1 : ℤ) ^ v.length ≠ 0 := pow_ne_zero _ (by norm_num)
    have h0 := hz 0
    have h1 := hz 1
    fin_cases j
    · change word v 0 0 = 0 at h0
      change word v 1 0 = 0 at h1
      simp [Matrix.det_fin_two, h0, h1] at hd
      exact hp hd.symm
    · change word v 0 1 = 0 at h0
      change word v 1 1 = 0 at h1
      simp [Matrix.det_fin_two, h0, h1] at hd
      exact hp hd.symm
  have mmpos (p q : List Bool) (i j : Fin 2) :
      0 < word (p ++ [false, false] ++ q) i j := by
    have hm : ∀ r s : Fin 2, 0 < (atomic false * atomic false) r s := by
      intro r s
      fin_cases r <;> fin_cases s <;>
        norm_num [atomic, D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
          Matrix.mul_apply, Fin.sum_univ_two]
    obtain ⟨r, hr⟩ := rows q i
    obtain ⟨s, hs⟩ := cols p j
    have mid : ∀ u, 0 ≤ (word q * (atomic false * atomic false)) i u := by
      intro u
      rw [Matrix.mul_apply]
      exact Finset.sum_nonneg (fun t _ => mul_nonneg (nonneg q i t) (hm t u).le)
    have hp : 0 < (word q * (atomic false * atomic false)) i s := by
      rw [Matrix.mul_apply]
      exact Finset.sum_pos' (fun t _ => mul_nonneg (nonneg q i t) (hm t s).le)
        ⟨r, Finset.mem_univ _, mul_pos hr (hm r s)⟩
    have eq : word (p ++ [false, false] ++ q) =
        (word q * (atomic false * atomic false)) * word p := by
      simp only [wa, wc, wn, one_mul, mul_assoc]
    rw [eq, Matrix.mul_apply]
    exact Finset.sum_pos' (fun t _ => mul_nonneg (mid t) (nonneg p t j))
      ⟨s, Finset.mem_univ _, mul_pos hp hs⟩
  have shortest : ∀ n : ℕ, ∀ v : List Bool, v.length = n →
      ∀ (upper : Bool) (k : ℕ), 0 < k →
        word v = (if upper then !![1, (k : ℤ); 0, 1] else !![1, 0; (k : ℤ), 1]) →
        2*k ≤ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv upper k hk he
      rcases split v with ⟨p, a, q, rfl⟩ | ⟨a, m, rfl⟩
      · cases a
        · have hh := mmpos p q (if upper then 1 else 0) (if upper then 0 else 1)
          rw [he] at hh
          cases upper <;> norm_num at hh
        · have heq : word (p ++ [true, true] ++ q) = word (p ++ q) := by
            simp only [wa, wc, wn, one_mul, jj]
          have hlen : (p ++ q).length < n := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hv ⊢
            omega
          have hb := ih _ hlen _ rfl upper k hk (heq.symm.trans he)
          omega
      · have hm : m = n := by simpa only [alen] using hv
        have parity : (∃ j, m = 2*j) ∨ (∃ j, m = 2*j+1) := by
          have := Nat.mod_add_div m 2
          have := Nat.mod_lt m (by decide : 0 < 2)
          by_cases h : m % 2 = 0
          · exact Or.inl ⟨m/2, by omega⟩
          · exact Or.inr ⟨m/2, by omega⟩
        rcases parity with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · cases a
          · rw [(evens j).1] at he
            have h01 := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℤ => B 0 1) he
            have h10 := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℤ => B 1 0) he
            cases upper <;> simp at h01 h10 <;> omega
          · rw [(evens j).2] at he
            have h01 := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℤ => B 0 1) he
            have h10 := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℤ => B 1 0) he
            cases upper <;> simp at h01 h10 <;> omega
        · cases a
          · rw [(odds j).1] at he
            have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℤ => B 0 0) he
            cases upper <;> norm_num at h
          · rw [(odds j).2] at he
            have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℤ => B 1 1) he
            cases upper <;> norm_num at h
  exact ⟨all w.length w rfl, nonneg w, determinant w, wa w, evens, odds,
    shortest w.length w rfl⟩

#print axioms raw_word_signed_bound

end D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords
