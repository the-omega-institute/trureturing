/- GID: D5/S1/Words/KurkovReversedQBellRowPolynomial
   generality: I
   mirror-B: D5/B/S1/Words/KurkovReversedQBellRowPolynomial
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.BigOperators]
   utility: none
   digest: Kurkov's diagonal equals the reversed next q-Bell row polynomial. -/

import Mathlib.Algebra.Polynomial.BigOperators

noncomputable section

open Finset Polynomial
open scoped BigOperators Polynomial

namespace D5.S1.Words.KurkovReversedQBellRowPolynomial

/-- The q-Bell row polynomials from OEIS A126347, using Wagner's recurrence. -/
noncomputable def qBell : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 =>
      ∑ k : Fin (n + 1),
        C (n.choose k : ℤ) * qBell k * X ^ (k : ℕ)
termination_by n => n
decreasing_by omega

/-- Kurkov's triangular recurrence, totalized by zero beyond row zero's diagonal. -/
noncomputable def kurkovR : ℕ → ℕ → Polynomial ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k => kurkovR n n + X ^ (n + 1) * ∑ j ∈ range k, kurkovR n j

/-- Every q-Bell row is monic and has the triangular degree required for fixed-row reversal. -/
private theorem qBell_monic_degree :
    ∀ n : ℕ, (qBell n).Monic ∧ (qBell n).natDegree = n.choose 2 := by
  have qBell_succ (n : ℕ) :
      qBell (n + 1) =
        ∑ k ∈ range (n + 1), C (n.choose k : ℤ) * qBell k * X ^ k := by
    rw [qBell, Finset.sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro k hk
    simp [mem_range.mp hk]
  have triangle_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
    simp [Nat.choose, Nat.add_comm]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [qBell]
    | succ n =>
      have ihn := ih n (by omega)
      rw [qBell_succ, sum_range_succ]
      simp only [Nat.choose_self, Nat.cast_one, C_1, one_mul]
      by_cases hn : n = 0
      · subst n
        simp [qBell]
      · have hleadMonic : (qBell n * X ^ n).Monic := ihn.1.mul (monic_X.pow n)
        have hleadDegree : (qBell n * X ^ n).natDegree = (n + 1).choose 2 := by
          rw [natDegree_mul' (by simp [ihn.1]), ihn.2, natDegree_X_pow, triangle_succ]
        have hlowerDegree :
            (∑ k ∈ range n, C (n.choose k : ℤ) * qBell k * X ^ k).natDegree ≤
              n.choose 2 := by
          apply natDegree_sum_le_of_forall_le
          intro k hk
          have hkn : k < n := mem_range.mp hk
          have hkdeg := (ih k (by omega)).2
          calc
            (C (n.choose k : ℤ) * qBell k * X ^ k).natDegree
                = (C (n.choose k : ℤ) * (qBell k * X ^ k)).natDegree := by rw [mul_assoc]
            _ ≤ (qBell k * X ^ k).natDegree := natDegree_C_mul_le _ _
            _ ≤ (qBell k).natDegree + (X ^ k : Polynomial ℤ).natDegree := natDegree_mul_le
            _ = k.choose 2 + k := by rw [hkdeg, natDegree_X_pow]
            _ = (k + 1).choose 2 := (triangle_succ k).symm
            _ ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
        have hlowerLt :
            (∑ k ∈ range n, C (n.choose k : ℤ) * qBell k * X ^ k).natDegree <
              (qBell n * X ^ n).natDegree := by
          rw [hleadDegree, triangle_succ]
          omega
        exact ⟨hleadMonic.add_of_right (degree_lt_degree hlowerLt),
          natDegree_add_eq_right_of_natDegree_lt hlowerLt |>.trans hleadDegree⟩

/-- The Pascal expansion that aligns Kurkov's partial row sums with the q-Bell convolution. -/
private theorem kurkovR_pascal_expansion (n k : ℕ) (hk : k ≤ n) :
    kurkovR n k =
      ∑ i ∈ range (k + 1),
        C (k.choose i : ℤ) *
          X ^ ((n + 1).choose 2 - (n - i + 1).choose 2) *
            (match n - i with
            | 0 => 1
            | m + 1 => kurkovR m m) := by
  set triangle : ℕ → ℕ := fun m => m.choose 2 with triangle_def
  let diagonal : ℕ → Polynomial ℤ := fun m =>
    match m with
    | 0 => 1
    | r + 1 => kurkovR r r
  let binomialTerm : (ℕ → Polynomial ℤ) → ℕ → ℕ → ℕ → Polynomial ℤ := fun d m r i =>
    C (r.choose i : ℤ) *
      X ^ (triangle (m + 1) - triangle (m - i + 1)) * d (m - i)
  let pascalRow : (ℕ → Polynomial ℤ) → ℕ → ℕ → Polynomial ℤ := fun d m r =>
    ∑ i ∈ range (r + 1), binomialTerm d m r i
  have triangle_succ (m : ℕ) : triangle (m + 1) = triangle m + m := by
    simp [triangle_def, Nat.choose, Nat.add_comm]
  have binomialTerm_zero (d : ℕ → Polynomial ℤ) (m r : ℕ) :
      binomialTerm d m r 0 = d m := by
    simp [binomialTerm, triangle_def]
  have binomialTerm_top_zero (d : ℕ → Polynomial ℤ) (m r : ℕ) :
      binomialTerm d m r (r + 1) = 0 := by
    simp [binomialTerm]
  have binomialTerm_succ (d : ℕ → Polynomial ℤ) (m r i : ℕ) (hi : i ≤ m) :
      binomialTerm d (m + 1) (r + 1) (i + 1) =
        binomialTerm d (m + 1) r (i + 1) + X ^ (m + 1) * binomialTerm d m r i := by
    simp only [binomialTerm, Nat.choose_succ_succ, Nat.cast_add, map_add, add_mul]
    have hexp :
        triangle (m + 1 + 1) - triangle (m + 1 - (i + 1) + 1) =
          (m + 1) + (triangle (m + 1) - triangle (m - i + 1)) := by
      have hindex : m + 1 - (i + 1) + 1 = m - i + 1 := by omega
      have hle : triangle (m - i + 1) ≤ triangle (m + 1) := by
        rw [triangle_def]
        exact Nat.choose_le_choose 2 (by omega)
      rw [hindex, triangle_succ]
      omega
    rw [hexp, Nat.succ_sub_succ_eq_sub, pow_add]
    ring
  have binomialTerm_shift_sum (d : ℕ → Polynomial ℤ) (m r : ℕ) :
      binomialTerm d m r 0 + ∑ i ∈ range (r + 1), binomialTerm d m r (i + 1) =
        ∑ i ∈ range (r + 1), binomialTerm d m r i := by
    rw [sum_range_succ, binomialTerm_top_zero, add_zero, sum_range_succ']
    ac_rfl
  have pascalRow_zero (d : ℕ → Polynomial ℤ) (m : ℕ) : pascalRow d m 0 = d m := by
    simp [pascalRow, binomialTerm_zero]
  have pascalRow_succ (d : ℕ → Polynomial ℤ) (m r : ℕ) (hr : r ≤ m) :
      pascalRow d (m + 1) (r + 1) =
        pascalRow d (m + 1) r + X ^ (m + 1) * pascalRow d m r := by
    simp only [pascalRow]
    rw [sum_range_succ', binomialTerm_zero]
    have hsplit :
        (∑ i ∈ range (r + 1), binomialTerm d (m + 1) (r + 1) (i + 1)) =
          ∑ i ∈ range (r + 1),
            (binomialTerm d (m + 1) r (i + 1) + X ^ (m + 1) * binomialTerm d m r i) := by
      apply sum_congr rfl
      intro i hi
      have hir : i < r + 1 := mem_range.mp hi
      rw [binomialTerm_succ d m r i (by omega)]
    rw [hsplit, sum_add_distrib, ← mul_sum]
    conv_rhs => lhs; rw [← binomialTerm_shift_sum d (m + 1) r]
    rw [binomialTerm_zero]
    ring
  have kurkovR_succ_zero (m : ℕ) : kurkovR (m + 1) 0 = diagonal (m + 1) := by
    simp [kurkovR, diagonal]
  have kurkovR_succ_succ (m r : ℕ) :
      kurkovR (m + 1) (r + 1) =
        kurkovR (m + 1) r + X ^ (m + 1) * kurkovR m r := by
    simp only [kurkovR, sum_range_succ]
    ring
  have main : kurkovR n k = pascalRow diagonal n k := by
    induction n generalizing k with
    | zero =>
        have : k = 0 := by omega
        subst k
        simp [kurkovR, pascalRow_zero, diagonal]
    | succ n ihn =>
        induction k with
        | zero => rw [kurkovR_succ_zero, pascalRow_zero]
        | succ k ihk =>
            rw [kurkovR_succ_succ, ihk (by omega), ihn k (by omega),
              pascalRow_succ diagonal n k (by omega)]
  simpa only [pascalRow, binomialTerm, triangle_def, diagonal] using main

/-- OEIS A126347 (Mikhail Kurkov, 2025): Kurkov's diagonal is the reversal
of the next q-Bell row polynomial. -/
theorem result (n : ℕ) : kurkovR n n = (qBell (n + 1)).reverse := by
  set triangle : ℕ → ℕ := fun m => m.choose 2 with triangle_def
  let diagonal : ℕ → Polynomial ℤ := fun m =>
    match m with
    | 0 => 1
    | r + 1 => kurkovR r r
  let binomialTerm : (ℕ → Polynomial ℤ) → ℕ → ℕ → ℕ → Polynomial ℤ := fun d m r i =>
    C (r.choose i : ℤ) *
      X ^ (triangle (m + 1) - triangle (m - i + 1)) * d (m - i)
  let pascalRow : (ℕ → Polynomial ℤ) → ℕ → ℕ → Polynomial ℤ := fun d m r =>
    ∑ i ∈ range (r + 1), binomialTerm d m r i
  let reflectedBell : ℕ → Polynomial ℤ := fun m => (qBell m).reflect (triangle m)
  have triangle_succ (m : ℕ) : triangle (m + 1) = triangle m + m := by
    simp [triangle_def, Nat.choose, Nat.add_comm]
  have qBell_succ (m : ℕ) :
      qBell (m + 1) =
        ∑ r ∈ range (m + 1), C (m.choose r : ℤ) * qBell r * X ^ r := by
    rw [qBell, Finset.sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro r hr
    simp [mem_range.mp hr]
  have qBell_natDegree (m : ℕ) : (qBell m).natDegree = triangle m := by
    rw [triangle_def]
    exact (qBell_monic_degree m).2
  have pascal_expansion (m r : ℕ) (hr : r ≤ m) :
      kurkovR m r = pascalRow diagonal m r := by
    simpa only [pascalRow, binomialTerm, triangle_def, diagonal] using
      kurkovR_pascal_expansion m r hr
  have reflect_sum (s : Finset ℕ) (f : ℕ → Polynomial ℤ) (N : ℕ) :
      (∑ i ∈ s, f i).reflect N = ∑ i ∈ s, (f i).reflect N := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, ih, reflect_add]
  have reflect_pad (p : Polynomial ℤ) (d N : ℕ)
      (hp : p.natDegree ≤ d) (hdN : d ≤ N) :
      p.reflect N = p.reflect d * X ^ (N - d) := by
    conv_lhs => rw [← Nat.add_sub_of_le hdN, ← mul_one p]
    rw [reflect_mul p 1 hp (by simp)]
    simp
  have reflect_qBell_term_tight (c : ℤ) (r : ℕ) :
      (C c * qBell r * X ^ r).reflect (triangle (r + 1)) =
        C c * reflectedBell r := by
    rw [triangle_succ]
    rw [reflect_mul (C c * qBell r) (X ^ r)
      ((natDegree_C_mul_le c (qBell r)).trans_eq (qBell_natDegree r)) (by simp)]
    rw [reflect_C_mul]
    simp [reflectedBell, reflect_monomial]
  have reflect_qBell_term (m r : ℕ) (hr : r ≤ m) :
      (C (m.choose r : ℤ) * qBell r * X ^ r).reflect (triangle (m + 1)) =
        C (m.choose r : ℤ) *
          X ^ (triangle (m + 1) - triangle (r + 1)) * reflectedBell r := by
    have hdegree :
        (C (m.choose r : ℤ) * qBell r * X ^ r).natDegree ≤ triangle (r + 1) := by
      calc
        (C (m.choose r : ℤ) * qBell r * X ^ r).natDegree
            ≤ (C (m.choose r : ℤ) * qBell r).natDegree +
                (X ^ r : Polynomial ℤ).natDegree := natDegree_mul_le
        _ ≤ triangle r + r := add_le_add
          ((natDegree_C_mul_le _ _).trans_eq (qBell_natDegree r)) (by simp)
        _ = triangle (r + 1) := (triangle_succ r).symm
    have htriangle : triangle (r + 1) ≤ triangle (m + 1) := by
      rw [triangle_def]
      exact Nat.choose_le_choose 2 (by omega)
    rw [reflect_pad _ _ _ hdegree htriangle, reflect_qBell_term_tight]
    ring
  have reflectedBell_succ (m : ℕ) :
      reflectedBell (m + 1) = pascalRow reflectedBell m m := by
    simp only [reflectedBell]
    rw [qBell_succ, reflect_sum]
    have hterms :
        (∑ r ∈ range (m + 1),
            (C (m.choose r : ℤ) * qBell r * X ^ r).reflect (triangle (m + 1))) =
          ∑ r ∈ range (m + 1),
            C (m.choose r : ℤ) *
              X ^ (triangle (m + 1) - triangle (r + 1)) * reflectedBell r := by
      apply sum_congr rfl
      intro r hr
      have hrm : r < m + 1 := mem_range.mp hr
      rw [reflect_qBell_term m r (by omega)]
    rw [hterms]
    simp only [pascalRow]
    rw [← sum_range_reflect (fun r =>
      C (m.choose r : ℤ) *
        X ^ (triangle (m + 1) - triangle (r + 1)) * reflectedBell r) (m + 1)]
    apply sum_congr rfl
    intro i hi
    have hiN : i < m + 1 := mem_range.mp hi
    have him : i ≤ m := by omega
    have hindex : m + 1 - 1 - i = m - i := by omega
    simp only [binomialTerm]
    rw [hindex, Nat.choose_symm him]
  have diagonal_eq_reflectedBell : ∀ m : ℕ, diagonal m = reflectedBell m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      cases m with
      | zero => simp [diagonal, reflectedBell, qBell, triangle_def]
      | succ m =>
        rw [show diagonal (m + 1) = kurkovR m m by rfl,
          pascal_expansion m m le_rfl, reflectedBell_succ]
        simp only [pascalRow]
        apply sum_congr rfl
        intro i hi
        simp only [binomialTerm]
        rw [ih (m - i) (by omega)]
  calc
    kurkovR n n = diagonal (n + 1) := rfl
    _ = reflectedBell (n + 1) := diagonal_eq_reflectedBell (n + 1)
    _ = (qBell (n + 1)).reverse := by
      simp [reflectedBell, reverse, qBell_natDegree]

end D5.S1.Words.KurkovReversedQBellRowPolynomial
