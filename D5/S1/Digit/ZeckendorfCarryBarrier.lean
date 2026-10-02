/- GID: D5/S1/Digit/ZeckendorfCarryBarrier
   generality: I
   mirror-B: none(waiver:canonical-support-bound)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: A high canonical Fibonacci support plus one high Fibonacci weight cannot carry below two positions beneath its lower boundary. -/

import D5.S1.Words.ZeckendorfBeattyBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ZeckendorfCarryBarrier

open D5.S0.Conventions
open D5.S1.Words

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

/-- This bound includes empty high supports and the boundary weight `j=m-1`.
The output support is the actual canonical support of the sum. -/
theorem lower_support_carry_barrier (P : List ℕ) (m j : ℕ)
    (hP : P.IsZeckendorfRep) (hm : 4 ≤ m)
    (hmin : ∀ k ∈ P, m ≤ k) (hj : m - 1 ≤ j) :
    ∀ k ∈ wdigits ((P.map Nat.fib).sum + Nat.fib j), m - 2 ≤ k := by
  classical
  let r : ℝ := Real.goldenRatio⁻¹
  let E : List ℕ → ℝ := fun l => (l.map (fun k => Real.goldenConj ^ k)).sum
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hr : r ^ 2 + r = 1 := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have hconj : Real.goldenConj = -r := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    ring
  have pair (l : List ℕ) (hl : l.IsZeckendorfRep) :
      l.Pairwise (fun x y => y + 2 ≤ x) :=
    (List.pairwise_append.mp (List.isChain_iff_pairwise.mp hl)).1
  have two (l : List ℕ) (hl : l.IsZeckendorfRep) (k : ℕ) (hk : k ∈ l) : 2 ≤ k :=
    (List.pairwise_append.mp (List.isChain_iff_pairwise.mp hl)).2.2 k hk 0 (by simp)
  have powers (l : List ℕ) (d : ℕ) (hp : l.Pairwise (fun x y => y + 2 ≤ x))
      (hl : ∀ k ∈ l, d + 1 ≤ k) : (l.map (fun k => r ^ k)).sum < r ^ d :=
    sum_powers_lt hr0 hr1 hr hp hl
  have nonneg (l : List ℕ) : 0 ≤ (l.map (fun k => r ^ k)).sum :=
    List.sum_nonneg (fun x hx => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      positivity)
  have split (l : List ℕ) : E l =
      ((l.filter (fun k => decide (Even k))).map (fun k => r ^ k)).sum -
        ((l.filter (fun k => decide (Odd k))).map (fun k => r ^ k)).sum := by
    dsimp [E]
    rw [hconj, sum_neg_powers_eq_even_sub_odd]
  have tail (l : List ℕ) (d : ℕ) (hp : l.Pairwise (fun x y => y + 2 ≤ x))
      (hl : ∀ k ∈ l, d + 1 ≤ k) : |E l| < r ^ d := by
    have he := powers (l.filter (fun k => decide (Even k))) d (hp.filter _) (by
      intro k hk; exact hl k (List.mem_filter.mp hk).1)
    have ho := powers (l.filter (fun k => decide (Odd k))) d (hp.filter _) (by
      intro k hk; exact hl k (List.mem_filter.mp hk).1)
    rw [split]
    exact abs_lt.mpr ⟨by linarith [nonneg (l.filter (fun k => decide (Even k)))],
      by linarith [nonneg (l.filter (fun k => decide (Odd k)))]⟩
  have recurrence (a : ℕ) (ha : 1 ≤ a) :
      r ^ a + r ^ (a + 1) = r ^ (a - 1) := pow_add_pow_succ hr ha
  have raw_small : |E P + Real.goldenConj ^ j| < r ^ (m - 2) := by
    by_cases hhigh : m ≤ j
    · have ep := tail P (m - 1) (pair P hP) (by intro k hk; have := hmin k hk; omega)
      have jp : |Real.goldenConj ^ j| ≤ r ^ m := by
        rw [hconj, abs_pow, abs_neg, abs_of_pos hr0]
        exact pow_le_pow_of_le_one hr0.le hr1.le hhigh
      have hrec : r ^ (m - 1) + r ^ m = r ^ (m - 2) := by
        have := recurrence (m - 1) (by omega)
        simpa [show m - 1 + 1 = m by omega, show m - 1 - 1 = m - 2 by omega] using this
      calc
        |E P + Real.goldenConj ^ j| ≤ |E P| + |Real.goldenConj ^ j| := abs_add_le _ _
        _ < r ^ (m - 1) + r ^ m := add_lt_add_of_lt_of_le ep jp
        _ = r ^ (m - 2) := hrec
    · have hjeq : j = m - 1 := by omega
      have hmj : m = j + 1 := by omega
      have hrec : r ^ j + r ^ (j + 1) = r ^ (m - 2) := by
        rw [recurrence j (by omega)]
        congr 1
        omega
      have e := powers (P.filter (fun k => decide (Even k))) j ((pair P hP).filter _) (by
        intro k hk; have := hmin k (List.mem_filter.mp hk).1; omega)
      have o := powers (P.filter (fun k => decide (Odd k))) j ((pair P hP).filter _) (by
        intro k hk; have := hmin k (List.mem_filter.mp hk).1; omega)
      rcases Nat.even_or_odd j with he | ho
      · have et := powers (P.filter (fun k => decide (Even k))) (j + 1)
          ((pair P hP).filter _) (by
            intro k hk
            have hkm := hmin k (List.mem_filter.mp hk).1
            have hke : Even k := by simpa using (List.mem_filter.mp hk).2
            rw [Nat.even_iff] at he hke
            omega)
        rw [split, hconj, he.neg_pow]
        rw [abs_of_pos (by linarith [nonneg (P.filter (fun k => decide (Even k)))])]
        linarith [nonneg (P.filter (fun k => decide (Odd k)))]
      · have ot := powers (P.filter (fun k => decide (Odd k))) (j + 1)
          ((pair P hP).filter _) (by
            intro k hk
            have hkm := hmin k (List.mem_filter.mp hk).1
            have hko : Odd k := by simpa using (List.mem_filter.mp hk).2
            rw [Nat.odd_iff] at ho hko
            omega)
        rw [split, hconj, ho.neg_pow]
        rw [abs_of_neg (by linarith [nonneg (P.filter (fun k => decide (Odd k)))])]
        linarith [nonneg (P.filter (fun k => decide (Even k)))]
  let N := (P.map Nat.fib).sum + Nat.fib j
  let S := wdigits N
  have hS : S.IsZeckendorfRep := wdigits_isCanonical N
  have raw_interval : -(r ^ 2) < E P + Real.goldenConj ^ j ∧
      E P + Real.goldenConj ^ j < r := by
    have hp : r ^ (m - 2) ≤ r ^ 2 := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    have hsq : r ^ 2 < r := by nlinarith
    have hs := abs_lt.mp raw_small
    constructor <;> linarith
  have same_error : E S = E P + Real.goldenConj ^ j := by
    let A := ((P ++ [j]).map (fun k => Nat.fib (k - 1))).sum
    let B := (S.map (fun k => Nat.fib (k - 1))).sum
    have sum_identity (l : List ℕ) (hl : ∀ k ∈ l, 2 ≤ k) :
        ((l.map Nat.fib).sum : ℝ) * r =
          ((l.map (fun k => Nat.fib (k - 1))).sum : ℝ) - E l := by
      have h := sum_fib_mul_inv_golden hl
      have hc : ((l.map Nat.fib).sum : ℝ) * r =
          (l.map (fun k => (Nat.fib k : ℝ) * r)).sum := by
        have hcast : ((l.map Nat.fib).sum : ℝ) =
            (l.map (fun k => (Nat.fib k : ℝ))).sum := by simp [Function.comp_def]
        rw [hcast, ← List.sum_map_mul_right]
      rw [hc]
      simpa [r, E, Function.comp_def] using h
    have hraw := sum_identity (P ++ [j]) (by
      intro k hk
      rcases List.mem_append.mp hk with hk | hk
      · have := hmin k hk; omega
      · simp only [List.mem_singleton] at hk; subst k; omega)
    have hcan := sum_identity S (two S hS)
    have hvalue : (S.map Nat.fib).sum = N := decode_wdigits N
    have hrawval : ((P ++ [j]).map Nat.fib).sum = N := by simp [N]
    have eraw : E (P ++ [j]) = E P + Real.goldenConj ^ j := by simp [E]
    rw [hrawval, eraw] at hraw
    rw [hvalue] at hcan
    change (N : ℝ) * r = (A : ℝ) - (E P + Real.goldenConj ^ j) at hraw
    change (N : ℝ) * r = (B : ℝ) - E S at hcan
    have interval := conjugate_error_bounds hS
    change -(r ^ 2) < E S ∧ E S < r at interval
    have hdiff1 : (B : ℝ) - (A : ℝ) < 1 := by linarith
    have hdiff2 : -1 < (B : ℝ) - (A : ℝ) := by linarith
    have hd1 : (B : ℤ) - (A : ℤ) < 1 := by exact_mod_cast hdiff1
    have hd2 : -1 < (B : ℤ) - (A : ℤ) := by exact_mod_cast hdiff2
    have heq : A = B := by omega
    rw [heq] at hraw
    linarith
  have least_large (l : List ℕ) (hl : l.IsZeckendorfRep) (hne : l ≠ []) :
      r ^ (l.getLast hne + 1) < |E l| := by
    let ell := l.getLast hne
    let pre := l.dropLast
    have hdecomp : pre ++ [ell] = l := List.dropLast_append_getLast hne
    have hgap := (pair l hl).sublist (List.dropLast_sublist l)
    have hlow : ∀ k ∈ pre, ell + 2 ≤ k :=
      fun k hk => (pair l hl).rel_dropLast_getLast hk
    have esum : E l = E pre + Real.goldenConj ^ ell := by rw [← hdecomp]; simp [E]
    have diff : r ^ ell - r ^ (ell + 2) = r ^ (ell + 1) := by
      calc
        r ^ ell - r ^ (ell + 2) = r ^ ell * (1 - r ^ 2) := by rw [pow_add]; ring
        _ = r ^ ell * r := by congr 1; linarith
        _ = r ^ (ell + 1) := (pow_succ r ell).symm
    rcases Nat.even_or_odd ell with he | ho
    · have opposite := powers (pre.filter (fun k => decide (Odd k))) (ell + 2)
        (hgap.filter _) (by
          intro k hk
          have hklo := hlow k (List.mem_filter.mp hk).1
          have hko : Odd k := by simpa using (List.mem_filter.mp hk).2
          rw [Nat.even_iff] at he
          rw [Nat.odd_iff] at hko
          omega)
      have hpositive : r ^ (ell + 1) < E l := by
        rw [esum, split, hconj, he.neg_pow]
        linarith [nonneg (pre.filter (fun k => decide (Even k)))]
      exact hpositive.trans_le (le_abs_self _)
    · have opposite := powers (pre.filter (fun k => decide (Even k))) (ell + 2)
        (hgap.filter _) (by
          intro k hk
          have hklo := hlow k (List.mem_filter.mp hk).1
          have hke : Even k := by simpa using (List.mem_filter.mp hk).2
          rw [Nat.odd_iff] at ho
          rw [Nat.even_iff] at hke
          omega)
      have hnegative : r ^ (ell + 1) < -E l := by
        rw [esum, split, hconj, ho.neg_pow]
        linarith [nonneg (pre.filter (fun k => decide (Odd k)))]
      exact hnegative.trans_le (neg_le_abs _)
  intro k hk
  change k ∈ S at hk
  have hne : S ≠ [] := by intro hs; rw [hs] at hk; exact List.not_mem_nil hk
  have large := least_large S hS hne
  have least_le : S.getLast hne ≤ k := by
    by_cases he : k = S.getLast hne
    · omega
    · have hkpre := List.mem_dropLast_of_mem_of_ne_getLast hk he
      have h := (pair S hS).rel_dropLast_getLast hkpre
      omega
  have hleast : m - 2 ≤ S.getLast hne := by
    by_contra hnot
    have hpower : r ^ (m - 2) ≤ r ^ (S.getLast hne + 1) :=
      pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    rw [same_error] at large
    linarith
  omega

#print axioms lower_support_carry_barrier

end D5.S1.Digit.ZeckendorfCarryBarrier
