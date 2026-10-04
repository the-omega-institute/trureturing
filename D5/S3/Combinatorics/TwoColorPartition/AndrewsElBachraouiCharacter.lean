/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiCharacter
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiCharacter
   mirror-E: none(waiver:alternating-divisor-hyperbola)
   anchors: []
   utility: none
   digest: A signed hyperbola decomposition bounds alternating odd divisor sums. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiCharacter

open Finset

/-- The odd signed divisor summatory function is bounded by the small odd factor count. -/
theorem alternating_odd_divisor_sum_bound (n : ℕ) :
    |∑ i ∈ range (n+1), (-1 : ℤ)^(n-i) * ((2*i+1).divisors.card : ℤ)| ≤
      (((Nat.sqrt (2*n+1) + 1) / 2 : ℕ) : ℤ) := by
  classical
  have hbound (M : ℕ) :
      |∑ d ∈ Ioc 0 M, ZMod.χ₄ (d : ZMod 4) * (d.divisors.card : ℤ)| ≤
        (((Nat.sqrt M + 1) / 2 : ℕ) : ℤ) := by
    classical
    let f : ArithmeticFunction ℤ := ⟨fun n => ZMod.χ₄ (n : ZMod 4), by decide⟩
    have hf (n : ℕ) : f n = ZMod.χ₄ (n : ZMod 4) := rfl
    have hconv (n : ℕ) : (f * f) n = ZMod.χ₄ (n : ZMod 4) * (n.divisors.card : ℤ) := by
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * f b)]
      calc
        _ = ∑ d ∈ n.divisors, ZMod.χ₄ (n : ZMod 4) := by
          apply sum_congr rfl
          intro d hd
          rw [hf, hf, ← map_mul, ← Nat.cast_mul,
            Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
        _ = _ := by simp [mul_comm]
    have hprefix (X : ℕ) : (∑ b ∈ Ioc 0 X, f b) = (((X + 1) / 2 % 2 : ℕ) : ℤ) := by
      induction X with
      | zero => simp
      | succ X ih =>
          rw [Finset.sum_Ioc_succ_top (by omega : 0 ≤ X), ih, hf,
            ZMod.χ₄_nat_eq_if_mod_four]
          have hX := Nat.mod_lt X (by decide : 0 < 4)
          interval_cases h : X % 4 <;> split_ifs <;> omega
    let s := Nat.sqrt M
    let L := Ioc 0 M
    let K := Ioc 0 s
    have hKL : K ⊆ L := Ioc_subset_Ioc (by omega) (Nat.sqrt_le_self M)
    have hs : s * s ≤ M := Nat.sqrt_le M
    have hcover (a b : ℕ) (hab : a * b ≤ M) : a ≤ s ∨ b ≤ s := by
      by_contra h
      have ha : s + 1 ≤ a := by omega
      have hb : s + 1 ≤ b := by omega
      have hp := Nat.mul_le_mul ha hb
      have hl := Nat.lt_succ_sqrt M
      dsimp [s] at *
      nlinarith
    have hsquare (a b : ℕ) (ha : a ∈ K) (hb : b ∈ K) : a * b ≤ M := by
      have := Nat.mul_le_mul (mem_Ioc.mp ha).2 (mem_Ioc.mp hb).2
      omega
    let A : ℤ := ∑ a ∈ K, f a * ∑ b ∈ Ioc 0 (M / a), f b
    have hhyper : (∑ d ∈ Ioc 0 M, (f * f) d) = 2 * A - (∑ a ∈ K, f a) ^ 2 := by
      rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter, sum_filter, sum_product]
      have hrestrict (g : ℕ → ℤ) :
          (∑ a ∈ L, if a ∈ K then g a else 0) = ∑ a ∈ K, g a := by
        rw [← sum_filter]
        congr 1
        ext a
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun h => hKL h)
      have hrow (a : ℕ) (ha : a ∈ L) :
          (∑ b ∈ L, if a*b ≤ M then f b else 0) = ∑ b ∈ Ioc 0 (M/a), f b := by
        rw [← sum_filter]
        congr 1
        ext b
        have ha0 : 0 < a := (mem_Ioc.mp ha).1
        have hdiv : b ≤ M/a ↔ a*b ≤ M := by
          rw [Nat.le_div_iff_mul_le ha0, Nat.mul_comm]
        have hle := Nat.div_le_self M a
        simp only [L, mem_filter, mem_Ioc]
        omega
      have hrectangle :
          (∑ a ∈ L, ∑ b ∈ L,
            if a ∈ K then if a*b ≤ M then f a*f b else 0 else 0) = A := by
        calc
          _ = ∑ a ∈ L, if a ∈ K then f a *
              ∑ b ∈ L, if a*b ≤ M then f b else 0 else 0 := by
            apply sum_congr rfl
            intro a _
            by_cases haK : a ∈ K
            · simp only [haK, if_true, mul_sum]
              apply sum_congr rfl
              intro b _
              split_ifs <;> simp
            · simp [haK]
          _ = ∑ a ∈ K, f a * ∑ b ∈ L, if a*b ≤ M then f b else 0 := hrestrict _
          _ = A := by
            apply sum_congr rfl
            intro a ha
            rw [hrow a (hKL ha)]
      have hsquareSum :
          (∑ a ∈ L, ∑ b ∈ L,
            if a ∈ K ∧ b ∈ K then f a*f b else 0) = (∑ a ∈ K, f a)^2 := by
        calc
          _ = ∑ a ∈ L, if a ∈ K then f a *
              ∑ b ∈ L, if b ∈ K then f b else 0 else 0 := by
            apply sum_congr rfl
            intro a _
            by_cases haK : a ∈ K
            · simp only [haK, true_and, if_true, mul_sum]
              apply sum_congr rfl
              intro b _
              split_ifs <;> simp
            · simp [haK]
          _ = _ := by rw [hrestrict, hrestrict, pow_two, sum_mul]
      have hpoint (a b : ℕ) (ha : a ∈ L) (hb : b ∈ L) :
          (if a*b ≤ M then f a*f b else 0) =
            ((if a ∈ K then if a*b ≤ M then f a*f b else 0 else 0) +
            (if b ∈ K then if a*b ≤ M then f a*f b else 0 else 0) -
            (if a ∈ K ∧ b ∈ K then f a*f b else 0)) := by
        by_cases hab : a*b ≤ M
        · have hc := hcover a b hab
          have ha0 : 0 < a := (mem_Ioc.mp ha).1
          have hb0 : 0 < b := (mem_Ioc.mp hb).1
          have hka : a ∈ K ↔ a ≤ s := by simp only [K, mem_Ioc]; omega
          have hkb : b ∈ K ↔ b ≤ s := by simp only [K, mem_Ioc]; omega
          by_cases haK : a ∈ K
          · by_cases hbK : b ∈ K <;> simp [hab, haK, hbK]
          · have hbK : b ∈ K := hkb.mpr (hc.resolve_left (by simpa [← hka] using haK))
            simp [hab, haK, hbK]
        · have hc : ¬(a ∈ K ∧ b ∈ K) := by intro h; exact hab (hsquare a b h.1 h.2)
          simp [hab, hc]
      change (∑ a ∈ L, ∑ b ∈ L, if a * b ≤ M then f a * f b else 0) = _
      calc
        _ = ∑ a ∈ L, ∑ b ∈ L,
            ((if a ∈ K then if a*b ≤ M then f a*f b else 0 else 0) +
            (if b ∈ K then if a*b ≤ M then f a*f b else 0 else 0) -
            (if a ∈ K ∧ b ∈ K then f a*f b else 0)) := by
          apply sum_congr rfl
          intro a ha
          apply sum_congr rfl
          intro b hb
          exact hpoint a b ha hb
        _ = _ := by
          simp_rw [sum_sub_distrib, sum_add_distrib]
          rw [hrectangle, hsquareSum]
          have hswap : (∑ a ∈ L, ∑ b ∈ L,
              if b ∈ K then if a*b ≤ M then f a*f b else 0 else 0) = A := by
            rw [sum_comm]
            simpa only [mul_comm] using hrectangle
          rw [hswap]
          ring
    have habsprefix (X : ℕ) : (∑ b ∈ Ioc 0 X, |f b|) = (((X+1)/2 : ℕ) : ℤ) := by
      induction X with
      | zero => simp
      | succ X ih =>
          rw [Finset.sum_Ioc_succ_top (by omega : 0 ≤ X), ih, hf,
            ZMod.χ₄_nat_eq_if_mod_four]
          have hX := Nat.mod_lt X (by decide : 0 < 4)
          interval_cases h : X % 4 <;> split_ifs <;> norm_num <;> omega
    have hterm (a : ℕ) :
        -|f a| + f a ≤ 2*(f a * ∑ b ∈ Ioc 0 (M/a), f b) ∧
          2*(f a * ∑ b ∈ Ioc 0 (M/a), f b) ≤ |f a| + f a := by
      rw [hprefix, hf, ZMod.χ₄_nat_eq_if_mod_four]
      have hmod := Nat.mod_lt ((M/a+1)/2) (by decide : 0 < 2)
      split_ifs <;> norm_num <;> omega
    have hlower := sum_le_sum (fun a (_ : a ∈ K) => (hterm a).1)
    have hupper := sum_le_sum (fun a (_ : a ∈ K) => (hterm a).2)
    simp only [sum_add_distrib, sum_neg_distrib, ← mul_sum] at hlower hupper
    change -(∑ a ∈ K, |f a|) + ∑ a ∈ K, f a ≤ 2*A at hlower
    change 2*A ≤ (∑ a ∈ K, |f a|) + ∑ a ∈ K, f a at hupper
    rw [habsprefix, hprefix] at hlower hupper
    simp_rw [← hconv]
    rw [hhyper]
    rw [show (∑ a ∈ K, f a) = (((s+1)/2%2 : ℕ):ℤ) from hprefix s]
    have hmod := Nat.mod_lt ((s+1)/2) (by decide : 0 < 2)
    have hdelta : (((s+1)/2%2 : ℕ) : ℤ)^2 = (((s+1)/2%2 : ℕ) : ℤ) := by
      have hnonneg := Nat.zero_le ((s+1)/2%2)
      interval_cases h : ((s+1)/2%2) <;> norm_num
    change |2*A - (((s+1)/2%2 : ℕ) : ℤ)^2| ≤ (((s+1)/2 : ℕ):ℤ)
    rw [abs_le]
    constructor <;> nlinarith [hdelta]
  
  have hbridge :
      (∑ d ∈ Ioc 0 (2*n+1), ZMod.χ₄ (d : ZMod 4) * (d.divisors.card : ℤ)) =
        ∑ i ∈ range (n+1), (-1 : ℤ)^i * ((2*i+1).divisors.card : ℤ) := by
    have hfilter :
        (∑ d ∈ (Ioc 0 (2*n+1)).filter (fun d => d%2=1),
          ZMod.χ₄ (d : ZMod 4) * (d.divisors.card : ℤ)) =
        ∑ d ∈ Ioc 0 (2*n+1), ZMod.χ₄ (d : ZMod 4) * (d.divisors.card : ℤ) := by
      apply sum_subset (filter_subset _ _)
      intro d hd he
      have hm := Nat.mod_lt d (by decide : 0 < 2)
      have hnot : d%2≠1 := by
        intro h
        exact he (mem_filter.mpr ⟨hd,h⟩)
      have hz : d%2=0 := by omega
      rw [ZMod.χ₄_nat_eq_if_mod_four, if_pos hz, zero_mul]
    rw [← hfilter]
    symm
    apply sum_bij (fun i _ => 2*i+1)
    · intro i hi
      simp only [mem_filter, mem_Ioc, mem_range] at *
      omega
    · intro i hi j hj hij
      omega
    · intro d hd
      simp only [mem_filter, mem_Ioc] at hd
      refine ⟨d/2, mem_range.mpr (by omega), ?_⟩
      omega
    · intro i hi
      rw [ZMod.χ₄_eq_neg_one_pow (by omega)]
      congr 2
      omega
  have hsign :
      (∑ i ∈ range (n+1), (-1 : ℤ)^(n-i) * ((2*i+1).divisors.card : ℤ)) =
        (-1 : ℤ)^n * ∑ i ∈ range (n+1), (-1 : ℤ)^i *
          ((2*i+1).divisors.card : ℤ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hiN : i ≤ n := by have := mem_range.mp hi; omega
    have hp : (-1 : ℤ)^(n-i) = (-1 : ℤ)^(n+i) := by
      rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n+i)]
      congr 1
      omega
    rw [hp, pow_add]
    ring
  rw [hsign, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, ← hbridge]
  exact hbound (2*n+1)

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiCharacter
