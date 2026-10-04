/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted
   mirror-E: none(waiver:weighted-divisor-hyperbola)
   anchors: []
   utility: none
   digest: Character hyperbolas bound weighted and parity divisor coefficients. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiCharacter
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiWeighted

open Finset

/-- The weighted alternating divisor sum has a nonnegative signed value and a square bound. -/
theorem weighted_alternating_odd_divisor_sum_bound (n : ℕ) :
    0 ≤ (-1:ℤ)^n * ∑ i ∈ range (n+1), (-1:ℤ)^(n-i) *
      ((n-i+1:ℕ):ℤ) * ((2*i+1).divisors.card:ℤ) ∧
    ((-1:ℤ)^n * ∑ i ∈ range (n+1), (-1:ℤ)^(n-i) *
      ((n-i+1:ℕ):ℤ) * ((2*i+1).divisors.card:ℤ)) ≤
      (((Nat.sqrt (2*n+3)+1)/2:ℕ):ℤ)^2 := by
  classical
  have hbound (M : ℕ) :
    0 ≤ ∑ d ∈ Ioc 0 M, ZMod.χ₄ (d : ZMod 4) *
      (d.divisors.card : ℤ) * ((M : ℤ) - d) ∧
    (∑ d ∈ Ioc 0 M, ZMod.χ₄ (d : ZMod 4) *
      (d.divisors.card : ℤ) * ((M : ℤ) - d)) ≤
      2 * (((Nat.sqrt M + 1) / 2 : ℕ) : ℤ)^2 := by
    classical
    let f : ArithmeticFunction ℤ := ⟨fun n => ZMod.χ₄ (n : ZMod 4), by decide⟩
    let g : ArithmeticFunction ℤ := ⟨fun n => (n : ℤ) * f n, by simp⟩
    have hf (n : ℕ) : f n = ZMod.χ₄ (n : ZMod 4) := rfl
    have hg (n : ℕ) : g n = (n : ℤ) * f n := rfl
    have hconv (n : ℕ) : (f * f) n = ZMod.χ₄ (n : ZMod 4) * (n.divisors.card : ℤ) := by
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * f b)]
      calc
        _ = ∑ d ∈ n.divisors, ZMod.χ₄ (n : ZMod 4) := by
          apply sum_congr rfl
          intro d hd
          rw [hf, hf, ← map_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
        _ = _ := by simp [mul_comm]
    have hgconv (n : ℕ) : (g*g) n = (n : ℤ)*(f*f) n := by
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun a b => g a*g b),
        ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a*f b),
        mul_sum]
      apply sum_congr rfl
      intro d hd
      simp only [hg]
      have h := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      have hc : (d : ℤ)*((n/d : ℕ):ℤ) = (n : ℤ) := by exact_mod_cast h
      calc
        _ = ((d:ℤ)*((n/d:ℕ):ℤ))*(f d*f (n/d)) := by ring
        _ = _ := by rw [hc]
    have hprefix (X : ℕ) : (∑ b ∈ Ioc 0 X, f b) = (((X + 1) / 2 % 2 : ℕ) : ℤ) := by
      induction X with
      | zero => simp
      | succ X ih =>
          rw [Finset.sum_Ioc_succ_top (by omega : 0 ≤ X), ih, hf,
            ZMod.χ₄_nat_eq_if_mod_four]
          have hX := Nat.mod_lt X (by decide : 0 < 4)
          interval_cases h : X % 4 <;> split_ifs <;> omega
    have hgprefix (X : ℕ) : (∑ b ∈ Ioc 0 X, g b) =
        if (X+1)/2%2=0 then -(((X+1)/2 : ℕ):ℤ) else (((X+1)/2 : ℕ):ℤ) := by
      induction X with
      | zero => simp
      | succ X ih =>
          rw [Finset.sum_Ioc_succ_top (by omega : 0 ≤ X), ih, hg, hf,
            ZMod.χ₄_nat_eq_if_mod_four]
          have hX := Nat.mod_lt X (by decide : 0 < 4)
          interval_cases h : X % 4 <;> split_ifs <;> norm_num <;> omega
    have habsprefix (X : ℕ) : (∑ b ∈ Ioc 0 X, (b:ℤ)*|f b|) =
        (((X+1)/2 : ℕ):ℤ)^2 := by
      induction X with
      | zero => simp
      | succ X ih =>
          rw [Finset.sum_Ioc_succ_top (by omega : 0 ≤ X), ih]
          by_cases he : X%2=0
          · have hv : |f (X+1)| = 1 := by
              rw [hf, ZMod.χ₄_nat_eq_if_mod_four]
              split_ifs <;> norm_num <;> omega
            have hnext : (X+1+1)/2 = (X+1)/2+1 := by omega
            have hx : X = 2*((X+1)/2) := by omega
            rw [hv, hnext]
            push_cast
            have hxc : (X:ℤ)=2*(((X+1)/2:ℕ):ℤ) := by exact_mod_cast hx
            nlinarith
          · have hv : |f (X+1)| = 0 := by
              rw [hf, ZMod.χ₄_nat_eq_if_mod_four]
              split_ifs <;> norm_num <;> omega
            have hnext : (X+1+1)/2 = (X+1)/2 := by omega
            rw [hv, hnext]
            simp
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
    have hhyper (u : ArithmeticFunction ℤ) : (∑ d ∈ Ioc 0 M, (u * u) d) =
        2 * (∑ a ∈ K, u a * ∑ b ∈ Ioc 0 (M/a), u b) - (∑ a ∈ K, u a)^2 := by
      rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter, sum_filter, sum_product]
      have hrestrict (g : ℕ → ℤ) :
          (∑ a ∈ L, if a ∈ K then g a else 0) = ∑ a ∈ K, g a := by
        rw [← sum_filter]
        congr 1
        ext a
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun h => hKL h)
      have hrow (a : ℕ) (ha : a ∈ L) :
          (∑ b ∈ L, if a*b ≤ M then u b else 0) = ∑ b ∈ Ioc 0 (M/a), u b := by
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
            if a ∈ K then if a*b ≤ M then u a*u b else 0 else 0) =
          (∑ a ∈ K, u a * ∑ b ∈ Ioc 0 (M/a), u b) := by
        calc
          _ = ∑ a ∈ L, if a ∈ K then u a *
              ∑ b ∈ L, if a*b ≤ M then u b else 0 else 0 := by
            apply sum_congr rfl
            intro a _
            by_cases haK : a ∈ K
            · simp only [haK, if_true, mul_sum]
              apply sum_congr rfl
              intro b _
              split_ifs <;> simp
            · simp [haK]
          _ = ∑ a ∈ K, u a * ∑ b ∈ L, if a*b ≤ M then u b else 0 := hrestrict _
          _ = (∑ a ∈ K, u a * ∑ b ∈ Ioc 0 (M/a), u b) := by
            apply sum_congr rfl
            intro a ha
            rw [hrow a (hKL ha)]
      have hsquareSum :
          (∑ a ∈ L, ∑ b ∈ L,
            if a ∈ K ∧ b ∈ K then u a*u b else 0) = (∑ a ∈ K, u a)^2 := by
        calc
          _ = ∑ a ∈ L, if a ∈ K then u a *
              ∑ b ∈ L, if b ∈ K then u b else 0 else 0 := by
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
          (if a*b ≤ M then u a*u b else 0) =
            ((if a ∈ K then if a*b ≤ M then u a*u b else 0 else 0) +
            (if b ∈ K then if a*b ≤ M then u a*u b else 0 else 0) -
            (if a ∈ K ∧ b ∈ K then u a*u b else 0)) := by
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
      change (∑ a ∈ L, ∑ b ∈ L, if a * b ≤ M then u a * u b else 0) = _
      calc
        _ = ∑ a ∈ L, ∑ b ∈ L,
            ((if a ∈ K then if a*b ≤ M then u a*u b else 0 else 0) +
            (if b ∈ K then if a*b ≤ M then u a*u b else 0 else 0) -
            (if a ∈ K ∧ b ∈ K then u a*u b else 0)) := by
          apply sum_congr rfl
          intro a ha
          apply sum_congr rfl
          intro b hb
          exact hpoint a b ha hb
        _ = _ := by
          simp_rw [sum_sub_distrib, sum_add_distrib]
          rw [hrectangle, hsquareSum]
          have hswap : (∑ a ∈ L, ∑ b ∈ L,
              if b ∈ K then if a*b ≤ M then u a*u b else 0 else 0) =
          (∑ a ∈ K, u a * ∑ b ∈ Ioc 0 (M/a), u b) := by
            rw [sum_comm]
            simpa only [mul_comm] using hrectangle
          rw [hswap]
          ring
    let J (a : ℕ) : ℤ := (M:ℤ)*(∑ b ∈ Ioc 0 (M/a), f b) -
      (a:ℤ)*(∑ b ∈ Ioc 0 (M/a), g b)
    have hcenter (a : ℕ) (ha : 0 < a) :
        - (a:ℤ) ≤ 2*J a - M ∧ 2*J a - M ≤ a := by
      have hlo := Nat.div_mul_le_self M a
      have hhi := Nat.lt_mul_div_succ M ha
      have hr0 : M/a ≤ 2*((M/a+1)/2) := by omega
      have hr1 : 2*((M/a+1)/2) ≤ M/a+1 := by omega
      have hlow : (M:ℤ)-(a:ℤ) ≤ 2*(a:ℤ)*(((M/a+1)/2:ℕ):ℤ) := by
        have h := Nat.mul_le_mul_left a hr0
        have hh : (M:ℤ) < (a:ℤ)*(((M/a:ℕ):ℤ)+1) := by exact_mod_cast hhi
        have hl : (a:ℤ)*((M/a:ℕ):ℤ) ≤ (a:ℤ)*(2*(((M/a+1)/2:ℕ):ℤ)) := by
          exact_mod_cast h
        nlinarith
      have hupp : 2*(a:ℤ)*(((M/a+1)/2:ℕ):ℤ) ≤ (M:ℤ)+(a:ℤ) := by
        have h := Nat.mul_le_mul_left a hr1
        have hh : (a:ℤ)*((M/a:ℕ):ℤ) ≤ (M:ℤ) := by
          exact_mod_cast (by simpa [Nat.mul_comm] using hlo)
        have hl : (a:ℤ)*(2*(((M/a+1)/2:ℕ):ℤ)) ≤
            (a:ℤ)*(((M/a:ℕ):ℤ)+1) := by exact_mod_cast h
        nlinarith
      dsimp [J]
      rw [hprefix, hgprefix]
      have hm := Nat.mod_lt ((M/a+1)/2) (by decide : 0 < 2)
      split_ifs with he
      · rw [he]
        simp only [Nat.cast_zero, mul_zero]
        constructor <;> nlinarith
      · have hd : (M/a+1)/2%2=1 := by omega
        rw [hd]
        simp only [Nat.cast_one, mul_one]
        constructor <;> nlinarith
    have hterm (a : ℕ) (ha : a ∈ K) :
        -(a:ℤ)*|f a| ≤ f a*(2*J a-M) ∧ f a*(2*J a-M) ≤ (a:ℤ)*|f a| := by
      have hc := hcenter a (mem_Ioc.mp ha).1
      rw [hf, ZMod.χ₄_nat_eq_if_mod_four]
      split_ifs <;> norm_num <;> constructor <;> nlinarith
    have hlower := sum_le_sum (fun a (ha : a ∈ K) => (hterm a ha).1)
    have hupper := sum_le_sum (fun a (ha : a ∈ K) => (hterm a ha).2)
    have hneg : (∑ a ∈ K, -(a:ℤ)*|f a|) = -(∑ a ∈ K, (a:ℤ)*|f a|) := by
      simp [neg_mul, sum_neg_distrib]
    rw [hneg, habsprefix] at hlower
    rw [habsprefix] at hupper
    have hF : (∑ d ∈ Ioc 0 M, ZMod.χ₄ (d : ZMod 4) *
        (d.divisors.card : ℤ) * ((M:ℤ)-d)) =
        (((s+1)/2:ℕ):ℤ)^2 + ∑ a ∈ K, f a*(2*J a-M) := by
      calc
        _ = (M:ℤ)*(∑ d ∈ Ioc 0 M, (f*f) d) - ∑ d ∈ Ioc 0 M, (g*g) d := by
          rw [mul_sum, ← sum_sub_distrib]
          apply sum_congr rfl
          intro d _
          rw [hgconv, hconv]
          ring
        _ = _ := by
          rw [hhyper f, hhyper g, hprefix s, hgprefix s]
          have hdelta : (((s+1)/2%2:ℕ):ℤ)^2 = (((s+1)/2%2:ℕ):ℤ) := by
            have hmod := Nat.mod_lt ((s+1)/2) (by decide : 0 < 2)
            interval_cases h : (s+1)/2%2 <;> norm_num
          have hgsquare : (if (s+1)/2%2=0 then -(((s+1)/2:ℕ):ℤ)
              else (((s+1)/2:ℕ):ℤ))^2 = (((s+1)/2:ℕ):ℤ)^2 := by
            split_ifs <;> ring
          rw [hdelta, hgsquare]
          have hsum : (∑ a ∈ K, f a*(2*J a-M)) =
              2*(M:ℤ)*(∑ a ∈ K, f a*∑ b ∈ Ioc 0 (M/a), f b) -
              2*(∑ a ∈ K, g a*∑ b ∈ Ioc 0 (M/a), g b) -
              (M:ℤ)*∑ a ∈ K, f a := by
            rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
            apply sum_congr rfl
            intro a _
            dsimp [J]
            rw [hg]
            ring
          rw [hsum, hprefix s]
          ring
    rw [hF]
    change -(↑((s+1)/2):ℤ)^2 ≤ ∑ a ∈ K, f a*(2*J a-M) at hlower
    change (∑ a ∈ K, f a*(2*J a-M)) ≤ (↑((s+1)/2):ℤ)^2 at hupper
    constructor <;> nlinarith
  have hbridge : (∑ d ∈ Ioc 0 (2*n+3), ZMod.χ₄ (d:ZMod 4) *
      (d.divisors.card:ℤ) * (((2*n+3:ℕ):ℤ)-d)) =
      2 * ∑ i ∈ range (n+1), (-1:ℤ)^i *
        ((n-i+1:ℕ):ℤ) * ((2*i+1).divisors.card:ℤ) := by
    have hfilter :
        (∑ d ∈ (Ioc 0 (2*n+3)).filter (fun d => d%2=1),
          ZMod.χ₄ (d:ZMod 4) * (d.divisors.card:ℤ) * (((2*n+3:ℕ):ℤ)-d)) =
        ∑ d ∈ Ioc 0 (2*n+3), ZMod.χ₄ (d:ZMod 4) *
          (d.divisors.card:ℤ) * (((2*n+3:ℕ):ℤ)-d) := by
      apply sum_subset (filter_subset _ _)
      intro d hd he
      have hm := Nat.mod_lt d (by decide : 0 < 2)
      have hnot : d%2≠1 := by
        intro h
        exact he (mem_filter.mpr ⟨hd,h⟩)
      have hz : d%2=0 := by omega
      rw [ZMod.χ₄_nat_eq_if_mod_four, if_pos hz, zero_mul, zero_mul]
    have hreindex : (∑ d ∈ (Ioc 0 (2*n+3)).filter (fun d => d%2=1),
        ZMod.χ₄ (d:ZMod 4) * (d.divisors.card:ℤ) * (((2*n+3:ℕ):ℤ)-d)) =
        ∑ i ∈ range (n+2), (-1:ℤ)^i * ((2*i+1).divisors.card:ℤ) *
          ((((2*n+3:ℕ):ℤ))-((2*i+1:ℕ):ℤ)) := by
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
        have he : (2*i+1)/2=i := by omega
        rw [he]
    rw [← hfilter, hreindex, show n+2=(n+1)+1 by omega, sum_range_succ]
    have hend : ((2*n+3:ℕ):ℤ)-((2*(n+1)+1:ℕ):ℤ)=0 := by push_cast; ring
    rw [hend, mul_zero, add_zero, mul_sum]
    apply sum_congr rfl
    intro i hi
    have hiN : i ≤ n := by have := mem_range.mp hi; omega
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
      Nat.cast_sub hiN]
    ring
  have hsign :
      (-1:ℤ)^n * (∑ i ∈ range (n+1), (-1:ℤ)^(n-i) *
        ((n-i+1:ℕ):ℤ) * ((2*i+1).divisors.card:ℤ)) =
      ∑ i ∈ range (n+1), (-1:ℤ)^i *
        ((n-i+1:ℕ):ℤ) * ((2*i+1).divisors.card:ℤ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hiN : i ≤ n := by have := mem_range.mp hi; omega
    have hp : (-1:ℤ)^n * (-1:ℤ)^(n-i) = (-1:ℤ)^i := by
      rw [← pow_add, neg_one_pow_eq_pow_mod_two,
        neg_one_pow_eq_pow_mod_two i]
      congr 1
      omega
    calc
      _ = ((-1:ℤ)^n * (-1:ℤ)^(n-i)) *
          ((n-i+1:ℕ):ℤ) * ((2*i+1).divisors.card:ℤ) := by ring
      _ = _ := by rw [hp]
  have hb := hbound (2*n+3)
  rw [hbridge] at hb
  rw [hsign]
  constructor <;> nlinarith [hb.1, hb.2]

/-- The parity-restricted alternating divisor sum obeys a square-root bound. -/
theorem parity_alternating_odd_divisor_sum_bound (n : ℕ) :
    |∑ i ∈ (range (n+1)).filter (fun i => i%2=n%2),
      (-1:ℤ)^((n-i)/2) * ((2*i+1).divisors.card:ℤ)| ≤
      (Nat.sqrt (2*n+1):ℤ)+2 := by
  classical
  letI : Fact (1 < (8:ℕ)) := ⟨by decide⟩
  let u (c : MulChar (ZMod 8) ℤ) : ArithmeticFunction ℤ :=
    ⟨fun n => c (n:ZMod 8), by simpa using c.map_zero⟩
  have hu (c : MulChar (ZMod 8) ℤ) (n : ℕ) : u c n = c (n:ZMod 8) := rfl
  have hconv (c : MulChar (ZMod 8) ℤ) (n : ℕ) :
      (u c*u c) n = c (n:ZMod 8)*(n.divisors.card:ℤ) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => u c a*u c b)]
    calc
      _ = ∑ d ∈ n.divisors, c (n:ZMod 8) := by
        apply sum_congr rfl
        intro d hd
        rw [hu,hu,← map_mul,← Nat.cast_mul,
          Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      _ = _ := by simp [mul_comm]
  have habs (c : MulChar (ZMod 8) ℤ) (hc : c=ZMod.χ₈ ∨ c=ZMod.χ₈') (X : ℕ) :
      (∑ b ∈ Ioc 0 X, |u c b|) = (((X+1)/2:ℕ):ℤ) := by
    induction X with
    | zero => simp
    | succ X ih =>
        rw [sum_Ioc_succ_top (by omega : 0≤X), ih, hu]
        rcases hc with rfl | rfl
        · rw [ZMod.χ₈_nat_eq_if_mod_eight]
          split_ifs <;> norm_num <;> omega
        · rw [ZMod.χ₈'_nat_eq_if_mod_eight]
          split_ifs <;> norm_num <;> omega
  have hp8 (X : ℕ) : (∑ b ∈ Ioc 0 X, u ZMod.χ₈ b) =
      if (X+1)/2%4=1 then 1 else if (X+1)/2%4=3 then -1 else 0 := by
    induction X with
    | zero => simp
    | succ X ih =>
        rw [sum_Ioc_succ_top (by omega : 0≤X), ih, hu,
          ZMod.χ₈_nat_eq_if_mod_eight]
        have hX := Nat.mod_lt X (by decide : 0<8)
        have h0 : (X+1)/2%4=(X%8+1)/2%4 := by omega
        have h1 : (X+1+1)/2%4=(X%8+2)/2%4 := by omega
        have h2 : (X+1)%2=(X%8+1)%2 := by omega
        have h3 : (X+1)%8=(X%8+1)%8 := by omega
        rw [h0,h1,h2,h3]
        interval_cases h : X%8 <;> norm_num
  have hp8' (X : ℕ) : (∑ b ∈ Ioc 0 X, u ZMod.χ₈' b) =
      if (X+1)/2%4=0 then 0 else if (X+1)/2%4=2 then 2 else 1 := by
    induction X with
    | zero => simp
    | succ X ih =>
        rw [sum_Ioc_succ_top (by omega : 0≤X), ih, hu,
          ZMod.χ₈'_nat_eq_if_mod_eight]
        have hX := Nat.mod_lt X (by decide : 0<8)
        have h0 : (X+1)/2%4=(X%8+1)/2%4 := by omega
        have h1 : (X+1+1)/2%4=(X%8+2)/2%4 := by omega
        have h2 : (X+1)%2=(X%8+1)%2 := by omega
        have h3 : (X+1)%8=(X%8+1)%8 := by omega
        rw [h0,h1,h2,h3]
        interval_cases h : X%8 <;> norm_num
  have hbound (M : ℕ) (q : ArithmeticFunction ℤ) (mode : Bool)
      (ha : ∀ X, (∑ b ∈ Ioc 0 X, |q b|) = (((X+1)/2:ℕ):ℤ))
      (hp : ∀ X, if mode then
        0 ≤ ∑ b ∈ Ioc 0 X, q b ∧ (∑ b ∈ Ioc 0 X, q b) ≤ 2
        else |∑ b ∈ Ioc 0 X, q b| ≤ 1) :
      |∑ d ∈ Ioc 0 M, (q*q) d| ≤ 2*(((Nat.sqrt M+1)/2:ℕ):ℤ)+1 := by
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
    have hhyper (u : ArithmeticFunction ℤ) : (∑ d ∈ Ioc 0 M, (u * u) d) =
        2 * (∑ a ∈ K, u a * ∑ b ∈ Ioc 0 (M/a), u b) - (∑ a ∈ K, u a)^2 := by
      rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter, sum_filter, sum_product]
      have hrestrict (g : ℕ → ℤ) :
          (∑ a ∈ L, if a ∈ K then g a else 0) = ∑ a ∈ K, g a := by
        rw [← sum_filter]
        congr 1
        ext a
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun h => hKL h)
      have hrow (a : ℕ) (ha : a ∈ L) :
          (∑ b ∈ L, if a*b ≤ M then u b else 0) = ∑ b ∈ Ioc 0 (M/a), u b := by
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
            if a ∈ K then if a*b ≤ M then u a*u b else 0 else 0) =
          (∑ a ∈ K, u a * ∑ b ∈ Ioc 0 (M/a), u b) := by
        calc
          _ = ∑ a ∈ L, if a ∈ K then u a *
              ∑ b ∈ L, if a*b ≤ M then u b else 0 else 0 := by
            apply sum_congr rfl
            intro a _
            by_cases haK : a ∈ K
            · simp only [haK, if_true, mul_sum]
              apply sum_congr rfl
              intro b _
              split_ifs <;> simp
            · simp [haK]
          _ = ∑ a ∈ K, u a * ∑ b ∈ L, if a*b ≤ M then u b else 0 := hrestrict _
          _ = (∑ a ∈ K, u a * ∑ b ∈ Ioc 0 (M/a), u b) := by
            apply sum_congr rfl
            intro a ha
            rw [hrow a (hKL ha)]
      have hsquareSum :
          (∑ a ∈ L, ∑ b ∈ L,
            if a ∈ K ∧ b ∈ K then u a*u b else 0) = (∑ a ∈ K, u a)^2 := by
        calc
          _ = ∑ a ∈ L, if a ∈ K then u a *
              ∑ b ∈ L, if b ∈ K then u b else 0 else 0 := by
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
          (if a*b ≤ M then u a*u b else 0) =
            ((if a ∈ K then if a*b ≤ M then u a*u b else 0 else 0) +
            (if b ∈ K then if a*b ≤ M then u a*u b else 0 else 0) -
            (if a ∈ K ∧ b ∈ K then u a*u b else 0)) := by
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
      change (∑ a ∈ L, ∑ b ∈ L, if a * b ≤ M then u a * u b else 0) = _
      calc
        _ = ∑ a ∈ L, ∑ b ∈ L,
            ((if a ∈ K then if a*b ≤ M then u a*u b else 0 else 0) +
            (if b ∈ K then if a*b ≤ M then u a*u b else 0 else 0) -
            (if a ∈ K ∧ b ∈ K then u a*u b else 0)) := by
          apply sum_congr rfl
          intro a ha
          apply sum_congr rfl
          intro b hb
          exact hpoint a b ha hb
        _ = _ := by
          simp_rw [sum_sub_distrib, sum_add_distrib]
          rw [hrectangle, hsquareSum]
          have hswap : (∑ a ∈ L, ∑ b ∈ L,
              if b ∈ K then if a*b ≤ M then u a*u b else 0 else 0) =
          (∑ a ∈ K, u a * ∑ b ∈ Ioc 0 (M/a), u b) := by
            rw [sum_comm]
            simpa only [mul_comm] using hrectangle
          rw [hswap]
          ring

    let A : ℤ := ∑ a ∈ K, q a * ∑ b ∈ Ioc 0 (M/a), q b
    have hh := hhyper q
    change (∑ d ∈ Ioc 0 M, (q*q) d)=2*A-(∑ a ∈ K,q a)^2 at hh
    rw [hh]
    cases mode with
    | false =>
        simp only [Bool.false_eq_true, if_false] at hp
        have hterm (a : ℕ) : |q a*∑ b ∈ Ioc 0 (M/a),q b| ≤ |q a| := by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hp (M/a))
        have hA : |A| ≤ (((s+1)/2:ℕ):ℤ) := by
          calc
            _ ≤ ∑ a ∈ K, |q a*∑ b ∈ Ioc 0 (M/a),q b| := abs_sum_le_sum_abs _ _
            _ ≤ ∑ a ∈ K, |q a| := sum_le_sum (fun a _ => hterm a)
            _ = _ := ha s
        have hB := hp s
        rw [abs_le] at hA hB ⊢
        constructor <;> nlinarith [sq_nonneg (∑ a ∈ K,q a)]
    | true =>
        simp only [if_true] at hp
        have hterm (a : ℕ) :
            -2*|q a|+2*q a ≤ 2*(q a*∑ b ∈ Ioc 0 (M/a),q b) ∧
            2*(q a*∑ b ∈ Ioc 0 (M/a),q b) ≤ 2*|q a|+2*q a := by
          have hP := hp (M/a)
          by_cases hq : 0≤q a
          · rw [abs_of_nonneg hq]
            have h0 := mul_nonneg hq hP.1
            have h2 := mul_nonneg hq (sub_nonneg.mpr hP.2)
            constructor <;> nlinarith
          · have hqn : q a≤0 := by omega
            rw [abs_of_nonpos hqn]
            have h0 := mul_nonpos_of_nonpos_of_nonneg hqn hP.1
            have h2 := mul_nonpos_of_nonpos_of_nonneg hqn (sub_nonneg.mpr hP.2)
            constructor <;> nlinarith
        have hlo := sum_le_sum (fun a (_:a∈K) => (hterm a).1)
        have hhi := sum_le_sum (fun a (_:a∈K) => (hterm a).2)
        simp only [sum_add_distrib, ← mul_sum] at hlo hhi
        rw [ha s] at hlo hhi
        change -2*(((s+1)/2:ℕ):ℤ)+2*(∑a∈K,q a) ≤ 2*A at hlo
        change 2*A ≤ 2*(((s+1)/2:ℕ):ℤ)+2*(∑a∈K,q a) at hhi
        have hB := hp s
        change 0≤(∑a∈K,q a) ∧ (∑a∈K,q a)≤2 at hB
        have hcases : (∑a∈K,q a)=0 ∨ (∑a∈K,q a)=1 ∨ (∑a∈K,q a)=2 := by omega
        have hc : 0≤2*(∑a∈K,q a)-(∑a∈K,q a)^2 ∧
            2*(∑a∈K,q a)-(∑a∈K,q a)^2≤1 := by
          rcases hcases with h | h | h <;> rw [h] <;> norm_num
        rw [abs_le]
        constructor <;> nlinarith [hc.1,hc.2]
  have hb8 : |∑d∈Ioc 0 (2*n+1),ZMod.χ₈ (d:ZMod 8)*(d.divisors.card:ℤ)| ≤
      2*(((Nat.sqrt (2*n+1)+1)/2:ℕ):ℤ)+1 := by
    simpa only [hconv] using hbound (2*n+1) (u ZMod.χ₈) false
      (habs _ (Or.inl rfl)) (by
        intro X
        simp only [Bool.false_eq_true, if_false]
        rw [hp8]
        split_ifs <;> norm_num)
  have hb8' : |∑d∈Ioc 0 (2*n+1),ZMod.χ₈' (d:ZMod 8)*(d.divisors.card:ℤ)| ≤
      2*(((Nat.sqrt (2*n+1)+1)/2:ℕ):ℤ)+1 := by
    simpa only [hconv] using hbound (2*n+1) (u ZMod.χ₈') true
      (habs _ (Or.inr rfl)) (by
        intro X
        simp only [if_true]
        rw [hp8']
        split_ifs <;> norm_num)
  have hreindex (c : MulChar (ZMod 8) ℤ)
      (hz : ∀ (d:ℕ), d%2=0 → c (d:ZMod 8)=0) :
      (∑d∈Ioc 0 (2*n+1),c (d:ZMod 8)*(d.divisors.card:ℤ)) =
      ∑i∈range (n+1),c ((2*i+1:ℕ):ZMod 8)*((2*i+1).divisors.card:ℤ) := by
    have hfilter :
        (∑d∈(Ioc 0 (2*n+1)).filter (fun d => d%2=1),
          c (d:ZMod 8)*(d.divisors.card:ℤ)) =
        ∑d∈Ioc 0 (2*n+1),c (d:ZMod 8)*(d.divisors.card:ℤ) := by
      apply sum_subset (filter_subset _ _)
      intro d hd he
      have hm := Nat.mod_lt d (by decide : 0<2)
      have hnot : d%2≠1 := by
        intro h
        exact he (mem_filter.mpr ⟨hd,h⟩)
      rw [hz d (by omega),zero_mul]
    rw [← hfilter]
    symm
    apply sum_bij (fun i _ => 2*i+1)
    · intro i hi
      simp only [mem_filter,mem_Ioc,mem_range] at *
      omega
    · intro i hi j hj hij
      omega
    · intro d hd
      simp only [mem_filter,mem_Ioc] at hd
      refine ⟨d/2,mem_range.mpr (by omega),?_⟩
      omega
    · intro i _
      rfl
  have hz8 (d : ℕ) (h : d%2=0) : ZMod.χ₈ (d:ZMod 8)=0 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight,if_pos h]
  have hz8' (d : ℕ) (h : d%2=0) : ZMod.χ₈' (d:ZMod 8)=0 := by
    rw [ZMod.χ₈'_nat_eq_if_mod_eight,if_pos h]
  have hbridge :
      2*(∑i∈(range (n+1)).filter (fun i => i%2=n%2),
        (-1:ℤ)^((n-i)/2)*((2*i+1).divisors.card:ℤ)) =
      (-1:ℤ)^(n/2)*((∑d∈Ioc 0 (2*n+1),ZMod.χ₈' (d:ZMod 8)*(d.divisors.card:ℤ)) +
        (-1:ℤ)^n*(∑d∈Ioc 0 (2*n+1),ZMod.χ₈ (d:ZMod 8)*(d.divisors.card:ℤ))) := by
    rw [hreindex _ hz8',hreindex _ hz8]
    simp only [sum_filter,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hiN : i≤n := by have := mem_range.mp hi; omega
    have hs : 2*(if i%2=n%2 then (-1:ℤ)^((n-i)/2) else 0) =
        (-1:ℤ)^(n/2)*(ZMod.χ₈' ((2*i+1:ℕ):ZMod 8)+
          (-1:ℤ)^n*ZMod.χ₈ ((2*i+1:ℕ):ZMod 8)) := by
      have hodd : (2*i+1)%2≠0 := by omega
      rw [ZMod.χ₈'_nat_eq_if_mod_eight,ZMod.χ₈_nat_eq_if_mod_eight,
        if_neg hodd,if_neg hodd,
        neg_one_pow_eq_pow_mod_two ((n-i)/2),neg_one_pow_eq_pow_mod_two (n/2),
        neg_one_pow_eq_pow_mod_two n]
      have himod : (2*i+1)%8=2*(i%4)+1 := by omega
      have hnq : n/2%2=n%4/2 := by omega
      have hnp : n%2=n%4%2 := by omega
      have hip : i%2=i%4%2 := by omega
      rw [himod,hnq,hnp,hip]
      have hn := Nat.mod_lt n (by decide : 0<4)
      have hh := Nat.mod_lt i (by decide : 0<4)
      interval_cases hni : n%4 <;> interval_cases hii : i%4 <;> norm_num
      all_goals have hd : (n-i)/2%2=0 ∨ (n-i)/2%2=1 := by omega
      all_goals rcases hd with hd | hd <;> rw [hd] <;> norm_num <;> omega
    calc
      _ = (2*(if i%2=n%2 then (-1:ℤ)^((n-i)/2) else 0))*
          ((2*i+1).divisors.card:ℤ) := by split_ifs <;> ring
      _ = _ := by rw [hs]; ring
  have hsum :
      |(∑d∈Ioc 0 (2*n+1),ZMod.χ₈' (d:ZMod 8)*(d.divisors.card:ℤ))+
        (-1:ℤ)^n*(∑d∈Ioc 0 (2*n+1),ZMod.χ₈ (d:ZMod 8)*(d.divisors.card:ℤ))| ≤
      2*(2*(((Nat.sqrt (2*n+1)+1)/2:ℕ):ℤ)+1) := by
    calc
      _ ≤ |∑d∈Ioc 0 (2*n+1),ZMod.χ₈' (d:ZMod 8)*(d.divisors.card:ℤ)|+
          |(-1:ℤ)^n*(∑d∈Ioc 0 (2*n+1),ZMod.χ₈ (d:ZMod 8)*(d.divisors.card:ℤ))| :=
        abs_add_le _ _
      _ = |∑d∈Ioc 0 (2*n+1),ZMod.χ₈' (d:ZMod 8)*(d.divisors.card:ℤ)|+
          |∑d∈Ioc 0 (2*n+1),ZMod.χ₈ (d:ZMod 8)*(d.divisors.card:ℤ)| := by
        rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      _ ≤ _ := by linarith
  have hab := congrArg abs hbridge
  rw [abs_mul,abs_of_nonneg (by decide : 0≤(2:ℤ)),
    abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] at hab
  have hsqrt : 2*(((Nat.sqrt (2*n+1)+1)/2:ℕ):ℤ)+1 ≤
      (Nat.sqrt (2*n+1):ℤ)+2 := by omega
  nlinarith

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiWeighted
