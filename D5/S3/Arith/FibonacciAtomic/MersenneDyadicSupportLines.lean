/- GID: D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Two dyadic-cost supporting lines on every Mersenne real simplex. -/

import D5.S3.Arith.FibonacciAtomic.DyadicSupportLines

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic.DyadicSupportLines

/-- The two affine bounds on all real probability laws with `2^h-1` outcomes.
Zero atoms and terminating dyadic expansions are included. -/
theorem mersenne_support_lines (h : ℕ) (hh : 2 ≤ h)
    (p : Fin (2 ^ h - 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    let t := Finset.univ.inf' (by
      have H := (Nat.lt_two_pow_self (n := h))
      exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩) p
    Summable (fun d : ℕ => DyadicSupportLines.residual p d / (2 : ℝ) ^ d) ∧
      0 ≤ t ∧ t ≤ 1 / (2 ^ h - 1 : ℕ) ∧
      ((h : ℝ) * 2 ^ h - 2) * t ≤ cost p ∧
      (((h : ℝ) + 2) * 2 ^ h - 2) * t - 2 ≤ cost p := by
  classical
  let m := 2 ^ h - 1
  let M := (2 : ℝ) ^ h
  have hm : 0 < m := by dsimp [m]; have := (Nat.lt_two_pow_self (n := h)); omega
  have hM4 : 4 ≤ M := by
    have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hh
    norm_num at H
    exact H
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM4
  have hmcast : (m : ℝ) = M - 1 := by
    dsimp [m, M]
    rw [Nat.cast_sub (by have := (Nat.lt_two_pow_self (n := h)); omega)]
    norm_cast
  have hmc : (0 : ℝ) < m := by exact_mod_cast hm
  have data (P : Fin m → ℝ) (hS : ∑ i, P i = 1) :
      (∀ d, 0 ≤ DyadicSupportLines.residual P d ∧ DyadicSupportLines.residual P d ≤ m) ∧
        Summable (fun d : ℕ => DyadicSupportLines.residual P d / (2 : ℝ) ^ d) ∧ 0 ≤ cost P := by
    have bounds (d : ℕ) :
        0 ≤ DyadicSupportLines.residual P d ∧ DyadicSupportLines.residual P d ≤ m := by
      have hsum : ∑ i, (2 : ℝ) ^ d * P i = (2 : ℝ) ^ d := by
        rw [← Finset.mul_sum, hS, mul_one]
      have hlo := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => Int.floor_le ((2 : ℝ) ^ d * P i))
      have hhi := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => (Int.lt_floor_add_one ((2 : ℝ) ^ d * P i)).le)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hsum] at hlo hhi
      simp only [DyadicSupportLines.residual, Int.cast_sum]
      constructor <;> linarith only [hlo, hhi]
    have nonneg (d : ℕ) : 0 ≤ DyadicSupportLines.residual P d / (2 : ℝ) ^ d :=
      div_nonneg (bounds d).1 (by positivity)
    have summable : Summable (fun d : ℕ => DyadicSupportLines.residual P d / (2 : ℝ) ^ d) := by
      apply Summable.of_nonneg_of_le nonneg
        (fun d => div_le_div_of_nonneg_right (bounds d).2 (by positivity))
      simpa [div_pow, div_eq_mul_inv] using
        (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left (m : ℝ)
    exact ⟨bounds, summable, tsum_nonneg nonneg⟩
  have atom_upper (P : Fin m → ℝ) (hS : ∑ i, P i = 1) (t : ℝ)
      (ht : ∀ i, t ≤ P i) (i : Fin m) : P i ≤ 1 - ((m : ℝ) - 1) * t := by
    have H := Finset.single_le_sum (f := fun j => P j - t)
      (fun j _ => sub_nonneg.mpr (ht j)) (Finset.mem_univ i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hS] at H
    linarith only [H]
  have trunc (P : Fin m → ℝ) (hS : ∑ i, P i = 1) (n : ℕ) :
      ∑ d ∈ Finset.range n, DyadicSupportLines.residual P d / (2 : ℝ) ^ d ≤ cost P :=
    (data P hS).2.1.sum_le_tsum _
      (fun d _ => div_nonneg ((data P hS).1 d).1 (by positivity))
  have low (P : Fin m → ℝ) (hS : ∑ i, P i = 1)
      (t : ℝ) (ht0 : 0 ≤ t) (ht : ∀ i, t ≤ P i) (htlow : t ≤ 1 / M) :
      ((h : ℝ) * M - 2) * t ≤ cost P := by
    by_cases htzero : t = 0
    · simpa [htzero] using (data P hS).2.2
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
    have hMt : M * t ≤ 1 := by simpa [mul_comm] using (le_div_iff₀ hM).mp htlow
    let w : Fin m → ℝ := fun i => (P i - t) / (1 - (m : ℝ) * t)
    have hden : 0 < 1 - (m : ℝ) * t := by rw [hmcast]; nlinarith only [hMt, htpos]
    have hw0 (i : Fin m) : 0 ≤ w i := div_nonneg (sub_nonneg.mpr (ht i)) hden.le
    have hws : ∑ i, w i = 1 := by
      simp only [w, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS]
      exact div_self hden.ne'
    have hw1 (i : Fin m) : w i ≤ 1 := by
      rw [← hws]
      exact Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)
    have hwP (i : Fin m) : P i = t + (1 - (m : ℝ) * t) * w i := by
      dsimp only [w]
      rw [mul_div_cancel₀ _ hden.ne']
      ring
    have affine (i : Fin m) (A B : ℝ)
        (h0 : 0 ≤ B) (h1 : 0 ≤ A + B)
        (hv0 : (h : ℝ) / M ≤ A / M + B)
        (hv1 : 2 * ((h : ℝ) - 1) / M ≤ A * (2 / M) + B) :
        t * ((h : ℝ) + ((h : ℝ) - 2) * w i) ≤ A * P i + B := by
      have H0 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hMt)
        (sub_nonneg.mpr (hw1 i))) h0
      have H1 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hMt) (hw0 i)) h1
      have HV0 := mul_nonneg (mul_nonneg (mul_nonneg hM.le ht0)
        (sub_nonneg.mpr (hw1 i))) (sub_nonneg.mpr hv0)
      have HV1 := mul_nonneg (mul_nonneg (mul_nonneg hM.le ht0) (hw0 i))
        (sub_nonneg.mpr hv1)
      have identity : A * P i + B - t * ((h : ℝ) + ((h : ℝ) - 2) * w i) =
          (1 - M * t) * (1 - w i) * B + (1 - M * t) * w i * (A + B) +
          M * t * (1 - w i) * (A / M + B - (h : ℝ) / M) +
          M * t * w i * (A * (2 / M) + B - 2 * ((h : ℝ) - 1) / M) := by
        rw [hwP i, hmcast]
        field_simp [hM.ne']; ring
      rw [← sub_nonneg]
      rw [identity]
      exact add_nonneg (add_nonneg (add_nonneg H0 H1) HV0) HV1
    have scalar (i : Fin m) :
        t * ((h : ℝ) + ((h : ℝ) - 2) * w i) ≤
          ∑ d ∈ Finset.range h, (P i - (⌊(2 : ℝ) ^ d * P i⌋ : ℝ) / (2 : ℝ) ^ d) := by
      have hPi : P i < 1 := by
        have H := atom_upper P hS t ht i
        rw [hmcast] at H
        have H' := mul_pos (by linarith : 0 < M - 2) htpos
        linarith only [H, H']
      have hP0 : 0 ≤ P i := ht0.trans (ht i)
      have term0 (d : ℕ) : 0 ≤ P i - (⌊(2 : ℝ) ^ d * P i⌋ : ℝ) / (2 : ℝ) ^ d := by
        have H : (⌊(2 : ℝ) ^ d * P i⌋ : ℝ) / (2 : ℝ) ^ d ≤ P i :=
          (div_le_iff₀ (by positivity)).mpr (by
            simpa only [mul_comm] using Int.floor_le ((2 : ℝ) ^ d * P i))
        exact sub_nonneg.mpr H
      by_cases hsmall : (2 : ℝ) ^ h * P i < 1
      · have floors (d : ℕ) (hd : d ∈ Finset.range h) : ⌊(2 : ℝ) ^ d * P i⌋ = 0 := by
          apply Int.floor_eq_iff.mpr
          simp only [Int.cast_zero, zero_add]
          refine ⟨mul_nonneg (by positivity) hP0, ?_⟩
          have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (Nat.le_of_lt (Finset.mem_range.mp hd))
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right H hP0) hsmall
        have headsum : (∑ d ∈ Finset.range h,
            (P i - (⌊(2 : ℝ) ^ d * P i⌋ : ℝ) / (2 : ℝ) ^ d)) = (h : ℝ) * P i := by
          calc
            _ = ∑ _d ∈ Finset.range h, P i :=
              Finset.sum_congr rfl (fun d hd => by simp [floors d hd])
            _ = _ := by simp
        rw [headsum]
        have HV : 2 * ((h : ℝ) - 1) / M ≤ (h : ℝ) * (2 / M) + 0 := by
          apply (div_le_iff₀ hM).mpr
          field_simp [hM.ne']; nlinarith
        simpa only [add_zero] using affine i h 0 (by rfl) (by positivity) (by simp) HV
      · have hex : ∃ k : ℕ, 1 ≤ (2 : ℝ) ^ k * P i := ⟨h, le_of_not_gt hsmall⟩
        let k := Nat.find hex
        have hk : k ≤ h := Nat.find_min' hex (le_of_not_gt hsmall)
        have hkpos : 1 ≤ k := by
          by_contra H
          have hz : k = 0 := by omega
          have H' := Nat.find_spec hex
          change 1 ≤ (2 : ℝ) ^ k * P i at H'
          rw [hz] at H'
          norm_num at H'
          linarith only [H', hPi]
        have hxk : 1 ≤ (2 : ℝ) ^ k * P i := Nat.find_spec hex
        have floors (d : ℕ) (hd : d ∈ Finset.range k) : ⌊(2 : ℝ) ^ d * P i⌋ = 0 := by
          apply Int.floor_eq_iff.mpr
          simp only [Int.cast_zero, zero_add]
          exact ⟨mul_nonneg (by positivity) hP0,
            lt_of_not_ge (Nat.find_min hex (Finset.mem_range.mp hd))⟩
        have prefix_bound : (k : ℝ) * P i ≤
            ∑ d ∈ Finset.range h, (P i - (⌊(2 : ℝ) ^ d * P i⌋ : ℝ) / (2 : ℝ) ^ d) := by
          calc
            _ = ∑ d ∈ Finset.range k,
                (P i - (⌊(2 : ℝ) ^ d * P i⌋ : ℝ) / (2 : ℝ) ^ d) := by
              rw [Finset.sum_congr rfl (fun d hd => show
                P i - (⌊(2 : ℝ) ^ d * P i⌋ : ℝ) / (2 : ℝ) ^ d = P i by simp [floors d hd])]
              simp
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
              (fun d _ _ => term0 d)
        have hb0 : 0 ≤ 2 / (2 : ℝ) ^ k := by positivity
        have hb1 : 0 ≤ ((k : ℝ) - 2) + 2 / (2 : ℝ) ^ k := by
          by_cases hk1 : k = 1
          · norm_num [hk1]
          · have H : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
            linarith only [H, hb0]
        have growth : ((h - k : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (h - k) := by
          have H := one_add_mul_sub_le_pow (by norm_num : (-1 : ℝ) ≤ 2) (h - k)
          norm_num at H
          linarith only [H]
        have ratio : M / (2 : ℝ) ^ k = (2 : ℝ) ^ (h - k) := by
          dsimp only [M]
          simpa only [div_eq_mul_inv] using (pow_sub₀ (2 : ℝ) (by norm_num) hk).symm
        have ratio2 : 2 / (2 : ℝ) ^ k * M = 2 * (2 : ℝ) ^ (h - k) := by
          calc
            _ = 2 * (M / (2 : ℝ) ^ k) := by ring
            _ = _ := by rw [ratio]
        have hkr : ((h - k : ℕ) : ℝ) = (h : ℝ) - k := Nat.cast_sub hk
        have hv0 : (h : ℝ) / M ≤ ((k : ℝ) - 2) / M + 2 / (2 : ℝ) ^ k := by
          apply (div_le_iff₀ hM).mpr
          rw [add_mul, div_mul_cancel₀ _ hM.ne', ratio2]
          rw [hkr] at growth
          nlinarith only [growth, (show (k : ℝ) ≤ h by exact_mod_cast hk)]
        have hv1 : 2 * ((h : ℝ) - 1) / M ≤
            ((k : ℝ) - 2) * (2 / M) + 2 / (2 : ℝ) ^ k := by
          apply (div_le_iff₀ hM).mpr
          rw [add_mul]
          have H : (((k : ℝ) - 2) * (2 / M)) * M = 2 * ((k : ℝ) - 2) := by
            field_simp [hM.ne']
          rw [H, ratio2]
          rw [hkr] at growth
          linarith only [growth]
        have H := affine i ((k : ℝ) - 2) (2 / (2 : ℝ) ^ k) hb0 hb1 hv0 hv1
        have H' : ((k : ℝ) - 2) * P i + 2 / (2 : ℝ) ^ k ≤ (k : ℝ) * P i := by
          have HX : 1 / (2 : ℝ) ^ k ≤ P i :=
            (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hxk)
          have HX' : 2 / (2 : ℝ) ^ k ≤ 2 * P i := by
            simpa only [mul_one_div] using mul_le_mul_of_nonneg_left HX (by norm_num : (0 : ℝ) ≤ 2)
          nlinarith only [HX']
        exact H.trans (H'.trans prefix_bound)
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => scalar i)
    have lhs : ∑ i, t * ((h : ℝ) + ((h : ℝ) - 2) * w i) =
        ((h : ℝ) * M - 2) * t := by
      simp_rw [mul_add, ← mul_assoc]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hws, mul_one, hmcast]
      ring
    have rhs : (∑ i, ∑ d ∈ Finset.range h,
        (P i - (⌊(2 : ℝ) ^ d * P i⌋ : ℝ) / (2 : ℝ) ^ d)) =
        ∑ d ∈ Finset.range h, DyadicSupportLines.residual P d / (2 : ℝ) ^ d := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      simp only [Finset.sum_sub_distrib, ← Finset.sum_div, hS,
        DyadicSupportLines.residual, Int.cast_sum]
      field_simp [hM.ne']
    rw [lhs, rhs] at H
    exact H.trans (trunc P hS h)
  have high (P : Fin m → ℝ) (hS : ∑ i, P i = 1)
      (t : ℝ) (ht : ∀ i, t ≤ P i) (hthi : 1 / M < t) :
      let Q := fun i => M * P i - 1
      (∀ i, 0 ≤ Q i) ∧ (∑ i, Q i = 1) ∧ cost P = h + cost Q / M := by
    let Q : Fin m → ℝ := fun i => M * P i - 1
    have hMt : 1 < M * t := by simpa [mul_comm] using (div_lt_iff₀ hM).mp hthi
    have hQ (i : Fin m) : 0 ≤ Q i := by
      dsimp only [Q]
      have H := mul_le_mul_of_nonneg_left (ht i) hM.le
      linarith only [H, hMt]
    have hSQ : ∑ i, Q i = 1 := by
      simp only [Q, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS, mul_one, hmcast]
      ring
    have hPi (i : Fin m) : 0 ≤ P i ∧ M * P i < 2 := by
      have H := atom_upper P hS t ht i
      rw [hmcast] at H
      have H' := mul_pos (by linarith : 0 < M - 2) (sub_pos.mpr hMt)
      have H'' := mul_nonneg hM.le (sub_nonneg.mpr H)
      have htpos : 0 < t := lt_trans (by positivity) hthi
      exact ⟨le_trans htpos.le (ht i), by nlinarith only [H', H'']⟩
    have head_floor (i : Fin m) (d : ℕ) (hd : d < h) : ⌊(2 : ℝ) ^ d * P i⌋ = 0 := by
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_zero, zero_add]
      refine ⟨mul_nonneg (by positivity) (hPi i).1, ?_⟩
      have scale := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by omega : d + 1 ≤ h)
      change (2 : ℝ) ^ (d + 1) ≤ M at scale
      rw [pow_succ] at scale
      have H := mul_le_mul_of_nonneg_right scale (hPi i).1
      nlinarith only [H, (hPi i).2]
    have floor_tail (i : Fin m) (d : ℕ) :
        ⌊(2 : ℝ) ^ (d + h) * P i⌋ = ⌊(2 : ℝ) ^ d * Q i⌋ + (2 : ℤ) ^ d := by
      have scale : (2 : ℝ) ^ (d + h) * P i =
          (2 : ℝ) ^ d * Q i + (((2 : ℕ) ^ d : ℕ) : ℝ) := by
        simp only [Q, M, pow_add, Nat.cast_pow, Nat.cast_ofNat]
        ring
      rw [scale, Int.floor_add_natCast]
      norm_cast
    have tail (d : ℕ) : DyadicSupportLines.residual P (d + h) / (2 : ℝ) ^ (d + h) =
        (DyadicSupportLines.residual Q d / (2 : ℝ) ^ d) / M := by
      have hR : DyadicSupportLines.residual P (d + h) = DyadicSupportLines.residual Q d := by
        unfold DyadicSupportLines.residual
        simp_rw [floor_tail]
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, pow_add]
        push_cast
        rw [hmcast]
        dsimp only [M]
        ring
      rw [hR, pow_add]
      dsimp only [M]
      ring
    have head :
        ∑ d ∈ Finset.range h, DyadicSupportLines.residual P d / (2 : ℝ) ^ d = h := by
      have terms (d : ℕ) (hd : d ∈ Finset.range h) :
          DyadicSupportLines.residual P d / (2 : ℝ) ^ d = 1 := by
        simp only [DyadicSupportLines.residual, head_floor _ d (Finset.mem_range.mp hd),
          Int.cast_zero,
          Finset.sum_const_zero, sub_zero]
        exact div_self (by positivity)
      calc
        _ = ∑ _d ∈ Finset.range h, (1 : ℝ) := Finset.sum_congr rfl (fun d hd => terms d hd)
        _ = _ := by simp
    have tails :
        (∑' d, DyadicSupportLines.residual P (d + h) / (2 : ℝ) ^ (d + h)) = cost Q / M := by
      simp_rw [tail]
      exact tsum_div_const
    have split := Summable.sum_add_tsum_nat_add h (data P hS).2.1
    rw [head, tails] at split
    exact ⟨hQ, hSQ, split.symm⟩
  have approximate (n : ℕ) : ∀ (P : Fin m → ℝ), (∑ i, P i = 1) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 / (m : ℝ) → (∀ i, t ≤ P i) →
        (((h : ℝ) + 2) * M - 2) * t - 2 - ((h : ℝ) + 3) * (1 / M) ^ n ≤ cost P := by
    induction n with
    | zero =>
      intro P hS t ht0 htmax ht
      have H := (data P hS).2.2
      have htmax' := (le_div_iff₀ hmc).mp htmax
      rw [hmcast] at htmax'
      have hhm : (h : ℝ) ≤ m := by
        exact_mod_cast (show h ≤ m by dsimp [m]; have := Nat.lt_two_pow_self (n := h); omega)
      have hht : (h : ℝ) * t ≤ 1 := by
        have HH := mul_le_mul_of_nonneg_right hhm ht0
        rw [hmcast] at HH
        exact HH.trans (by simpa [mul_comm] using htmax')
      have HH := mul_nonneg (by positivity : 0 ≤ (h : ℝ) + 2) (sub_nonneg.mpr htmax')
      norm_num
      nlinarith only [H, hht, HH]
    | succ n ih =>
      intro P hS t ht0 htmax ht
      by_cases hlow : t ≤ 1 / M
      · have H := low P hS t ht0 ht hlow
        have H' := (le_div_iff₀ hM).mp hlow
        have Herr : 0 ≤ ((h : ℝ) + 3) * (1 / M) ^ (n + 1) := by positivity
        nlinarith only [H, H', Herr]
      · let Q : Fin m → ℝ := fun i => M * P i - 1
        obtain ⟨hQ, hSQ, heq⟩ := high P hS t ht (lt_of_not_ge hlow)
        change (∑ i, Q i) = 1 at hSQ
        change cost P = (h : ℝ) + cost Q / M at heq
        have htmax' := (le_div_iff₀ hmc).mp htmax
        have hstmax : M * t - 1 ≤ 1 / (m : ℝ) := by
          apply (le_div_iff₀ hmc).mpr
          rw [hmcast] at htmax' ⊢
          nlinarith only [htmax', hM.le]
        have H := ih Q hSQ (M * t - 1)
          (by have HH := (div_lt_iff₀ hM).mp (lt_of_not_ge hlow); linarith only [HH]) hstmax
          (fun i => by
            change M * t - 1 ≤ M * P i - 1
            exact sub_le_sub_right (mul_le_mul_of_nonneg_left (ht i) hM.le) 1)
        have HE : M * (cost P - (h : ℝ)) = cost Q := by
          rw [heq]
          field_simp [hM.ne']; ring
        rw [pow_succ]
        have Hdiv := (div_le_div_iff_of_pos_right hM).mpr H
        have HE' : cost Q / M = cost P - (h : ℝ) := by
          exact (div_eq_iff hM.ne').mpr (by simpa [mul_comm] using HE.symm)
        rw [HE'] at Hdiv
        have Id : ((((h : ℝ) + 2) * M - 2) * (M * t - 1) - 2 -
            ((h : ℝ) + 3) * (1 / M) ^ n) / M =
            (((h : ℝ) + 2) * M - 2) * t - 2 -
            ((h : ℝ) + 3) * ((1 / M) ^ n * (1 / M)) - (h : ℝ) := by
          field_simp [hM.ne']; ring
        rw [Id] at Hdiv
        linarith only [Hdiv]
  let t := Finset.univ.inf' (by exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩) p
  have lower (i : Fin m) : t ≤ p i := Finset.inf'_le _ (Finset.mem_univ i)
  have ht0 : 0 ≤ t := Finset.le_inf' _ p (fun i _ => hp i)
  have htmax : t ≤ 1 / (m : ℝ) := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => lower i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at H
    rw [show (∑ i : Fin m, p i) = 1 from hs] at H
    exact (le_div_iff₀ hmc).mpr (by simpa [mul_comm] using H)
  have second : (((h : ℝ) + 2) * M - 2) * t - 2 ≤ cost p := by
    have limit := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : (0 : ℝ) ≤ 1 / M) (by exact (div_lt_one hM).mpr (by linarith))
    have limit' : Filter.Tendsto
        (fun n : ℕ => (((h : ℝ) + 2) * M - 2) * t - 2 - ((h : ℝ) + 3) * (1 / M) ^ n)
        Filter.atTop (nhds ((((h : ℝ) + 2) * M - 2) * t - 2)) := by
      simpa only [mul_zero, sub_zero] using
        tendsto_const_nhds.sub (limit.const_mul ((h : ℝ) + 3))
    exact le_of_tendsto limit' (Filter.Eventually.of_forall
      (fun n => approximate n p hs t ht0 htmax lower))
  change Summable _ ∧ 0 ≤ t ∧ t ≤ 1 / (m : ℝ) ∧
    ((h : ℝ) * M - 2) * t ≤ cost p ∧ (((h : ℝ) + 2) * M - 2) * t - 2 ≤ cost p
  refine ⟨(data p hs).2.1, ht0, htmax, ?_, second⟩
  by_cases hlow : t ≤ 1 / M
  · exact low p hs t ht0 lower hlow
  · have H := (div_lt_iff₀ hM).mp (lt_of_not_ge hlow)
    nlinarith only [second, H]

end D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines
