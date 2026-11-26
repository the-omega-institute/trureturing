/- GID: D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The large-parameter limit of the signed Omega summatory limsup. -/

import D5.S3.Factorization.PrimeExponentRecordLimitOne
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-! The odd-part decomposition and a uniform error bound for the signed Omega sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Filter Real
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture

/-- The signed summatory function, with prime factors counted with multiplicity. -/
def W (a x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (-a) ^ ArithmeticFunction.cardFactors n

/-- The normalized real limsup from Theorem 1.5. -/
def s (a : ℝ) : ℝ :=
  Filter.limsup (fun x : ℝ => |W a x| / x ^ Real.logb 2 a) atTop

/-- A uniform bound for the contribution from odd integers greater than one. -/
def B (a : ℝ) : ℝ := (1 / 2 : ℝ) * 3 ^ (2 - Real.logb 2 a / 3)

private def geom (a : ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), (-a) ^ j

private lemma geom_eq {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    geom a k = (1 - (-a) ^ (k + 1)) / (a + 1) := by
  rw [geom, geom_sum_eq (by linarith : -a ≠ 1)]
  have hp : a + 1 ≠ 0 := by linarith
  have hn : -a - 1 ≠ 0 := by linarith
  field_simp
  ring

private lemma geom_bound {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    |geom a k| ≤ a ^ k := by
  have ha0 : 0 ≤ a := by linarith
  have hp : 0 < a + 1 := by linarith
  rw [geom_eq ha, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  calc
    |1 - (-a) ^ (k + 1)| ≤ |(1 : ℝ)| + |(-a) ^ (k + 1)| := abs_sub _ _
    _ = 1 + a ^ (k + 1) := by simp [abs_pow, abs_of_nonneg ha0]
    _ ≤ a ^ k * (a + 1) := by
      have h : 1 ≤ a ^ k := one_le_pow₀ ha
      rw [pow_succ]
      nlinarith

private lemma geom_lower {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    a / (a + 1) - (a ^ k)⁻¹ / (a + 1) ≤ |geom a k| / a ^ k := by
  have ha0 : 0 < a := by linarith
  have hp : 0 < a + 1 := by linarith
  have hk : 0 < a ^ k := pow_pos ha0 k
  have hl := abs_sub_abs_le_abs_sub ((-a) ^ (k + 1)) (1 : ℝ)
  simp only [abs_pow, abs_neg, abs_of_pos ha0, abs_one] at hl
  rw [abs_sub_comm] at hl
  rw [geom_eq ha, abs_div, abs_of_pos hp]
  apply (le_div_iff₀ hk).mpr
  apply (le_div_iff₀ hp).mpr
  rw [pow_succ] at hl
  field_simp
  nlinarith

private def odds (N : ℕ) : Finset ℕ := (Icc 1 N).filter Odd

private def height (N m : ℕ) : ℕ := Nat.log 2 (N / m)

private lemma height_iff {N m j : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    j ≤ height N m ↔ 2 ^ j * m ≤ N := by
  rw [height, Nat.le_log_iff_pow_le Nat.one_lt_two
    (Nat.ne_of_gt (Nat.div_pos hmN hm)), Nat.le_div_iff_mul_le hm]

private lemma decomposition (a : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (-a) ^ ArithmeticFunction.cardFactors n) =
      ∑ m ∈ odds N, (-a) ^ ArithmeticFunction.cardFactors m * geom a (height N m) := by
  classical
  simp_rw [geom, mul_sum]
  rw [sum_sigma']
  symm
  apply sum_bij (fun p _ => 2 ^ p.2 * p.1)
  · intro p hp
    rcases mem_sigma.mp hp with ⟨hm, hj⟩
    rcases mem_filter.mp hm with ⟨hmN, _⟩
    rcases mem_Icc.mp hmN with ⟨hm, hmN⟩
    exact mem_Icc.mpr ⟨Nat.mul_pos (by positivity) (by omega),
      (height_iff (by omega) hmN).mp (by simpa using hj)⟩
  · intro p hp q hq he
    rcases mem_sigma.mp hp with ⟨hm, _⟩
    rcases mem_sigma.mp hq with ⟨hn, _⟩
    have hmO := (mem_filter.mp hm).2
    have hnO := (mem_filter.mp hn).2
    have he' := congrArg (fun n => ordCompl[2] n) he
    simp only [Nat.ordCompl_pow_mul_of_not_dvd _ Nat.prime_two
      hmO.not_two_dvd_nat, Nat.ordCompl_pow_mul_of_not_dvd _ Nat.prime_two
      hnO.not_two_dvd_nat] at he'
    cases p with | mk m j =>
      cases q with | mk n k =>
        dsimp at he' he
        subst n
        have hjk := Nat.pow_right_injective (by decide : 2 ≤ 2)
          (mul_right_cancel₀ hmO.pos.ne' he)
        subst k
        rfl
  · intro n hn
    obtain ⟨j, m, hmO, hn'⟩ := Nat.exists_eq_two_pow_mul_odd
      (Nat.ne_of_gt (mem_Icc.mp hn).1)
    have hm : 0 < m := Nat.pos_of_ne_zero hmO.pos.ne'
    have hmN : m ≤ N := le_trans
      (Nat.le_mul_of_pos_left m (pow_pos (by decide) j)) (hn' ▸ (mem_Icc.mp hn).2)
    refine ⟨⟨m, j⟩, mem_sigma.mpr ⟨mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hm, hmN⟩, hmO⟩, ?_⟩, hn'.symm⟩
    apply mem_range.mpr
    exact Nat.lt_succ_of_le ((height_iff hm hmN).mpr (hn' ▸ (mem_Icc.mp hn).2))
  · intro p hp
    have hm := (mem_filter.mp (mem_sigma.mp hp).1).2
    rw [ArithmeticFunction.cardFactors_mul (by positivity) hm.pos.ne',
      ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two, pow_add]
    ring

private lemma exponent_data {a : ℝ} (ha : 64 ≤ a) :
    6 ≤ Real.logb 2 a ∧ (2 : ℝ) ^ Real.logb 2 a = a := by
  have ha0 : 0 < a := by linarith
  constructor
  · apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) ha0).mpr
    norm_num
    exact ha
  · exact Real.rpow_logb (by norm_num) (by norm_num) ha0

private lemma odd_weight {a : ℝ} (ha : 64 ≤ a) {m : ℕ} (hm : Odd m) :
    a ^ ArithmeticFunction.cardFactors m / (m : ℝ) ^ Real.logb 2 a ≤
      (m : ℝ) ^ (-(Real.logb 2 a / 3)) := by
  let v := Real.logb 2 a
  let t := ArithmeticFunction.cardFactors m
  have hv : 0 ≤ v := by have := (exponent_data ha).1; dsimp [v]; linarith
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm.pos
  have h3nat : 3 ^ ArithmeticFunction.cardFactors m ≤ m := by
    simpa only [ArithmeticFunction.cardFactors_apply] using
      D5.S3.Factorization.PrimeExponentRecordLimitOne.odd_part_lower m hm.pos.ne' hm
  have h3 : (3 : ℝ) ^ t ≤ m := by exact_mod_cast h3nat
  have h8 : (2 : ℝ) ^ (t * 3) ≤ (m : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two, pow_mul']
    calc
      ((2 : ℝ) ^ 3) ^ t ≤ ((3 : ℝ) ^ 2) ^ t := by gcongr; norm_num
      _ = ((3 : ℝ) ^ t) ^ 2 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      _ ≤ (m : ℝ) ^ 2 := by gcongr
  have hb := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ (t * 3)) h8
    (show 0 ≤ v / 3 by positivity)
  have hnum : a ^ t ≤ (m : ℝ) ^ (2 * v / 3) := by
    have he : ((2 : ℝ) ^ (t * 3)) ^ (v / 3) = a ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ = (2 : ℝ) ^ (v * (t : ℝ)) := by congr 1; push_cast; ring
        _ = ((2 : ℝ) ^ v) ^ t := Real.rpow_mul_natCast (by norm_num) _ _
        _ = a ^ t := by rw [(exponent_data ha).2]
    rw [he, ← Real.rpow_mul hm0.le] at hb
    convert hb using 1 <;> congr 1 <;> ring
  calc
    a ^ t / (m : ℝ) ^ v ≤ (m : ℝ) ^ (2 * v / 3) / (m : ℝ) ^ v :=
      div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hm0.le _)
    _ = (m : ℝ) ^ (-(v / 3)) := by
      rw [← Real.rpow_sub hm0]
      congr 1
      ring

private lemma reciprocal_tail (N : ℕ) :
    (∑ m ∈ Icc 3 (N + 2), 1 / ((m : ℝ) * (m - 1))) =
      1 / 2 - 1 / (N + 2 : ℝ) := by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · norm_num
  calc
    _ = ∑ m ∈ Icc 3 (N + 2),
        (-1 / (((m + 1 : ℕ) : ℝ) - 1) - -1 / ((m : ℝ) - 1)) := by
      apply sum_congr rfl
      intro m hm
      have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
      have hm0 : (m : ℝ) ≠ 0 := by linarith
      have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
      push_cast
      field_simp [hm0, hm1]
      <;> ring
    _ = -1 / (((N + 2 + 1 : ℕ) : ℝ) - 1) - -1 / ((3 : ℝ) - 1) :=
      Finset.sum_Icc_sub (by omega) (fun m : ℕ => -1 / ((m : ℝ) - 1))
    _ = _ := by push_cast; ring_nf

private lemma power_tail {r : ℝ} (hr : 2 ≤ r) (N : ℕ) :
    (∑ m ∈ Icc 3 N, (m : ℝ) ^ (-r)) ≤ (1 / 2 : ℝ) * 3 ^ (2 - r) := by
  have hc : 0 ≤ (3 : ℝ) ^ (2 - r) := Real.rpow_nonneg (by norm_num) _
  have hpoint (m : ℕ) (hm : m ∈ Icc 3 N) :
      (m : ℝ) ^ (-r) ≤ 3 ^ (2 - r) * (1 / ((m : ℝ) * (m - 1))) := by
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have hm0 : 0 < (m : ℝ) := by linarith
    have hp : (m : ℝ) ^ (2 - r) ≤ (3 : ℝ) ^ (2 - r) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hm3 (by linarith)
    have he : (m : ℝ) ^ (-r) = (m : ℝ) ^ (2 - r) / (m : ℝ) ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_sub hm0]
      congr 1
      ring
    rw [he, mul_one_div]
    apply div_le_div₀ hc hp
    · exact mul_pos hm0 (by linarith)
    · nlinarith
  calc
    _ ≤ ∑ m ∈ Icc 3 N, 3 ^ (2 - r) * (1 / ((m : ℝ) * (m - 1))) :=
      sum_le_sum hpoint
    _ = 3 ^ (2 - r) * ∑ m ∈ Icc 3 N, 1 / ((m : ℝ) * (m - 1)) := by rw [mul_sum]
    _ ≤ 3 ^ (2 - r) * ∑ m ∈ Icc 3 (N + 2), 1 / ((m : ℝ) * (m - 1)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (by omega))
      intro m hm _
      have : (3 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
      exact le_of_lt (one_div_pos.mpr (mul_pos (by linarith) (by linarith)))
    _ ≤ (1 / 2 : ℝ) * 3 ^ (2 - r) := by
      rw [reciprocal_tail]
      have : 0 ≤ 1 / (N + 2 : ℝ) := by positivity
      nlinarith

private def weight (a : ℝ) (m : ℕ) : ℝ :=
  a ^ ArithmeticFunction.cardFactors m / (m : ℝ) ^ Real.logb 2 a

private lemma odd_tail {a : ℝ} (ha : 64 ≤ a) (N : ℕ) :
    ∑ m ∈ (odds N).erase 1, weight a m ≤ B a := by
  classical
  have hs : (odds N).erase 1 ⊆ Icc 3 N := by
    intro m hm
    rcases mem_erase.mp hm with ⟨hm1, hm⟩
    rcases mem_filter.mp hm with ⟨hmN, hmO⟩
    rcases mem_Icc.mp hmN with ⟨hm, hmN⟩
    exact mem_Icc.mpr ⟨by obtain ⟨j, hj⟩ := hmO; omega, hmN⟩
  calc
    _ ≤ ∑ m ∈ (odds N).erase 1, (m : ℝ) ^ (-(Real.logb 2 a / 3)) := by
      apply sum_le_sum
      intro m hm
      exact odd_weight ha (mem_filter.mp (mem_of_mem_erase hm)).2
    _ ≤ ∑ m ∈ Icc 3 N, (m : ℝ) ^ (-(Real.logb 2 a / 3)) :=
      sum_le_sum_of_subset_of_nonneg hs (fun m _ _ => Real.rpow_nonneg (by positivity) _)
    _ ≤ B a := power_tail (by have := (exponent_data ha).1; linarith) N

private lemma dyadic_power {a : ℝ} (ha : 64 ≤ a) (j : ℕ) :
    ((2 : ℝ) ^ j) ^ Real.logb 2 a = a ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm, Real.rpow_mul_natCast (by norm_num), (exponent_data ha).2]

private lemma block_bound {a x : ℝ} (ha : 64 ≤ a) (hx : 1 ≤ x) {m : ℕ}
    (hm : m ∈ odds ⌊x⌋₊) :
    |(-a) ^ ArithmeticFunction.cardFactors m * geom a (height ⌊x⌋₊ m)| ≤
      x ^ Real.logb 2 a * weight a m := by
  have ha0 : 0 ≤ a := by linarith
  rcases mem_filter.mp hm with ⟨hmN, hmO⟩
  rcases mem_Icc.mp hmN with ⟨hm1, hmN⟩
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have hx0 : 0 < x := by linarith
  have hv : 0 ≤ Real.logb 2 a := by have := (exponent_data ha).1; linarith
  have hc : ((2 : ℝ) ^ height ⌊x⌋₊ m) * m ≤ x := by
    have h := (height_iff (by omega) hmN).mp (le_refl (height ⌊x⌋₊ m))
    have h' : ((2 : ℝ) ^ height ⌊x⌋₊ m) * m ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast h
    exact h'.trans (Nat.floor_le hx0.le)
  have hr := Real.rpow_le_rpow (by positivity) hc hv
  rw [Real.mul_rpow (by positivity) hm0.le, dyadic_power ha] at hr
  have hj : a ^ height ⌊x⌋₊ m ≤ x ^ Real.logb 2 a / (m : ℝ) ^ Real.logb 2 a :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hm0 _)).mpr hr
  calc
    _ = a ^ ArithmeticFunction.cardFactors m * |geom a (height ⌊x⌋₊ m)| := by
      rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg ha0]
    _ ≤ a ^ ArithmeticFunction.cardFactors m * a ^ height ⌊x⌋₊ m := by
      gcongr
      exact geom_bound (by linarith) _
    _ ≤ a ^ ArithmeticFunction.cardFactors m *
        (x ^ Real.logb 2 a / (m : ℝ) ^ Real.logb 2 a) := by gcongr
    _ = x ^ Real.logb 2 a * weight a m := by dsimp [weight]; ring

private lemma residual {a x : ℝ} (ha : 64 ≤ a) (hx : 1 ≤ x) :
    |W a x - geom a (Nat.log 2 ⌊x⌋₊)| ≤ x ^ Real.logb 2 a * B a := by
  classical
  have h1 : 1 ∈ odds ⌊x⌋₊ := by
    simp only [odds, mem_filter, mem_Icc, le_refl, true_and]
    exact ⟨(Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by exact_mod_cast hx), by decide⟩
  have he : W a x - geom a (Nat.log 2 ⌊x⌋₊) =
      ∑ m ∈ (odds ⌊x⌋₊).erase 1,
        (-a) ^ ArithmeticFunction.cardFactors m * geom a (height ⌊x⌋₊ m) := by
    have h := sum_erase_add (odds ⌊x⌋₊)
      (fun m => (-a) ^ ArithmeticFunction.cardFactors m * geom a (height ⌊x⌋₊ m)) h1
    rw [W, decomposition]
    simpa [height] using (eq_sub_iff_add_eq.mpr h).symm
  rw [he]
  calc
    _ ≤ ∑ m ∈ (odds ⌊x⌋₊).erase 1,
        |(-a) ^ ArithmeticFunction.cardFactors m * geom a (height ⌊x⌋₊ m)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ (odds ⌊x⌋₊).erase 1, x ^ Real.logb 2 a * weight a m := by
      apply sum_le_sum
      intro m hm
      exact block_bound ha hx (mem_of_mem_erase hm)
    _ = x ^ Real.logb 2 a * ∑ m ∈ (odds ⌊x⌋₊).erase 1, weight a m := by rw [mul_sum]
    _ ≤ x ^ Real.logb 2 a * B a :=
      mul_le_mul_of_nonneg_left (odd_tail ha _) (Real.rpow_nonneg (by linarith) _)

private lemma uniform_upper {a x : ℝ} (ha : 64 ≤ a) (hx : 1 ≤ x) :
    |W a x| / x ^ Real.logb 2 a ≤ 1 + B a := by
  have h1 : 1 ∈ odds ⌊x⌋₊ := by
    simp only [odds, mem_filter, mem_Icc, le_refl, true_and]
    exact ⟨(Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx), by decide⟩
  have hg := block_bound ha hx h1
  simp only [ArithmeticFunction.cardFactors_one, pow_zero, one_mul, height,
    Nat.div_one, weight, Nat.cast_one, Real.one_rpow, div_one, mul_one] at hg
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < x) _)).mpr
  have h := abs_add_le (W a x - geom a (Nat.log 2 ⌊x⌋₊))
    (geom a (Nat.log 2 ⌊x⌋₊))
  rw [sub_add_cancel] at h
  nlinarith [residual ha hx]

private lemma dyadic_lower {a : ℝ} (ha : 64 ≤ a) (k : ℕ) :
    a / (a + 1) - (a ^ k)⁻¹ / (a + 1) - B a ≤
      |W a ((2 : ℝ) ^ k)| / ((2 : ℝ) ^ k) ^ Real.logb 2 a := by
  have hx : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have he : Nat.log 2 ⌊(2 : ℝ) ^ k⌋₊ = k := by
    rw [show (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) by norm_cast,
      Nat.floor_natCast, Nat.log_pow Nat.one_lt_two]
  have hr := residual ha hx
  rw [he, dyadic_power ha] at hr
  rw [dyadic_power ha]
  have hg := geom_lower (by linarith : 1 ≤ a) k
  have h := abs_sub_abs_le_abs_sub (geom a k) (W a ((2 : ℝ) ^ k))
  rw [abs_sub_comm] at h
  have hk : 0 < a ^ k := pow_pos (by linarith) _
  have hh : (|geom a k| - |W a ((2 : ℝ) ^ k)|) / a ^ k ≤ B a :=
    (div_le_iff₀ hk).mpr (by simpa [mul_comm] using h.trans hr)
  rw [sub_div] at hh
  linarith

/-- The uniform two-sided estimate for the limsup in the large-parameter range. -/
theorem quantitative (a : ℝ) (ha : 64 ≤ a) :
    a / (a + 1) - B a ≤ s a ∧ s a ≤ 1 + B a := by
  let q : ℝ → ℝ := fun x => |W a x| / x ^ Real.logb 2 a
  have hu : ∀ᶠ x : ℝ in atTop, q x ≤ 1 + B a := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact uniform_upper ha hx
  have hb : IsBoundedUnder (· ≤ ·) atTop q := isBoundedUnder_of_eventually_le hu
  have hn : ∀ᶠ x : ℝ in atTop, 0 ≤ q x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have hc : IsCoboundedUnder (· ≤ ·) atTop q :=
    isCoboundedUnder_le_of_eventually_le atTop hn
  constructor
  · change a / (a + 1) - B a ≤ limsup q atTop
    apply (le_limsup_iff' hc hb).mpr
    intro y hy
    have ha1 : 1 < a := by linarith
    have hz : Tendsto (fun k : ℕ => (a ^ k)⁻¹ / (a + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_atTop_of_one_lt ha1).inv_tendsto_atTop.div_const (a + 1)
    have hL : Tendsto
        (fun k : ℕ => a / (a + 1) - (a ^ k)⁻¹ / (a + 1) - B a)
        atTop (𝓝 (a / (a + 1) - B a)) := by
      simpa using (tendsto_const_nhds.sub hz).sub_const (B a)
    have hev : ∀ᶠ k : ℕ in atTop, y ≤ q ((2 : ℝ) ^ k) := by
      filter_upwards [(tendsto_order.mp hL).1 y hy] with k hk
      exact hk.le.trans (dyadic_lower ha k)
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).frequently
      hev.frequently
  · exact limsup_le_of_le hc hu

private lemma B_limit : Tendsto B atTop (𝓝 0) := by
  have he : Tendsto (fun a : ℝ => 2 - Real.logb 2 a / 3) atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [(Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop
      (3 * (2 - b))] with a ha
    linarith
  have h := ((tendsto_rpow_atBot_of_base_gt_one 3 (by norm_num)).comp he).const_mul
    (1 / 2 : ℝ)
  change Tendsto (fun a : ℝ => (1 / 2 : ℝ) * 3 ^ (2 - Real.logb 2 a / 3))
    atTop (𝓝 0)
  simpa only [Function.comp_def, mul_zero] using h

/-- Johnston--Leong--Tudzi Conjecture 5.1. -/
theorem result : Tendsto s atTop (𝓝 1) := by
  have hi : Tendsto (fun a : ℝ => 1 / (a + 1)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).const_div_atTop 1
  have hf : Tendsto (fun a : ℝ => a / (a + 1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hi
    have h' : Tendsto (fun a : ℝ => 1 - 1 / (a + 1)) atTop (𝓝 1) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (-1 : ℝ)] with a ha
    have hn : a + 1 ≠ 0 := by linarith
    field_simp
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hf.sub B_limit)
    (by simpa using (tendsto_const_nhds (x := (1 : ℝ))).add B_limit)
  · filter_upwards [eventually_ge_atTop (64 : ℝ)] with a ha
    exact (quantitative a ha).1
  · filter_upwards [eventually_ge_atTop (64 : ℝ)] with a ha
    exact (quantitative a ha).2

end D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture
