/- GID: D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Complementary dyadic counterexamples and strict high-side cost scaling. -/

import D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ComplementaryDyadicSupportLines

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic.DyadicSupportLines

/-- The two-mass law on the complementary dyadic simplex. -/
noncomputable def counterexampleLaw (a : ℕ) (i : Fin (2 ^ a + 1)) : ℝ :=
  if i.val < 2 ^ (a - 1) + 1 then 1 / (2 : ℝ) ^ a
  else ((2 : ℝ) ^ a - 2) / ((2 : ℝ) ^ a) ^ 2

/-- An exact counterexample to the first supporting line for every exponent at least three. -/
theorem complementary_counterexample (a : ℕ) (ha : 3 ≤ a) :
    let B := (2 : ℝ) ^ a
    let p := counterexampleLaw a
    let t := Finset.univ.inf' (by simp) p
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
    Summable (fun d : ℕ => residual p d / (2 : ℝ) ^ d) ∧
    t = (B - 2) / B ^ 2 ∧ cost p = ((a : ℝ) + 1) * (B - 1) / B ∧
    B * ((a : ℝ) + 2) * t - cost p = (B - a - 3) / B ∧
    0 < (B - a - 3) / B ∧
    ¬ (∀ P : Fin (2 ^ a + 1) → ℝ, (∀ i, 0 ≤ P i) → (∑ i, P i = 1) →
      B * ((a : ℝ) + 2) * Finset.univ.inf' (by simp) P ≤ cost P) := by
  classical
  let B := (2 : ℝ) ^ a
  let H := 2 ^ (a - 1)
  let p := counterexampleLaw a
  have hB : 0 < B := by positivity
  have hB8 : 8 ≤ B := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at hh
    exact hh
  have hsplit : 2 ^ a + 1 = (H + 1) + H := by
    have he : a = (a - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
    dsimp only [H]
    omega
  have hH : (H : ℝ) = B / 2 := by
    have he : a = (a - 1) + 1 := by omega
    dsimp only [B, H]
    conv_rhs => rw [he, pow_succ]
    push_cast
    ring
  have split_sum (x y : ℝ) :
      (∑ i : Fin (2 ^ a + 1), if i.val < H + 1 then x else y) =
        (H + 1 : ℕ) * x + (H : ℝ) * y := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < H + 1 then x else y)]
    rw [hsplit, Finset.sum_range_add]
    have left : (∑ i ∈ Finset.range (H + 1), if i < H + 1 then x else y) =
        (H + 1 : ℕ) * x := by
      simp only [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi)),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have right : (∑ i ∈ Finset.range H, if H + 1 + i < H + 1 then x else y) =
        (H : ℝ) * y := by
      calc
        _ = ∑ _i ∈ Finset.range H, y := by
          apply Finset.sum_congr rfl
          intro i _
          rw [if_neg (by omega)]
        _ = _ := by simp
    rw [left, right]
  have hsmall : 0 ≤ (B - 2) / B ^ 2 := div_nonneg (by linarith) (by positivity)
  have horder : (B - 2) / B ^ 2 ≤ 1 / B := by
    field_simp [hB.ne']
    linarith
  have hprob (i : Fin (2 ^ a + 1)) : 0 ≤ p i := by
    dsimp only [p, counterexampleLaw]
    split_ifs <;> first | exact hsmall | positivity
  have hsum : ∑ i, p i = 1 := by
    change (∑ i : Fin (2 ^ a + 1), if i.val < H + 1 then 1 / B else
      (B - 2) / B ^ 2) = 1
    rw [split_sum]
    push_cast
    rw [hH]
    field_simp [hB.ne']
    ring
  have hmin : Finset.univ.inf' (by simp) p = (B - 2) / B ^ 2 := by
    apply le_antisymm
    · have hHpos : 0 < H := by positivity
      let i : Fin (2 ^ a + 1) := ⟨H + 1, by omega⟩
      have hi := Finset.inf'_le p (Finset.mem_univ i)
      have hpi : p i = (B - 2) / B ^ 2 := by
        dsimp only [p, counterexampleLaw, i]
        rw [if_neg (by dsimp only [H]; omega)]
      rw [← hpi]
      exact hi
    · apply Finset.le_inf'
      intro i _
      dsimp only [p, counterexampleLaw]
      split_ifs <;> first | exact horder | exact le_rfl
  have head_floor (d : ℕ) (hd : d < a) (i : Fin (2 ^ a + 1)) :
      ⌊(2 : ℝ) ^ d * p i⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_zero, zero_add]
    have hpmax : p i ≤ 1 / B := by
      dsimp only [p, counterexampleLaw]
      split_ifs <;> first | exact horder | exact le_rfl
    have hpw : (2 : ℝ) ^ d < B := by
      exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hd
    refine ⟨mul_nonneg (by positivity) (hprob i), ?_⟩
    have hh := mul_le_mul_of_nonneg_left hpmax (by positivity : 0 ≤ (2 : ℝ) ^ d)
    exact hh.trans_lt (by
      simpa only [mul_one_div] using (div_lt_one hB).mpr hpw)
  have head (d : ℕ) (hd : d < a) : residual p d / (2 : ℝ) ^ d = 1 := by
    simp only [DyadicSupportLines.residual, head_floor d hd, Finset.sum_const_zero, Int.cast_zero, sub_zero]
    exact div_self (by positivity)
  have middle_floor (j : ℕ) (hj : j < a) (i : Fin (2 ^ a + 1)) :
      ⌊(2 : ℝ) ^ (a + j) * p i⌋ =
        if i.val < H + 1 then (2 : ℤ) ^ j else (2 : ℤ) ^ j - 1 := by
    have hjB : (2 : ℝ) ^ (j + 1) ≤ B := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hid : (2 : ℝ) ^ (a + j) * ((B - 2) / B ^ 2) =
        (2 : ℝ) ^ j - (2 : ℝ) ^ (j + 1) / B := by
      dsimp only [B]
      rw [pow_add, pow_succ]
      field_simp
      ring
    dsimp only [p, counterexampleLaw]
    split_ifs with hi
    · have hid' : (2 : ℝ) ^ (a + j) * (1 / B) = (2 : ℝ) ^ j := by
        dsimp only [B]
        rw [pow_add]
        field_simp
      rw [hid']
      exact_mod_cast (Int.floor_natCast (R := ℝ) (2 ^ j))
    · rw [hid]
      apply Int.floor_eq_iff.mpr
      push_cast
      have hz : 0 < (2 : ℝ) ^ (j + 1) / B := by positivity
      have ho : (2 : ℝ) ^ (j + 1) / B ≤ 1 := (div_le_one hB).mpr hjB
      constructor <;> linarith
  have middle (j : ℕ) (hj : j < a) : residual p (a + j) = B / 2 - (2 : ℝ) ^ j := by
    simp only [DyadicSupportLines.residual, middle_floor j hj, Int.cast_sum]
    simp_rw [Int.cast_ite, Int.cast_pow, Int.cast_ofNat, Int.cast_sub, Int.cast_one]
    rw [split_sum]
    push_cast
    rw [hH, pow_add]
    change B * (2 : ℝ) ^ j - ((B / 2 + 1) * (2 : ℝ) ^ j +
      B / 2 * ((2 : ℝ) ^ j - 1)) = B / 2 - (2 : ℝ) ^ j
    ring
  have tail (d : ℕ) (hd : 2 * a ≤ d) : residual p d = 0 := by
    have hde : d = 2 * a + (d - 2 * a) := by omega
    have hf (i : Fin (2 ^ a + 1)) :
        (⌊(2 : ℝ) ^ d * p i⌋ : ℝ) = (2 : ℝ) ^ d * p i := by
      dsimp only [p, counterexampleLaw]
      split_ifs with hi
      · have he : (2 : ℝ) ^ d * (1 / B) = (2 : ℝ) ^ (d - a) := by
          dsimp only [B]
          conv_lhs => rw [show d = a + (d - a) by omega, pow_add]
          field_simp
        rw [he]
        exact_mod_cast (Int.floor_natCast (R := ℝ) (2 ^ (d - a)))
      · have he : (2 : ℝ) ^ d * ((B - 2) / B ^ 2) =
            (2 : ℝ) ^ (d - 2 * a) * (B - 2) := by
          conv_lhs => rw [hde, pow_add]
          rw [show (2 : ℝ) ^ (2 * a) = B ^ 2 by simp [B, pow_mul, Nat.mul_comm]]
          field_simp
        rw [he]
        have he' : (2 : ℝ) ^ (d - 2 * a) * (B - 2) =
            (((2 : ℤ) ^ (d - 2 * a) * ((2 : ℤ) ^ a - 2) : ℤ) : ℝ) := by
          push_cast
          rfl
        rw [he', Int.floor_intCast]
    simp only [DyadicSupportLines.residual, Int.cast_sum, hf,
      ← Finset.mul_sum, hsum, mul_one, sub_self]
  have hsumm : Summable (fun d : ℕ => residual p d / (2 : ℝ) ^ d) := by
    apply summable_of_ne_finset_zero (s := Finset.range (2 * a))
    intro d hd
    rw [tail d (by simpa using hd), zero_div]
  have hcost : cost p = ((a : ℝ) + 1) * (B - 1) / B := by
    have split := hsumm.sum_add_tsum_nat_add (2 * a)
    have hz : (∑' d : ℕ, residual p (d + 2 * a) / (2 : ℝ) ^ (d + 2 * a)) = 0 := by
      have he : (fun d : ℕ => residual p (d + 2 * a) / (2 : ℝ) ^ (d + 2 * a)) =
          (fun _ => 0) := by
        funext d
        rw [tail _ (by omega), zero_div]
      rw [he]
      exact tsum_zero
    rw [hz, add_zero] at split
    unfold cost
    rw [← split]
    rw [show 2 * a = a + a by omega, Finset.sum_range_add]
    have hhead : (∑ d ∈ Finset.range a, residual p d / (2 : ℝ) ^ d) = a := by
      simp only [Finset.sum_congr rfl (fun d hd => head d (Finset.mem_range.mp hd)),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hmid : (∑ j ∈ Finset.range a, residual p (a + j) / (2 : ℝ) ^ (a + j)) =
        1 / 2 * (∑ j ∈ Finset.range a, (1 / 2 : ℝ) ^ j) - (a : ℝ) / B := by
      calc
        _ = ∑ j ∈ Finset.range a, (1 / 2 * (1 / 2 : ℝ) ^ j - 1 / B) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [middle j (Finset.mem_range.mp hj), pow_add, one_div_pow]
          change (B / 2 - (2 : ℝ) ^ j) / (B * (2 : ℝ) ^ j) = _
          field_simp
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    rw [hhead, hmid, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    rw [one_div_pow]
    change (a : ℝ) + (1 / 2 * ((1 / B - 1) / (1 / 2 - 1)) - (a : ℝ) / B) = _
    field_simp [hB.ne']
    ring
  have hgap : B * ((a : ℝ) + 2) * Finset.univ.inf' (by simp) p - cost p =
      (B - a - 3) / B := by
    rw [hmin, hcost]
    field_simp [hB.ne']
    ring
  have hgrowth : (a : ℝ) + 3 < B := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ha
    have hg : ((n : ℝ) + 1) ≤ (2 : ℝ) ^ n := by
      have hh := one_add_mul_sub_le_pow (by norm_num : (-1 : ℝ) ≤ 2) n
      norm_num at hh
      linarith
    dsimp only [B]
    rw [pow_add]
    push_cast
    norm_num
    nlinarith
  have hpos : 0 < (B - a - 3) / B := div_pos (by linarith) hB
  refine ⟨hprob, hsum, hsumm, hmin, hcost, hgap, hpos, ?_⟩
  intro claim
  have hc := claim p hprob hsum
  linarith only [hc, hgap, hpos]


/-- The affine transformation used only above the strict high-side threshold. -/
noncomputable def highSideMap (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ)
    (i : Fin (2 ^ a + 1)) : ℝ :=
  ((2 : ℝ) ^ a) ^ 2 * p i - ((2 : ℝ) ^ a - 1)

/-- Strict high-side scaling, finite exit for nonuniform laws, and the uniform fixed point. -/
theorem complementary_high_side_scaling (a : ℕ) (ha : 3 ≤ a)
    (p : Fin (2 ^ a + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hh : ((2 : ℝ) ^ a - 1) / ((2 : ℝ) ^ a) ^ 2 <
      Finset.univ.inf' (by simp) p) :
    let B := (2 : ℝ) ^ a
    let t0 := (B - 1) / B ^ 2
    let t := Finset.univ.inf' (by simp) p
    let q := highSideMap a p
    let s := Finset.univ.inf' (by simp) q
    let H0 := (a : ℝ) + 2 - a / B - 2 / B ^ 2
    let C := B * ((a : ℝ) + 2) + 2 * B ^ 2
    let d0 := 2 * (B - 1)
    Summable (fun d : ℕ => residual p d / (2 : ℝ) ^ d) ∧
    (∀ i, 0 < q i) ∧ (∑ i, q i = 1) ∧ s = B ^ 2 * t - (B - 1) ∧
    Summable (fun d : ℕ => residual q d / (2 : ℝ) ^ d) ∧
    cost p = H0 + cost q / B ^ 2 ∧
    cost p - C * t + d0 = (cost q - C * s + d0) / B ^ 2 ∧
    ((¬ ∀ i, p i = 1 / (B + 1)) →
      ∃ k : ℕ,
        (∀ j < k, t0 < Finset.univ.inf' (by simp) ((highSideMap a)^[j] p)) ∧
        (∀ i, 0 < (highSideMap a)^[k] p i) ∧
        (∑ i, (highSideMap a)^[k] p i = 1) ∧
        0 < Finset.univ.inf' (by simp) ((highSideMap a)^[k] p) ∧
        Finset.univ.inf' (by simp) ((highSideMap a)^[k] p) ≤ t0) ∧
    ((∀ i, p i = 1 / (B + 1)) → q = p ∧
      cost p = (B * ((a : ℝ) + 2) + 2) / (B + 1)) := by
  classical
  let B := (2 : ℝ) ^ a
  let t0 := (B - 1) / B ^ 2
  let minimum := fun P : Fin (2 ^ a + 1) → ℝ => Finset.univ.inf' (by simp) P
  let t := minimum p
  let q := highSideMap a p
  have hB : 0 < B := by positivity
  have hB8 : 8 ≤ B := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at h
    exact h
  have hB2 : 0 < B ^ 2 := by positivity
  have hm : ((2 ^ a + 1 : ℕ) : ℝ) = B + 1 := by simp [B]
  have min_le (P : Fin (2 ^ a + 1) → ℝ) (i : Fin (2 ^ a + 1)) : minimum P ≤ P i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have min_map (P : Fin (2 ^ a + 1) → ℝ) :
      minimum (highSideMap a P) = B ^ 2 * minimum P - (B - 1) := by
    have mono : Monotone (fun x : ℝ => B ^ 2 * x - (B - 1)) := by
      intro x y hxy
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hxy hB2.le) _
    exact (Finset.apply_inf'_eq_inf'_comp (by simp)
      (fun x : ℝ => B ^ 2 * x - (B - 1)) (fun x y => mono.map_inf x y)).symm
  have step (P : Fin (2 ^ a + 1) → ℝ) (hS : ∑ i, P i = 1)
      (hhigh : t0 < minimum P) :
      (∀ i, 0 < highSideMap a P i) ∧ (∑ i, highSideMap a P i = 1) := by
    have ht : B - 1 < B ^ 2 * minimum P := by
      exact (div_lt_iff₀ hB2).mp hhigh
    constructor
    · intro i
      change 0 < B ^ 2 * P i - (B - 1)
      have hlo := mul_le_mul_of_nonneg_left (min_le P i) hB2.le
      linarith only [ht, hlo]
    · simp only [highSideMap, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS, mul_one]
      rw [hm]
      change B ^ 2 - (B + 1) * (B - 1) = 1
      ring
  have hhigh : t0 < t := hh
  obtain ⟨hqpos, hqsum⟩ := step p hs hhigh
  have summable (P : Fin (2 ^ a + 1) → ℝ) (hS : ∑ i, P i = 1) :
      Summable (fun d : ℕ => residual P d / (2 : ℝ) ^ d) := by
    have bound (d : ℕ) : 0 ≤ residual P d ∧ residual P d ≤ B + 1 := by
      have hscaled : ∑ i, (2 : ℝ) ^ d * P i = (2 : ℝ) ^ d := by
        rw [← Finset.mul_sum, hS, mul_one]
      have hlow := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => Int.floor_le ((2 : ℝ) ^ d * P i))
      have hupp := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => (Int.lt_floor_add_one ((2 : ℝ) ^ d * P i)).le)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hscaled, hm] at hlow hupp
      simp only [DyadicSupportLines.residual, Int.cast_sum]
      constructor <;> linarith only [hlow, hupp]
    apply Summable.of_nonneg_of_le
      (fun d => div_nonneg (bound d).1 (by positivity))
      (fun d => div_le_div_of_nonneg_right (bound d).2 (by positivity))
    simpa only [div_pow, div_eq_mul_inv] using
      (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left (B + 1)
  have hpupper (i : Fin (2 ^ a + 1)) : p i < 1 / B := by
    have hi := Finset.single_le_sum (f := fun j => p j - t)
      (fun j _ => sub_nonneg.mpr (min_le p j)) (Finset.mem_univ i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hs, hm] at hi
    have ht : B - 1 < B ^ 2 * t := (div_lt_iff₀ hB2).mp hhigh
    apply (lt_div_iff₀ hB).mpr
    nlinarith only [hi, ht, hB]
  have floors_head (d : ℕ) (hd : d < a) (i : Fin (2 ^ a + 1)) :
      ⌊(2 : ℝ) ^ d * p i⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    simp only [Int.cast_zero, zero_add]
    refine ⟨mul_nonneg (by positivity) (hp i), ?_⟩
    have hpow : (2 : ℝ) ^ d ≤ B :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd.le
    have hmul := mul_le_mul_of_nonneg_right hpow (hp i)
    exact hmul.trans_lt ((lt_div_iff₀ hB).mp (hpupper i))
  have floors_middle (j : ℕ) (hj : j < a) (i : Fin (2 ^ a + 1)) :
      ⌊(2 : ℝ) ^ (a + j) * p i⌋ = (2 : ℤ) ^ j - 1 := by
    have hpow : (2 : ℝ) ^ j < B :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hj
    have hlow : (2 : ℝ) ^ j - 1 < (2 : ℝ) ^ j * B * p i := by
      have ht : B - 1 < B ^ 2 * p i :=
        (div_lt_iff₀ hB2).mp (hhigh.trans_le (min_le p i))
      have hh' := mul_lt_mul_of_pos_left ht (by positivity : 0 < (2 : ℝ) ^ j)
      have hid : (2 : ℝ) ^ j * B * p i * B = (2 : ℝ) ^ j * (B ^ 2 * p i) := by ring
      nlinarith only [hh', hpow, hB, hid]
    have hupp : (2 : ℝ) ^ j * B * p i < (2 : ℝ) ^ j := by
      have h := mul_lt_mul_of_pos_left ((lt_div_iff₀ hB).mp (hpupper i))
        (by positivity : 0 < (2 : ℝ) ^ j)
      nlinarith only [h]
    apply Int.floor_eq_iff.mpr
    push_cast
    rw [pow_add]
    change (2 : ℝ) ^ j - 1 ≤ B * (2 : ℝ) ^ j * p i ∧
      B * (2 : ℝ) ^ j * p i < (2 : ℝ) ^ j - 1 + 1
    constructor <;> nlinarith only [hlow, hupp]
  have floors_tail (e : ℕ) (i : Fin (2 ^ a + 1)) :
      ⌊(2 : ℝ) ^ (2 * a + e) * p i⌋ = ⌊(2 : ℝ) ^ e * q i⌋ +
        ((2 : ℤ) ^ a - 1) * (2 : ℤ) ^ e := by
    have hid : (2 : ℝ) ^ (2 * a + e) * p i = (2 : ℝ) ^ e * q i +
        ((((2 : ℤ) ^ a - 1) * (2 : ℤ) ^ e : ℤ) : ℝ) := by
      dsimp only [q, highSideMap]
      rw [pow_add, show (2 : ℝ) ^ (2 * a) = B ^ 2 by simp [B, pow_mul, Nat.mul_comm]]
      push_cast
      change B ^ 2 * (2 : ℝ) ^ e * p i =
        (2 : ℝ) ^ e * (B ^ 2 * p i - (B - 1)) + (B - 1) * (2 : ℝ) ^ e
      ring
    rw [hid, Int.floor_add_intCast]
  have tail (e : ℕ) : residual p (2 * a + e) / (2 : ℝ) ^ (2 * a + e) =
      (residual q e / (2 : ℝ) ^ e) / B ^ 2 := by
    have hr : residual p (2 * a + e) = residual q e := by
      simp only [DyadicSupportLines.residual, floors_tail, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Int.cast_sum]
      push_cast
      rw [hm, pow_add,
        show (2 : ℝ) ^ (2 * a) = B ^ 2 by simp [B, pow_mul, Nat.mul_comm]]
      change B ^ 2 * (2 : ℝ) ^ e -
        ((∑ i, (⌊(2 : ℝ) ^ e * q i⌋ : ℝ)) + (B + 1) * ((B - 1) * (2 : ℝ) ^ e)) = _
      ring
    rw [hr, pow_add,
      show (2 : ℝ) ^ (2 * a) = B ^ 2 by simp [B, pow_mul, Nat.mul_comm]]
    ring
  have headsum : (∑ d ∈ Finset.range (2 * a), residual p d / (2 : ℝ) ^ d) =
      (a : ℝ) + 2 - a / B - 2 / B ^ 2 := by
    rw [show 2 * a = a + a by omega, Finset.sum_range_add]
    have head : (∑ d ∈ Finset.range a, residual p d / (2 : ℝ) ^ d) = a := by
      calc
        _ = ∑ _d ∈ Finset.range a, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          simp only [DyadicSupportLines.residual,
            floors_head d (Finset.mem_range.mp hd), Finset.sum_const_zero,
            Int.cast_zero, sub_zero]
          exact div_self (by positivity)
        _ = _ := by simp
    have middle : (∑ j ∈ Finset.range a, residual p (a + j) / (2 : ℝ) ^ (a + j)) =
        (B + 1) / B * (∑ j ∈ Finset.range a, (1 / 2 : ℝ) ^ j) - a / B := by
      calc
        _ = ∑ j ∈ Finset.range a, ((B + 1) / B * (1 / 2 : ℝ) ^ j - 1 / B) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [DyadicSupportLines.residual, floors_middle j (Finset.mem_range.mp hj),
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          rw [hm, pow_add, one_div_pow]
          change (B * (2 : ℝ) ^ j - (B + 1) * ((2 : ℝ) ^ j - 1)) /
            (B * (2 : ℝ) ^ j) = (B + 1) / B * (1 / (2 : ℝ) ^ j) - 1 / B
          field_simp
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp [div_eq_mul_inv]
    rw [head, middle, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1), one_div_pow]
    change (a : ℝ) + ((B + 1) / B * ((1 / B - 1) / (1 / 2 - 1)) - a / B) = _
    field_simp [hB.ne']
    ring
  have hcost : cost p = (a : ℝ) + 2 - a / B - 2 / B ^ 2 + cost q / B ^ 2 := by
    have split := (summable p hs).sum_add_tsum_nat_add (2 * a)
    have htail : (∑' e : ℕ, residual p (e + 2 * a) / (2 : ℝ) ^ (e + 2 * a)) =
        cost q / B ^ 2 := by
      simp_rw [Nat.add_comm _ (2 * a), tail]
      exact tsum_div_const
    rw [headsum, htail] at split
    exact split.symm
  have hdefect : cost p - (B * ((a : ℝ) + 2) + 2 * B ^ 2) * t + 2 * (B - 1) =
      (cost q - (B * ((a : ℝ) + 2) + 2 * B ^ 2) * minimum q + 2 * (B - 1)) /
        B ^ 2 := by
    rw [show minimum q = B ^ 2 * t - (B - 1) from min_map p, hcost]
    field_simp [hB.ne']
    ring
  have exit (hne : ¬ ∀ i, p i = 1 / (B + 1)) :
      ∃ k : ℕ, (∀ j < k, t0 < minimum ((highSideMap a)^[j] p)) ∧
        (∀ i, 0 < (highSideMap a)^[k] p i) ∧
        (∑ i, (highSideMap a)^[k] p i = 1) ∧
        0 < minimum ((highSideMap a)^[k] p) ∧
        minimum ((highSideMap a)^[k] p) ≤ t0 := by
    let u := 1 / (B + 1)
    have htlt : t < u := by
      have hbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ => min_le p i)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hs, hm] at hbound
      have htle : t ≤ u := (le_div_iff₀ (by positivity : 0 < B + 1)).mpr
        (by simpa only [mul_comm] using hbound)
      apply lt_of_le_of_ne htle
      intro heq
      apply hne
      intro i
      have hi := Finset.single_le_sum (f := fun j => p j - t)
        (fun j _ => sub_nonneg.mpr (min_le p j)) (Finset.mem_univ i)
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hs, hm] at hi
      have hu : (B + 1) * u = 1 := by dsimp only [u]; field_simp
      rw [heq, hu] at hi
      have hlo := min_le p i
      rw [heq] at hlo
      exact le_antisymm (by linarith only [hi]) hlo
    have formula (j : ℕ) : minimum ((highSideMap a)^[j] p) =
        u - (B ^ 2) ^ j * (u - t) := by
      induction j with
      | zero => simp [t]
      | succ j ih =>
        rw [Function.iterate_succ_apply', min_map, ih, pow_succ]
        dsimp only [u]
        field_simp
        ring
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((u - t0) / (u - t))
      (by nlinarith : 1 < B ^ 2)
    have hex : ∃ j : ℕ, minimum ((highSideMap a)^[j] p) ≤ t0 := by
      refine ⟨n, ?_⟩
      rw [formula]
      have h := (div_lt_iff₀ (sub_pos.mpr htlt)).mp hn
      linarith only [h]
    let k := Nat.find hex
    have hbefore (j : ℕ) (hj : j < k) : t0 < minimum ((highSideMap a)^[j] p) :=
      lt_of_not_ge (Nat.find_min hex hj)
    have hkpos : 0 < k := by
      by_contra hn
      have hk : k = 0 := by omega
      have h := Nat.find_spec hex
      change minimum ((highSideMap a)^[k] p) ≤ t0 at h
      rw [hk, Function.iterate_zero_apply] at h
      exact (not_le_of_gt hhigh) h
    have law (j : ℕ) (hj : j ≤ k) :
        (∀ i, 0 < (highSideMap a)^[j] p i) ∧ (∑ i, (highSideMap a)^[j] p i = 1) := by
      induction j with
      | zero =>
        simp only [Function.iterate_zero_apply]
        refine ⟨fun i => ?_, hs⟩
        have htpos : 0 < t := lt_trans (by dsimp only [t0]; positivity) hhigh
        exact htpos.trans_le (min_le p i)
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact step _ (ih (by omega)).2 (hbefore j (by omega))
    obtain ⟨hpos, hsum⟩ := law k le_rfl
    refine ⟨k, hbefore, hpos, hsum, ?_, Nat.find_spec hex⟩
    exact (Finset.lt_inf'_iff _).mpr (fun i _ => hpos i)
  have uniform (hu : ∀ i, p i = 1 / (B + 1)) :
      q = p ∧ cost p = (B * ((a : ℝ) + 2) + 2) / (B + 1) := by
    have hq : q = p := by
      funext i
      change B ^ 2 * p i - (B - 1) = p i
      rw [hu i]
      field_simp
      ring
    refine ⟨hq, ?_⟩
    rw [hq] at hcost
    have he : 1 - 1 / B ^ 2 ≠ 0 := by
      have hBB : 1 < B ^ 2 := by nlinarith
      have hdiv : 1 / B ^ 2 < 1 := (div_lt_one hB2).mpr hBB
      linarith
    apply (mul_left_cancel₀ he)
    have hce : (1 - 1 / B ^ 2) * cost p = (a : ℝ) + 2 - a / B - 2 / B ^ 2 := by
      linarith only [hcost]
    rw [hce]
    field_simp [hB.ne']
    ring
  exact ⟨summable p hs, hqpos, hqsum, min_map p, summable q hqsum,
    hcost, hdefect, exit, uniform⟩

end D5.S3.Arith.FibonacciAtomic.ComplementaryDyadicSupportLines
