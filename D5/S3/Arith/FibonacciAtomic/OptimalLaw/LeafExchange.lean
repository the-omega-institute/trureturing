/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLaw/LeafExchange
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLaw/LeafExchange
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A dyadic leaf exchange controls the same law at every depth and rules out profitable donors. -/

import D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic
open DyadicSupportLines
namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange

private noncomputable def exchanged {m : ℕ} (p q : Fin m → ℝ) (j : Fin m) (D : ℕ) : Fin m → ℝ :=
  fun i => p i + (1 / (2 : ℝ) ^ D) * q i - if i = j then 1 / (2 : ℝ) ^ D else 0

/-- Subtracting one depth-D donor cylinder preserves every coarser floor prefix. -/
lemma donor_prefix (x : ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hbit : ⌊(2 : ℝ) ^ D * x⌋ = 2 * ⌊(2 : ℝ) ^ (D - 1) * x⌋ + 1)
    (d : ℕ) (hd : d < D) :
    ⌊(2 : ℝ) ^ d * (x-1 / (2 : ℝ) ^ D)⌋ = ⌊(2 : ℝ) ^ d * x⌋ := by
  have hE : D = (D - 1) + 1 := by omega
  have scale : (2 : ℝ) ^ D * (x-1 / (2 : ℝ) ^ D) = (2 : ℝ) ^ D * x-1 := by
    field_simp
  have H := Int.floor_le ((2 : ℝ) ^ D * x)
  rw [hbit] at H
  push_cast at H
  have same : ⌊(2 : ℝ) ^ (D - 1) * (x-1 / (2 : ℝ) ^ D)⌋ = ⌊(2 : ℝ) ^ (D - 1) * x⌋ := by
    apply Int.floor_eq_iff.mpr
    have poweq : (2 : ℝ) ^ D = (2 : ℝ) ^ (D - 1) * 2 := by
      conv_lhs => rw [hE, pow_succ]
    have high := Int.lt_floor_add_one ((2 : ℝ) ^ (D - 1) * x)
    constructor
    · have scale' : 2 * ((2 : ℝ) ^ (D - 1) * (x-1 / (2 : ℝ) ^ D)) = (2 : ℝ) ^ D * x-1 := by
        calc
          _ = (2 : ℝ) ^ D * (x-1 / (2 : ℝ) ^ D) := by rw [poweq]; ring
          _ = _ := scale
      nlinarith only [H, scale']
    · have step : (2 : ℝ) ^ (D - 1) * (x-1 / (2 : ℝ) ^ D) ≤ (2 : ℝ) ^ (D - 1) * x := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [show (0 : ℝ) ≤ 1 / 2 ^ D by positivity]
      exact step.trans_lt high
  let k := D - 1-d
  have ek : D - 1 = d + k := by dsimp [k]; omega
  have scale_down (y : ℝ) : (2 : ℝ) ^ d * y = ((2 : ℝ) ^ (D - 1) * y) / ((2 ^ k : ℕ) : ℝ) := by
    rw [ek, pow_add]
    push_cast
    field_simp
  rw [scale_down, scale_down, Int.floor_div_natCast, Int.floor_div_natCast, same]

private lemma leaf_exchange (m D : ℕ) (p q : Fin m → ℝ) (j : Fin m)
    (hD : 1 ≤ D) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q i) (ht : ∑ i, q i = 1) (hqj : q j = 0)
    (hbit : ⌊(2 : ℝ) ^ D * p j⌋ = 2 * ⌊(2 : ℝ) ^ (D - 1) * p j⌋ + 1) :
    (∀ i, 0 ≤ exchanged p q j D i) ∧
    (∑ i, exchanged p q j D i) = 1 ∧
    (∀ d, d < D → DyadicSupportLines.residual (exchanged p q j D) d ≤ DyadicSupportLines.residual p d) ∧
    (∀ n, DyadicSupportLines.residual (exchanged p q j D) (D + n) ≤ DyadicSupportLines.residual p (D + n) + DyadicSupportLines.residual q n) ∧
    cost (exchanged p q j D) ≤ cost p + (1 / (2 : ℝ) ^ D) * cost q := by
  classical
  let P := exchanged p q j D
  let δ : ℝ := 1 / (2 : ℝ) ^ D
  have δpos : 0 < δ := by dsimp [δ]; positivity
  have debit : (2 : ℝ) ^ D * δ = 1 := by dsimp [δ]; field_simp
  have donor : δ ≤ p j := by
    have z : 0 ≤ ⌊(2 : ℝ) ^ (D - 1) * p j⌋ := Int.floor_nonneg.mpr (mul_nonneg (by positivity) (hp j))
    have b : (1 : ℤ) ≤ ⌊(2 : ℝ) ^ D * p j⌋ := by omega
    have b' : (1 : ℝ) ≤ (⌊(2 : ℝ) ^ D * p j⌋ : ℝ) := by exact_mod_cast b
    have H := Int.floor_le ((2 : ℝ) ^ D * p j)
    nlinarith [pow_pos (by norm_num : (0 : ℝ)<2) D]
  have positive (i : Fin m) : 0 ≤ P i := by
    dsimp [P, exchanged]
    split_ifs with hi
    · subst i
      rw [hqj, mul_zero, add_zero]
      exact sub_nonneg.mpr donor
    · exact sub_nonneg.mpr (by simpa [δ] using add_nonneg (hp i) (mul_nonneg δpos.le (hq i)))
  have total : ∑ i, P i = 1 := by
    simp [P, exchanged, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hs, ht]
  have shallow (d : ℕ) (hd : d < D) : DyadicSupportLines.residual P d ≤ DyadicSupportLines.residual p d := by
    have floors (i : Fin m) : ⌊(2 : ℝ) ^ d * p i⌋ ≤ ⌊(2 : ℝ) ^ d * P i⌋ := by
      by_cases hi : i = j
      · subst i
        simp only [P, exchanged, hqj, mul_zero, add_zero, ite_true]
        rw [donor_prefix _ D hD hbit d hd]
      · apply Int.floor_mono
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simp only [P, exchanged, if_neg hi, sub_zero]
        exact le_add_of_nonneg_right (mul_nonneg δpos.le (hq i))
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => floors i)
    unfold DyadicSupportLines.residual
    exact sub_le_sub_left (Int.cast_le.mpr H) _
  have deep (n : ℕ) : DyadicSupportLines.residual P (D + n) ≤ DyadicSupportLines.residual p (D + n) + DyadicSupportLines.residual q n := by
    have scaling : (2 : ℝ) ^ (D + n) * δ = (2 : ℝ) ^ n := by
      dsimp [δ]
      rw [pow_add]
      field_simp
    have floors (i : Fin m) :
        ⌊(2 : ℝ) ^ (D + n) * p i⌋ + ⌊(2 : ℝ) ^ n * q i⌋ -
          (if i = j then (2 : ℤ) ^ n else 0) ≤ ⌊(2 : ℝ) ^ (D + n) * P i⌋ := by
      by_cases hi : i = j
      · subst i
        have eqn : (2 : ℝ) ^ (D + n) * P j = (2 : ℝ) ^ (D + n) * p j - ((2 : ℤ) ^ n : ℝ) := by
          simp only [P, exchanged, hqj, mul_zero, add_zero, ite_true]
          push_cast
          rw [mul_sub, scaling]
        have hf : ⌊(2 : ℝ) ^ (D + n) * P j⌋ = ⌊(2 : ℝ) ^ (D + n) * p j⌋-(2 : ℤ) ^ n := by
          convert Int.floor_sub_intCast ((2 : ℝ) ^ (D + n) * p j) ((2 : ℤ) ^ n) using 1
          rw [eqn]
          norm_cast
        rw [hf]
        simp [hqj]
      · have eqn : (2 : ℝ) ^ (D + n) * P i =
            (2 : ℝ) ^ (D + n) * p i + (2 : ℝ) ^ n * q i := by
          simp only [P, exchanged, if_neg hi, sub_zero]
          rw [mul_add, ← mul_assoc, scaling]
        rw [eqn]
        simpa [hi] using Int.le_floor_add ((2 : ℝ) ^ (D + n) * p i) ((2 : ℝ) ^ n * q i)
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => floors i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at H
    have H' : (∑ i, (⌊(2 : ℝ) ^ (D + n) * p i⌋ : ℝ)) + (∑ i, (⌊(2 : ℝ) ^ n * q i⌋ : ℝ)) - (2 : ℝ) ^ n ≤
        (∑ i, (⌊(2 : ℝ) ^ (D + n) * P i⌋ : ℝ)) := by exact_mod_cast H
    simp only [DyadicSupportLines.residual, Int.cast_sum]
    linarith
  have pd := OptimalLawStrictSlope.law_data m p hs
  have qd := OptimalLawStrictSlope.law_data m q ht
  have nd := OptimalLawStrictSlope.law_data m P total
  have head : (∑ d ∈ Finset.range D, DyadicSupportLines.residual P d / (2 : ℝ) ^ d) ≤
      ∑ d ∈ Finset.range D, DyadicSupportLines.residual p d / (2 : ℝ) ^ d := by
    exact Finset.sum_le_sum (fun d hd => div_le_div_of_nonneg_right
      (shallow d (Finset.mem_range.mp hd)) (by positivity))
  have tail : (∑' n, DyadicSupportLines.residual P (n + D) / (2 : ℝ) ^ (n + D)) ≤
      (∑' n, DyadicSupportLines.residual p (n + D) / (2 : ℝ) ^ (n + D)) + δ * cost q := by
    have smp := pd.2.1.comp_injective (show Function.Injective (fun n : ℕ => n + D) from fun _ _ h => Nat.add_right_cancel h)
    have smn := nd.2.1.comp_injective (show Function.Injective (fun n : ℕ => n + D) from fun _ _ h => Nat.add_right_cancel h)
    dsimp only [Function.comp_def] at smp smn
    have smq := qd.2.1.mul_left δ
    have bound (n : ℕ) : DyadicSupportLines.residual P (n + D) / (2 : ℝ) ^ (n + D) ≤
        DyadicSupportLines.residual p (n + D) / (2 : ℝ) ^ (n + D) + δ * (DyadicSupportLines.residual q n / (2 : ℝ) ^ n) := by
      have H := div_le_div_of_nonneg_right (deep n) (by positivity : (0 : ℝ) ≤ 2 ^ (D + n))
      have eqn : (DyadicSupportLines.residual p (D + n) + DyadicSupportLines.residual q n) / (2 : ℝ) ^ (D + n) =
          DyadicSupportLines.residual p (D + n) / (2 : ℝ) ^ (D + n) + δ * (DyadicSupportLines.residual q n / (2 : ℝ) ^ n) := by
        dsimp [δ]
        rw [pow_add]
        field_simp
      simpa [Nat.add_comm, eqn] using H
    have H := smn.tsum_le_tsum bound (smp.add smq)
    rw [Summable.tsum_add smp smq, tsum_mul_left] at H
    exact H
  refine ⟨positive, total, shallow, deep, ?_⟩
  have a := nd.2.1.sum_add_tsum_nat_add D
  have b := pd.2.1.sum_add_tsum_nat_add D
  change _ = cost P at a
  change _ = cost p at b
  change cost P ≤ cost p + δ * cost q
  linarith

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange

namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange
private lemma minimum_lower (m D : ℕ) (p q : Fin m → ℝ) (j : Fin m)
    (S : Finset (Fin m)) (t u : ℝ) (hq : ∀ i, 0 ≤ q i)
    (hS : ∀ i ∈ S, t ≤ p i ∧ u ≤ q i)
    (houtside : ∀ i, i ∉ S → i ≠ j → t + (1 / (2 : ℝ) ^ D) * u ≤ p i)
    (hdonor : t + (1 / (2 : ℝ) ^ D) * (1 + u) ≤ p j) :
    ∀ i, t + (1 / (2 : ℝ) ^ D) * u ≤ exchanged p q j D i := by
  intro i
  have δ0 : (0 : ℝ) ≤ 1 / 2 ^ D := by positivity
  by_cases hi : i = j
  · subst i
    dsimp [exchanged]
    simp only [ite_true]
    have H := mul_nonneg δ0 (hq j)
    linarith
  · simp only [exchanged, if_neg hi, sub_zero]
    by_cases hs : i ∈ S
    · have H := hS i hs
      have HH := mul_le_mul_of_nonneg_left H.2 δ0
      linarith [H.1]
    · have H := houtside i hs hi
      linarith [mul_nonneg δ0 (hq i)]

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange

namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange
/-- A cheaper receiver cannot exploit a one digit of an attaining law while raising its minimum. -/
lemma profitable_leaf_impossible (m D : ℕ) (hm : 2 ≤ m)
    (p q : Fin m → ℝ) (j : Fin m) (hD : 1 ≤ D)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q i) (ht : ∑ i, q i = 1) (hqj : q j = 0)
    (S : Finset (Fin m)) (t u : ℝ) (htpos : 0 < t) (hupos : 0 < u)
    (hS : ∀ i ∈ S, t ≤ p i ∧ u ≤ q i)
    (houtside : ∀ i, i ∉ S → i ≠ j → t + (1 / (2 : ℝ) ^ D) * u ≤ p i)
    (hdonor : t + (1 / (2 : ℝ) ^ D) * (1 + u) ≤ p j)
    (hopt : cost p = OptimalLawStrictSlope.alpha m * t)
    (hprofit : cost q < OptimalLawStrictSlope.alpha m * u) :
    ⌊(2 : ℝ) ^ D * p j⌋ ≠ 2 * ⌊(2 : ℝ) ^ (D - 1) * p j⌋ + 1 := by
  classical
  intro hbit
  let P := exchanged p q j D
  let δ : ℝ := 1 / (2 : ℝ) ^ D
  have δpos : 0 < δ := by dsimp [δ]; positivity
  have H := leaf_exchange m D p q j hD hp hs hq ht hqj hbit
  have low := minimum_lower m D p q j S t u hq hS houtside hdonor
  have pos : ∀ i, 0 < P i := by
    intro i
    have B : 0 < t + δ * u := by positivity
    exact B.trans_le (low i)
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ P ⟨j, Finset.mem_univ j⟩
  have lealpha := OptimalLawStrictSlope.alpha_le m P pos H.2.1 k
    (fun i => hk i (Finset.mem_univ i))
  have L : OptimalLawStrictSlope.alpha m * P k ≤ cost P := (le_div_iff₀ (pos k)).mp lealpha
  have α0 : 0 ≤ OptimalLawStrictSlope.alpha m :=
    le_trans (Nat.cast_nonneg m) (OptimalLawStrictSlope.alpha_ge_labels m hm)
  have L' := mul_le_mul_of_nonneg_left (low k) α0
  have C := H.2.2.2.2
  have profit := mul_lt_mul_of_pos_left hprofit δpos
  change cost P ≤ cost p + δ * cost q at C
  rw [hopt] at C
  change OptimalLawStrictSlope.alpha m * (t + δ * u) ≤ _ at L'
  nlinarith only [L, L', C, profit]

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange
