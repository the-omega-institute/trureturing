/- GID: D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform low-side second support for real laws on a complementary dyadic simplex. -/

import D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines
import D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
namespace D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
open D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
open D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope (law_data)

local notation "term" => (fun (x : ℝ) (d : ℕ) =>
  x - (⌊(2 : ℝ) ^ d * x⌋ : ℝ) / (2 : ℝ) ^ d)

private theorem term_nonneg (x : ℝ) (d : ℕ) : 0 ≤ term x d := by
  dsimp only
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using Int.floor_le ((2 : ℝ) ^ d * x)

private theorem prefix_le {m : ℕ} (p : Fin m → ℝ) (hs : ∑ i, p i = 1) (n : ℕ) :
    ∑ i, ∑ d ∈ Finset.range n, term (p i) d ≤ cost p := by
  have eq (d : ℕ) : ∑ i, term (p i) d = DyadicSupportLines.residual p d / (2 : ℝ) ^ d := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div, hs,
      DyadicSupportLines.residual, Int.cast_sum]
    field_simp
  rw [Finset.sum_comm]
  simp_rw [eq]
  exact (law_data m p hs).2.1.sum_le_tsum _
    (fun d _ => div_nonneg ((law_data m p hs).1 d).1 (by positivity))

private theorem atom_upper {m : ℕ} (p : Fin m → ℝ) (hs : ∑ i, p i = 1)
    (t : ℝ) (ht : ∀ i, t ≤ p i) (i : Fin m) : p i ≤ 1 - ((m : ℝ) - 1) * t := by
  have H := Finset.single_le_sum (f := fun j => p j - t)
    (fun j _ => sub_nonneg.mpr (ht j)) (Finset.mem_univ i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hs] at H
  linarith

private theorem merge {n : ℕ} (hn : 0 < n) (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (t : ℝ) (ht : ∀ i, t ≤ p i) :
    ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      (∀ i, t ≤ q i) ∧ cost q ≤ cost p := by
  classical
  let k : Fin (n + 1) := 0
  let l : Fin n := ⟨0, hn⟩
  let q : Fin n → ℝ := fun i => p (k.succAbove i) + if i = l then p k else 0
  have hq (i : Fin n) : 0 ≤ q i := by
    dsimp [q]
    split_ifs <;> linarith [hp (k.succAbove i), hp k]
  have total : ∑ i, q i = 1 := by
    simp only [q, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have H := Fin.sum_univ_succAbove p k
    linarith
  have lower (i : Fin n) : t ≤ q i := by
    dsimp [q]
    split_ifs <;> linarith [ht (k.succAbove i), hp k]
  have floor_sum (d : ℕ) :
      (∑ i, ⌊(2 : ℝ) ^ d * p i⌋) ≤ ∑ i, ⌊(2 : ℝ) ^ d * q i⌋ := by
    have pointwise (i : Fin n) :
        ⌊(2 : ℝ) ^ d * p (k.succAbove i)⌋ +
          (if i = l then ⌊(2 : ℝ) ^ d * p k⌋ else 0) ≤ ⌊(2 : ℝ) ^ d * q i⌋ := by
      by_cases hi : i = l
      · simp only [q, hi, ite_true]
        simpa only [mul_add, hi] using
          Int.le_floor_add ((2 : ℝ) ^ d * p (k.succAbove i)) ((2 : ℝ) ^ d * p k)
      · simp only [q, hi, ite_false, add_zero, le_refl]
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => pointwise i)
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at H
    have E := Fin.sum_univ_succAbove (fun i => ⌊(2 : ℝ) ^ d * p i⌋) k
    omega
  have resid_le (d : ℕ) : DyadicSupportLines.residual q d ≤ DyadicSupportLines.residual p d := by
    unfold DyadicSupportLines.residual
    have H : (∑ i, (⌊(2 : ℝ) ^ d * p i⌋:ℝ)) ≤ ∑ i, (⌊(2 : ℝ) ^ d * q i⌋:ℝ) := by
      exact_mod_cast floor_sum d
    simp only [Int.cast_sum]
    linarith
  refine ⟨q, hq, total, lower, ?_⟩
  exact (law_data n q total).2.1.tsum_le_tsum
    (fun d => div_le_div_of_nonneg_right (resid_le d) (by positivity))
    (law_data (n + 1) p hs).2.1

private theorem mersenne_comparison (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (t : ℝ) (ht : ∀ i, t ≤ p i) :
    (((a : ℝ) + 2) * (2 : ℝ) ^ a - 2) * t - 2 ≤ cost p := by
  classical
  have hB : 1 < 2 ^ a := by have H := Nat.lt_two_pow_self (n:= a); omega
  obtain ⟨q, hq, hqs, hqt, hqcost⟩ := merge (by positivity : 0 < 2 ^ a) p hp hs t ht
  have hnat : 2 ^ a - 1 + 1 = 2 ^ a := by omega
  let q' : Fin (2 ^ a - 1 + 1) → ℝ := fun i => q (Fin.cast hnat i)
  have qs' : ∑ i, q' i = 1 := by
    have E : (∑ i, q' i) = ∑ i, q i :=
      Fintype.sum_equiv (finCongr hnat) _ _ (fun _ => rfl)
    exact E.trans hqs
  have qp' : ∀ i, 0 ≤ q' i := fun i => hq _
  have qt' : ∀ i, t ≤ q' i := fun i => hqt _
  obtain ⟨r, hr, hrs, hrt, hrcost⟩ := merge (by omega : 0 < 2 ^ a - 1) q' qp' qs' t qt'
  have qeq : cost q'=cost q := by
    have E (d : ℕ) : (∑ i, (⌊(2 : ℝ) ^ d * q' i⌋:ℤ)) = ∑ i, (⌊(2 : ℝ) ^ d * q i⌋:ℤ) :=
      Fintype.sum_equiv (finCongr hnat) _ _ (fun _ => rfl)
    unfold cost
    apply tsum_congr
    intro d
    unfold DyadicSupportLines.residual
    rw [E]
  have hm : (Finset.univ : Finset (Fin (2 ^ a - 1))).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let u := Finset.univ.inf' hm r
  have tu : t ≤ u := Finset.le_inf' _ _ (fun i _ => hrt i)
  have H := D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines.mersenne_support_lines
    a (by omega) r hr hrs
  have H' : (((a : ℝ) + 2) * (2 : ℝ) ^ a - 2) * u - 2 ≤ cost r := H.2.2.2.2
  have hcoef : 0 ≤ ((a : ℝ) + 2) * (2 : ℝ) ^ a - 2 := by
    have a0 : (3 : ℝ) ≤ a := by exact_mod_cast ha
    have pow1 : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
    nlinarith
  have htbound := mul_le_mul_of_nonneg_left tu hcoef
  rw [qeq] at hrcost
  linarith
private theorem inverse_geometric (n : ℕ) : ∑ j ∈ Finset.range n, (1 : ℝ) / (2 : ℝ) ^ j =
    2 - 2 / (2 : ℝ) ^ n := by
  have H := geom_sum_inv (by norm_num : (2 : ℝ) ≠ 1) (by norm_num : (2 : ℝ) ≠ 0) n
  rw [show (2 : ℝ) - 1 = 1 by norm_num, inv_one, one_mul] at H
  simpa only [one_div, inv_pow, div_eq_mul_inv, mul_comm, one_mul] using H

private theorem head_zero (a : ℕ) (x : ℝ) (hx : 0 ≤ x) (hupper : (2 : ℝ) ^ a * x < 2)
    (d : ℕ) (hd : d < a) : ⌊(2 : ℝ) ^ d * x⌋ = 0 := by
  have hn : 0 < 2 ^ a - 1 := by
    have H := Nat.lt_two_pow_self (n := a)
    omega
  exact MersenneDyadicSupportLines.scaling_floors a (fun _ => x)
    (fun _ => ⟨hx, hupper⟩) ⟨0, hn⟩ d hd

private theorem small_tail (a : ℕ) (x δ : ℝ)
    (hsmall : (2 : ℝ) ^ a * x < 1)
    (hz : 1 - (2 : ℝ) ^ a * x ≤ δ) (hδ : (2 : ℝ) ^ a * δ ≤ 2) :
    (2 - 2 / (2 : ℝ) ^ a - (a : ℝ) * δ) / (2 : ℝ) ^ a ≤
      ∑ j ∈ Finset.range a, term x (a + j) := by
  have hB : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have floors (j : ℕ) (hj : j < a) :
      ⌊(2 : ℝ) ^ (a + j) * x⌋ = (2 : ℤ) ^ j - 1 := by
    apply Int.floor_eq_iff.mpr
    have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show j + 1 ≤ a by omega)
    rw [pow_succ] at H
    have hδ0 : 0 ≤ δ := by linarith
    have H1 := mul_le_mul_of_nonneg_right H hδ0
    have H2 := mul_le_mul_of_nonneg_left hz (by positivity : (0 : ℝ) ≤ 2 ^ j)
    have H3 := mul_lt_mul_of_pos_left hsmall (by positivity : (0 : ℝ) < 2 ^ j)
    rw [pow_add]
    push_cast
    constructor <;> nlinarith
  have terms (j : ℕ) (hj : j ∈ Finset.range a) : term x (a + j) =
      ((1 : ℝ) / (2 : ℝ) ^ j - (1 - (2 : ℝ) ^ a * x)) / (2 : ℝ) ^ a := by
    dsimp only
    rw [floors j (Finset.mem_range.mp hj), pow_add]
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun j hj => terms j hj)]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, inverse_geometric]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  apply div_le_div_of_nonneg_right _ hB.le
  have H := mul_le_mul_of_nonneg_left hz (by positivity : (0 : ℝ) ≤ a)
  linarith

private theorem near_boundary (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (t : ℝ) (ht : ∀ i, t ≤ p i)
    (htlo : ((2 : ℝ) ^ a - 2) / ((2 : ℝ) ^ a) ^ 2 < t)
    (hthi : t ≤ ((2 : ℝ) ^ a - 1) / ((2 : ℝ) ^ a) ^ 2) :
    ((2 : ℝ) ^ a * ((a : ℝ) + 2) + 2 * ((2 : ℝ) ^ a) ^ 2) * t -
        2 * ((2 : ℝ) ^ a - 1) ≤ cost p := by
  classical
  let B : ℝ := (2 : ℝ) ^ a
  let δ : ℝ := 1 - B * t
  let S := Finset.univ.filter (fun i => B * p i < 1)
  let n : ℝ := S.card
  have hB : 0 < B := by dsimp [B]; positivity
  have hB8 : 8 ≤ B := by
    have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at H
    exact H
  have haB : (a : ℝ) + 1 ≤ B := by
    have H := Nat.lt_two_pow_self (n:= a)
    dsimp [B]
    exact_mod_cast (show a + 1 ≤ 2 ^ a by omega)
  have hcard : ((2 ^ a + 1 : ℕ) : ℝ) = B + 1 := by dsimp [B]; norm_cast
  have hδlo : 1 ≤ B * δ := by
    change t ≤ (B - 1) / B ^ 2 at hthi
    have H := (le_div_iff₀ (sq_pos_of_pos hB)).mp hthi
    dsimp [δ]
    nlinarith
  have hδhi : B * δ < 2 := by
    change (B - 2) / B ^ 2 < t at htlo
    have H := (div_lt_iff₀ (sq_pos_of_pos hB)).mp htlo
    dsimp [δ]
    nlinarith
  have hδ0 : 0 < δ := by nlinarith
  have atomU (i : Fin (2 ^ a + 1)) : B * p i < 2 := by
    have H := atom_upper p hs t ht i
    rw [hcard] at H
    have H' := mul_le_mul_of_nonneg_left H hB.le
    dsimp [δ] at hδhi
    nlinarith
  have deficit_sum : ∑ i, (1 - B * p i) = 1 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, hs, mul_one, hcard]
    ring
  have deficit_le : 1 ≤ n * δ := by
    have all_le : ∑ i, (1 - B * p i) ≤ ∑ i ∈ S, (1 - B * p i) := by
      have H : ∑ i ∈ S, -(1 - B * p i) ≤ ∑ i, -(1 - B * p i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
        linarith
      simp only [Finset.sum_neg_distrib] at H
      linarith
    have each_le : ∑ i ∈ S, (1 - B * p i) ≤ ∑ _i ∈ S, δ := by
      apply Finset.sum_le_sum
      intro i _
      have H := mul_le_mul_of_nonneg_left (ht i) hB.le
      dsimp [δ]
      linarith
    rw [deficit_sum] at all_le
    simp only [Finset.sum_const, nsmul_eq_mul] at each_le
    exact all_le.trans each_le
  have n0 : 0 ≤ n := by dsimp [n]; positivity
  let k : ℝ := 2 - 2 / B - (a : ℝ) * δ
  have k0 : 0 ≤ k := by
    have H := mul_le_mul_of_nonneg_right haB hδ0.le
    have H' := mul_nonneg (by linarith : 0 ≤ B - (a : ℝ) - 1) hδ0.le
    have H'' : (a : ℝ) * δ ≤ 2 - 2 / B := by
      have E := mul_le_mul_of_nonneg_left hδhi.le (by positivity : (0 : ℝ) ≤ a)
      have hbδ : B * δ < 2 := hδhi
      -- Algebra with a+1 <= B ensures positivity of the tail coefficient.
      have aid : (a : ℝ) * δ * B = (a : ℝ) * (B * δ) := by ring
      have bound : (a : ℝ) * δ * B ≤ 2 * (B - 1) := by rw [aid]; nlinarith
      have eq : (2 - 2 / B) * B = 2 * (B - 1) := by field_simp
      nlinarith
    dsimp [k]
    linarith
  have tail_bound : n * k / B ≤ ∑ i, ∑ j ∈ Finset.range a, term (p i) (a + j) := by
    calc
      _ = ∑ _i ∈ S, k / B := by simp [n, Finset.sum_const, nsmul_eq_mul, mul_div_assoc]
      _ ≤ ∑ i ∈ S, ∑ j ∈ Finset.range a, term (p i) (a + j) := by
        apply Finset.sum_le_sum
        intro i hi
        have hsmall : (2 : ℝ) ^ a * p i < 1 := by
          simpa [S, B] using (Finset.mem_filter.mp hi).2
        have H := mul_le_mul_of_nonneg_left (ht i) hB.le
        have hz : 1 - (2 : ℝ) ^ a * p i ≤ δ := by change 1 - B * p i ≤ δ; dsimp [δ]; linarith
        exact small_tail a (p i) δ hsmall hz hδhi.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => Finset.sum_nonneg (fun j _ => term_nonneg (p i) (a + j)))
  have head : ∑ i, ∑ d ∈ Finset.range a, term (p i) d = (a : ℝ) := by
    have terms (i : Fin (2 ^ a + 1)) (d : ℕ) (hd : d ∈ Finset.range a) : term (p i) d = p i := by
      simp [head_zero a (p i) (hp i) (atomU i) d (Finset.mem_range.mp hd)]
    simp_rw [Finset.sum_congr rfl (fun d hd => terms _ d hd)]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, hs, mul_one]
  have total_lower : (a : ℝ) + n * k / B ≤ cost p := by
    have H := prefix_le p hs (a + a)
    simp only [Finset.sum_range_add, Finset.sum_add_distrib] at H
    rw [head] at H
    linarith
  have algebra : 4 - (2 * B + (a : ℝ) + 2) * δ ≤ n * k / B := by
    have H := mul_le_mul_of_nonneg_left deficit_le k0
    have poly : 0 ≤ (B * δ - 1) * ((2 * B + (a : ℝ) + 2) * (B * δ) - 2 * (B - 1)) := by
      apply mul_nonneg (by linarith)
      have H2 := mul_le_mul_of_nonneg_left hδlo (by positivity : 0 ≤ 2 * B + (a : ℝ) + 2)
      linarith
    have identity : k - B * δ * (4 - (2 * B + (a : ℝ) + 2) * δ) =
        ((B * δ - 1) * ((2 * B + (a : ℝ) + 2) * (B * δ) - 2 * (B - 1))) / B := by
      dsimp [k]
      field_simp
      ring
    have nonnegative : 0 ≤ k - B * δ * (4 - (2 * B + (a : ℝ) + 2) * δ) := by
      rw [identity]
      exact div_nonneg poly hB.le
    apply (le_div_iff₀ hB).mpr
    nlinarith
  have target_identity : (B * ((a : ℝ) + 2) + 2 * B ^ 2) * t - 2 * (B - 1) =
      (a : ℝ) + 4 - (2 * B + (a : ℝ) + 2) * δ := by dsimp [δ]; ring
  change (B * ((a : ℝ) + 2) + 2 * B ^ 2) * t - 2 * (B - 1) ≤ cost p
  rw [target_identity]
  linarith

private theorem middle_prefix (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (t : ℝ) (ht : ∀ i, t ≤ p i)
    (htlo : ((2 : ℝ) ^ a - 3) / ((2 : ℝ) ^ a) ^ 2 < t)
    (hthi : t ≤ ((2 : ℝ) ^ a - 2) / ((2 : ℝ) ^ a) ^ 2) :
    (a : ℝ) - 2 / (2 : ℝ) ^ a ≤ cost p := by
  classical
  let B : ℝ := (2 : ℝ) ^ a
  have hB : 0 < B := by dsimp [B]; positivity
  have hB8 : 8 ≤ B := by
    have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at H
    exact H
  have hcard : ((2 ^ a + 1 : ℕ) : ℝ) = B + 1 := by dsimp [B]; norm_cast
  have half : (2 : ℝ) ^ (a - 1) = B / 2 := by
    have H : (2 : ℝ) ^ (a - 1) * 2 = B := by
      rw [← pow_succ, show a - 1 + 1 = a by omega]
    linarith
  have tlo : B ^ 2 * t > B - 3 := by
    change (B - 3) / B ^ 2 < t at htlo
    have H := (div_lt_iff₀ (sq_pos_of_pos hB)).mp htlo
    nlinarith
  have tupper : B * t < 1 := by
    change t ≤ (B - 2) / B ^ 2 at hthi
    have H := (le_div_iff₀ (sq_pos_of_pos hB)).mp hthi
    nlinarith
  have atomU (i : Fin (2 ^ a + 1)) : B * p i < 3 := by
    have H := atom_upper p hs t ht i
    rw [hcard] at H
    have H' := mul_le_mul_of_nonneg_left H hB.le
    nlinarith
  have heads (i : Fin (2 ^ a + 1)) (d : ℕ) (hd : d < a - 1) : ⌊(2 : ℝ) ^ d * p i⌋=0 := by
    apply head_zero (a - 1) (p i) (hp i) ?_ d hd
    rw [half]
    have H := atomU i
    nlinarith
  have floorU (i : Fin (2 ^ a + 1)) : ⌊(2 : ℝ) ^ (a - 1) * p i⌋ ≤ 1 := by
    have H : (2 : ℝ) ^ (a - 1) * p i < 2 := by rw [half]; nlinarith [atomU i]
    have H' : ⌊(2 : ℝ) ^ (a - 1) * p i⌋ < (2 : ℤ) := Int.floor_lt.mpr (by simpa using H)
    omega
  have floorZ (i : Fin (2 ^ a + 1)) (hi : p i < 2 / B) : ⌊(2 : ℝ) ^ (a - 1) * p i⌋=0 := by
    apply Int.floor_eq_zero_iff.mpr
    refine ⟨mul_nonneg (by positivity) (hp i), ?_⟩
    rw [half]
    have H := (lt_div_iff₀ hB).mp hi
    nlinarith
  have floor_sum : ∑ i, ⌊(2 : ℝ) ^ (a - 1) * p i⌋ ≤ (1 : ℤ) := by
    by_cases H : ∃ i, 2 / B ≤ p i
    · obtain ⟨i, hi⟩ := H
      have other (j : Fin (2 ^ a + 1)) (hj : j ≠ i) : p j < 2 / B := by
        by_contra HJ
        have hj' : 2 / B ≤ p j := le_of_not_gt HJ
        have T := Finset.add_le_sum (s:= Finset.univ) (f:= fun k => p k - t)
          (fun k _ => sub_nonneg.mpr (ht k)) (Finset.mem_univ i) (Finset.mem_univ j) (Ne.symm hj)
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, hs, hcard] at T
        have Hi := (div_le_iff₀ hB).mp hi
        have Hj := (div_le_iff₀ hB).mp hj'
        have HT := mul_le_mul_of_nonneg_left T hB.le
        nlinarith
      rw [Finset.sum_eq_single i (fun j _ hj => floorZ j (other j hj)) (by simp)]
      exact floorU i
    · have allZ (i : Fin (2 ^ a + 1)) : ⌊(2 : ℝ) ^ (a - 1) * p i⌋=0 :=
        floorZ i (lt_of_not_ge (fun hi => H ⟨i, hi⟩))
      simp only [allZ, Finset.sum_const_zero]
      norm_num
  have first : ∑ i, ∑ d ∈ Finset.range (a - 1), term (p i) d = ((a - 1 : ℕ) : ℝ) := by
    have T (i : Fin (2 ^ a + 1)) (d : ℕ) (hd : d ∈ Finset.range (a - 1)) : term (p i) d = p i := by
      simp [heads i d (Finset.mem_range.mp hd)]
    simp_rw [Finset.sum_congr rfl (fun d hd => T _ d hd)]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, hs, mul_one]
  have last : 1 - 2 / B ≤ ∑ i, term (p i) (a - 1) := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div, hs, half]
    have HF : (∑ i, (⌊(2 : ℝ) ^ (a - 1) * p i⌋:ℝ)) ≤ 1 := by exact_mod_cast floor_sum
    have HD := div_le_div_of_nonneg_right HF (show 0 ≤ B / 2 by positivity)
    have HE : (1 : ℝ) / (B / 2) = 2 / B := by field_simp
    rw [HE, half] at HD
    linarith
  have H := prefix_le p hs ((a - 1) + 1)
  simp only [Finset.sum_range_succ, Finset.sum_add_distrib] at H
  rw [first] at H
  have acast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    norm_cast
    exact Nat.cast_sub (show 1 ≤ a by omega)
  rw [acast] at H
  change (a : ℝ) - 2 / B ≤ cost p
  linarith

/-- The full low-side estimate, with an arbitrary supplied lower bound on all atoms. -/
private theorem low_side_lower (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (t : ℝ) (ht : ∀ i, t ≤ p i)
    (hthi : t ≤ ((2 : ℝ) ^ a - 1) / ((2 : ℝ) ^ a) ^ 2) :
    ((2 : ℝ) ^ a * ((a : ℝ) + 2) + 2 * ((2 : ℝ) ^ a) ^ 2) * t -
        2 * ((2 : ℝ) ^ a - 1) ≤ cost p := by
  let B : ℝ := (2 : ℝ) ^ a
  have hB : 0 < B := by dsimp [B]; positivity
  have hB8 : 8 ≤ B := by
    have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at H
    exact H
  change t ≤ (B - 1) / B ^ 2 at hthi
  change (B * ((a : ℝ) + 2) + 2 * B ^ 2) * t - 2 * (B - 1) ≤ cost p
  by_cases hlo : t ≤ (B - 3) / B ^ 2
  · have H := mersenne_comparison a ha p hp hs t ht
    change (((a : ℝ) + 2) * B - 2) * t - 2 ≤ cost p at H
    have T := (le_div_iff₀ (sq_pos_of_pos hB)).mp hlo
    have tt : t ≤ 1 := by
      have H0 : B ^ 2 ≥ B := by nlinarith
      have H1 : t ≤ (B - 3) / B ^ 2 := hlo
      have H2 : (B - 3) / B ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hB)).mpr (by nlinarith)
      exact H1.trans H2
    nlinarith
  · have hlo' : (B - 3) / B ^ 2 < t := lt_of_not_ge hlo
    by_cases hmid : t ≤ (B - 2) / B ^ 2
    · have H := middle_prefix a ha p hp hs t ht hlo' hmid
      change (a : ℝ) - 2 / B ≤ cost p at H
      have T := (le_div_iff₀ (sq_pos_of_pos hB)).mp hmid
      have hc : 0 ≤ B * ((a : ℝ) + 2) + 2 * B ^ 2 := by positivity
      have HI := mul_le_mul_of_nonneg_left hmid hc
      have HE : (B * ((a : ℝ) + 2) + 2 * B ^ 2) * ((B - 2) / B ^ 2) - 2 * (B - 1) =
          (a : ℝ) - 2 * ((a : ℝ) + 2) / B := by field_simp; ring
      have Hdiv : 2 / B ≤ 2 * ((a : ℝ) + 2) / B := by
        apply div_le_div_of_nonneg_right _ hB.le
        nlinarith
      have HI' := sub_le_sub_right HI (2 * (B - 1))
      rw [HE] at HI'
      linarith
    · exact near_boundary a ha p hp hs t ht (lt_of_not_ge hmid) hthi

/-- The second supporting inequality on the low interval of the complementary simplex. -/
theorem result (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    let t := Finset.univ.inf' (by
      exact ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩) p
    t ≤ ((2 : ℝ) ^ a - 1) / ((2 : ℝ) ^ a) ^ 2 →
      ((2 : ℝ) ^ a * ((a : ℝ) + 2) + 2 * ((2 : ℝ) ^ a) ^ 2) * t -
        2 * ((2 : ℝ) ^ a - 1) ≤ cost p := by
  classical
  dsimp only
  intro hlow
  exact low_side_lower a ha p hp hs _
    (fun i => Finset.inf'_le _ (Finset.mem_univ i)) hlow


end D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
