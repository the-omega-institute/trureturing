/- GID: D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Global second support and strict high-side scaling for complementary dyadic real laws. -/

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

local notation "B" => (fun a : ℕ => (2 : ℝ) ^ a)
local notation "C" => (fun a : ℕ => B a * ((a : ℝ) + 2) + 2 * B a ^ 2)
local notation "d0" => (fun a : ℕ => 2 * (B a - 1))
local notation "t0" => (fun a : ℕ => (B a - 1) / B a ^ 2)
local notation "H0" => (fun a : ℕ => (a : ℝ) + 2 - a / B a - 2 / B a ^ 2)
local notation "mn" => (fun (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) =>
  Finset.univ.inf' Finset.univ_nonempty p)

/-- The affine high-side rescaling of a complementary dyadic law. -/
noncomputable def high_transform (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) :
    Fin (2 ^ a + 1) → ℝ := fun i => B a ^ 2 * p i - (B a - 1)

/-- The excess over the second affine support line. -/
noncomputable def support_gap (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) : ℝ :=
  cost p - C a * mn a p + d0 a

private theorem bpos (a : ℕ) : 0 < B a := by dsimp only; positivity
private theorem bcast (a : ℕ) : ((2 ^ a + 1 : ℕ) : ℝ) = B a + 1 := by simp
private theorem bge (a : ℕ) (ha : 3 ≤ a) : 8 ≤ B a := by
  have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
  norm_num at H
  exact H
private theorem mn_le (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) (i : Fin (2 ^ a + 1)) : mn a p ≤ p i :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem high_data (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hs : ∑ i, p i = 1) (ht : t0 a < mn a p) :
    (∀ i, 0 < high_transform a p i) ∧ (∑ i, high_transform a p i = 1) ∧
    (∀ i, t0 a < p i ∧ p i < 1 / B a) := by
  have hB := bpos a
  have hB8 := bge a ha
  have hmin (i : Fin (2 ^ a + 1)) := mn_le a p i
  have hut (i : Fin (2 ^ a + 1)) : p i ≤ 1 - B a * mn a p := by
    have H := atom_upper p hs (mn a p) (fun j => mn_le a p j) i
    simpa only [bcast, add_sub_cancel_right] using H
  have hstrict : B a - 1 < B a ^ 2 * mn a p := by
    simpa [mul_comm] using (div_lt_iff₀ (sq_pos_of_pos hB)).mp ht
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold high_transform
    have H := mul_le_mul_of_nonneg_left (hmin i) (sq_nonneg (B a))
    linarith
  · simp only [high_transform, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs,
      mul_one, bcast]
    ring
  · intro i
    refine ⟨ht.trans_le (hmin i), ?_⟩
    have H := hut i
    have HH := mul_le_mul_of_nonneg_left H hB.le
    apply (lt_div_iff₀ hB).mpr
    nlinarith

private theorem floor_head (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ)
    (hi : ∀ i, 0 ≤ p i ∧ p i < 1 / B a)
    (i : Fin (2 ^ a + 1)) (d : ℕ) (hd : d < a) :
    ⌊(2 : ℝ) ^ d * p i⌋ = 0 := by
  apply head_zero a (p i) (hi i).1 ?_ d hd
  have H := (lt_div_iff₀ (bpos a)).mp (hi i).2
  dsimp only at H ⊢
  nlinarith

private theorem floor_middle (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ)
    (hi : ∀ i, t0 a < p i ∧ p i < 1 / B a)
    (i : Fin (2 ^ a + 1)) (j : ℕ) (hj : j < a) :
    ⌊(2 : ℝ) ^ (a + j) * p i⌋ = (2 : ℤ) ^ j - 1 := by
  have hB := bpos a
  have hJ : (2 : ℝ) ^ j < B a := by
    exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hj
  have hp := (div_lt_iff₀ (sq_pos_of_pos hB)).mp (hi i).1
  have hu := (lt_div_iff₀ hB).mp (hi i).2
  have lo := mul_pos (by positivity : (0 : ℝ) < 2 ^ j)
    (show 0 < B a ^ 2 * p i - (B a - 1) by linarith)
  have gap := mul_pos hB (sub_pos.mpr hJ)
  have hB2 := sq_pos_of_pos hB
  apply Int.floor_eq_iff.mpr
  push_cast
  rw [pow_add]
  change (2 : ℝ) ^ j - 1 ≤ B a * (2 : ℝ) ^ j * p i ∧
    B a * (2 : ℝ) ^ j * p i < (2 : ℝ) ^ j - 1 + 1
  constructor
  · nlinarith
  · nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]

private theorem floor_tail (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ)
    (i : Fin (2 ^ a + 1)) (e : ℕ) :
    ⌊(2 : ℝ) ^ (e + a * 2) * p i⌋ =
      ⌊(2 : ℝ) ^ e * high_transform a p i⌋ + ((2 : ℤ) ^ a - 1) * (2 : ℤ) ^ e := by
  have E : (2 : ℝ) ^ (e + a * 2) * p i =
      (2 : ℝ) ^ e * high_transform a p i +
        ((((2 : ℤ) ^ a - 1) * (2 : ℤ) ^ e : ℤ) : ℝ) := by
    simp only [high_transform, pow_add, pow_mul]
    push_cast
    ring
  rw [E, Int.floor_add_intCast]

private theorem residual_tail (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) (e : ℕ) :
    DyadicSupportLines.residual p (e + a * 2) = DyadicSupportLines.residual (high_transform a p) e := by
  unfold DyadicSupportLines.residual
  simp_rw [floor_tail]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, pow_add, pow_mul]
  push_cast
  ring

private theorem head_sum (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ)
    (hi : ∀ i, t0 a < p i ∧ p i < 1 / B a) (ha : 3 ≤ a) :
    ∑ d ∈ Finset.range (2 * a), DyadicSupportLines.residual p d / (2 : ℝ) ^ d = H0 a := by
  have hB := bpos a
  have htpos : 0 < t0 a := div_pos (by have := bge a ha; linarith) (sq_pos_of_pos hB)
  have hz := floor_head a p (fun i => ⟨(htpos.trans (hi i).1).le, (hi i).2⟩)
  have first : ∑ d ∈ Finset.range a, DyadicSupportLines.residual p d / (2 : ℝ) ^ d = a := by
    have layer_term (d : ℕ) (hd : d ∈ Finset.range a) : DyadicSupportLines.residual p d / (2 : ℝ) ^ d = 1 := by
      simp only [DyadicSupportLines.residual, hz _ d (Finset.mem_range.mp hd), Int.cast_zero,
        Finset.sum_const_zero, sub_zero]
      exact div_self (by positivity)
    rw [Finset.sum_congr rfl (fun d hd => layer_term d hd)]
    simp
  have mid (j : ℕ) (hj : j ∈ Finset.range a) :
      DyadicSupportLines.residual p (a + j) / (2 : ℝ) ^ (a + j) =
        (B a + 1) / B a * (1 / 2 : ℝ) ^ j - 1 / B a := by
    simp_rw [DyadicSupportLines.residual,
      floor_middle a p hi _ j (Finset.mem_range.mp hj)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_add]
    push_cast
    have HP : (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j := by simp
    rw [HP]
    change (B a * (2 : ℝ) ^ j - (B a + 1) * ((2 : ℝ) ^ j - 1)) /
      (B a * (2 : ℝ) ^ j) = _
    field_simp
    ring
  have geo : ∑ j ∈ Finset.range a, (1 / 2 : ℝ) ^ j = 2 - 2 / B a := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    simp only [div_pow, one_pow]
    ring
  rw [show 2 * a = a + a by omega, Finset.sum_range_add, first]
  have second : ∑ j ∈ Finset.range a, DyadicSupportLines.residual p (a + j) / (2 : ℝ) ^ (a + j) =
      (B a + 1) / B a * (2 - 2 / B a) - a / B a := by
    rw [Finset.sum_congr rfl (fun j hj => mid j hj)]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, geo, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  rw [second]
  dsimp only
  field_simp
  ring

private theorem scaling (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hs : ∑ i, p i = 1) (ht : t0 a < mn a p) :
    (∀ i, 0 < high_transform a p i) ∧ (∑ i, high_transform a p i = 1) ∧
      cost p = H0 a + cost (high_transform a p) / B a ^ 2 := by
  have H := high_data a ha p hs ht
  have tail (e : ℕ) : DyadicSupportLines.residual p (e + a * 2) / (2 : ℝ) ^ (e + a * 2) =
      (DyadicSupportLines.residual (high_transform a p) e / (2 : ℝ) ^ e) / B a ^ 2 := by
    rw [residual_tail, pow_add, pow_mul]
    dsimp only
    ring
  have tails : (∑' e, DyadicSupportLines.residual p (e + a * 2) / (2 : ℝ) ^ (e + a * 2)) =
      cost (high_transform a p) / B a ^ 2 := by
    simp_rw [tail]
    exact tsum_div_const
  have split := Summable.sum_add_tsum_nat_add (2 * a) (law_data _ p hs).2.1
  have tails' : (∑' e, DyadicSupportLines.residual p (e + 2 * a) / (2 : ℝ) ^ (e + 2 * a)) = cost (high_transform a p) / B a ^ 2 := by
    simpa [Nat.mul_comm] using tails
  rw [head_sum a p H.2.2 ha, tails'] at split
  exact ⟨H.1, H.2.1, split.symm⟩


private theorem min_q (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) :
    mn a (high_transform a p) = B a ^ 2 * mn a p - (B a - 1) := by
  let f : ℝ →o ℝ := ⟨fun x => B a ^ 2 * x - (B a - 1),
    fun _ _ h => sub_le_sub_right (mul_le_mul_of_nonneg_left h (sq_nonneg _)) _⟩
  exact (map_finset_inf' f _ p).symm

private theorem d_scaling (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hs : ∑ i, p i = 1) (ht : t0 a < mn a p) :
    support_gap a p = support_gap a (high_transform a p) / B a ^ 2 := by
  have H := (scaling a ha p hs ht).2.2
  unfold support_gap
  rw [H, min_q]
  dsimp only
  field_simp [(bpos a).ne']
  ring

/-- Strictly high laws remain positive and normalized, with exact cost and gap scaling. -/
theorem high_scaling (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hs : ∑ i, p i = 1) (ht : t0 a < mn a p) :
    (∀ i, 0 < high_transform a p i) ∧ (∑ i, high_transform a p i = 1) ∧
      cost p = H0 a + cost (high_transform a p) / B a ^ 2 ∧
      support_gap a p = support_gap a (high_transform a p) / B a ^ 2 := by
  have H := scaling a ha p hs ht
  exact ⟨H.1, H.2.1, H.2.2, d_scaling a ha p hs ht⟩

private theorem minimum_upper (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) (hs : ∑ i, p i = 1) :
    mn a p ≤ 1 / (B a + 1) := by
  have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => mn_le a p i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    bcast, hs] at H
  exact (le_div_iff₀ (by have := bpos a; linarith)).mpr (by simpa [mul_comm] using H)

private theorem uniform_of_min (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) (hs : ∑ i, p i = 1)
    (ht : mn a p = 1 / (B a + 1)) : p = fun _ => 1 / (B a + 1) := by
  classical
  have csum : ∑ _i : Fin (2 ^ a + 1), (1 / (B a + 1)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, bcast]
    exact mul_one_div_cancel (by have := bpos a; linarith)
  ext i
  have H := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (fun j _ => show 1 / (B a + 1) ≤ p j by rw [← ht]; exact mn_le a p j)).mp
    (csum.trans hs.symm) i (Finset.mem_univ i)
  exact H.symm

private theorem fixed (a : ℕ) :
    high_transform a (fun _ => 1 / (B a + 1)) = fun _ => 1 / (B a + 1) := by
  ext i
  unfold high_transform
  field_simp [show B a + 1 ≠ 0 by have := bpos a; linarith]
  ring

private theorem mn_const (a : ℕ) (c : ℝ) : mn a (fun _ => c) = c := by
  simp only [Finset.inf'_const]

private theorem uniform_high (a : ℕ) :
    t0 a < mn a (fun _ => 1 / (B a + 1)) := by
  rw [mn_const]
  dsimp only
  apply (div_lt_div_iff₀ (sq_pos_of_pos (bpos a)) (by have := bpos a; linarith)).mpr
  nlinarith

/-- The uniform law has zero excess over the second supporting line. -/
theorem uniform_gap_zero (a : ℕ) (ha : 3 ≤ a) :
    support_gap a (fun _ => 1 / (B a + 1)) = 0 := by
  have hs : ∑ _i : Fin (2 ^ a + 1), (1 / (B a + 1)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, bcast]
    exact mul_one_div_cancel (by have := bpos a; linarith)
  have H := (high_scaling a ha _ hs (uniform_high a)).2.2.2
  rw [fixed] at H
  have HE := (eq_div_iff (sq_pos_of_pos (bpos a)).ne').mp H
  have Hne : B a ^ 2 - 1 ≠ 0 := by have := bge a ha; nlinarith
  have HM : (B a ^ 2 - 1) * support_gap a (fun _ => 1 / (B a + 1)) = 0 := by linarith
  exact (mul_eq_zero.mp HM).resolve_left Hne

/-- The closed-form orbit of the high-side affine transformation. -/
noncomputable def scaled_iterate (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) (k : ℕ) :
    Fin (2 ^ a + 1) → ℝ :=
  fun i => 1 / (B a + 1) + (B a ^ 2) ^ k * (p i - 1 / (B a + 1))
local notation "T" => (fun (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) (k : ℕ) =>
  1 / (B a + 1) - (B a ^ 2) ^ k * (1 / (B a + 1) - mn a p))

private theorem r_zero (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) :
    scaled_iterate a p 0 = p := by
  ext i
  simp [scaled_iterate]
private theorem r_next (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) (k : ℕ) :
    scaled_iterate a p (k + 1) = high_transform a (scaled_iterate a p k) := by
  ext i
  unfold scaled_iterate high_transform
  rw [pow_succ]
  field_simp [show B a + 1 ≠ 0 by have := bpos a; linarith]
  ring
private theorem r_sum (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) (hs : ∑ i, p i = 1) (k : ℕ) :
    ∑ i, scaled_iterate a p k i = 1 := by
  have csum : ∑ _i : Fin (2 ^ a + 1), (1 / (B a + 1)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, bcast]
    exact mul_one_div_cancel (by have := bpos a; linarith)
  simp only [scaled_iterate, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    csum, hs, sub_self, mul_zero, add_zero]
private theorem r_min (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) (k : ℕ) :
    mn a (scaled_iterate a p k) = T a p k := by
  let f : ℝ →o ℝ := ⟨fun x => 1 / (B a + 1) + (B a ^ 2) ^ k *
    (x - 1 / (B a + 1)), fun _ _ h => add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (sub_le_sub_right h _) (pow_nonneg (sq_nonneg _) k))⟩
  have H := (map_finset_inf' f (Finset.univ_nonempty :
    (Finset.univ : Finset (Fin (2 ^ a + 1))).Nonempty) p).symm
  change mn a (scaled_iterate a p k) =
    1 / (B a + 1) + (B a ^ 2) ^ k * (mn a p - 1 / (B a + 1)) at H
  rw [H]
  ring

/-- Every nonuniform strictly high law has a finite positive first exit to the low interval. -/
theorem finite_exit (a : ℕ) (ha : 3 ≤ a) (p : Fin (2 ^ a + 1) → ℝ)
    (hs : ∑ i, p i = 1) (ht : t0 a < mn a p)
    (hnu : p ≠ fun _ => 1 / (B a + 1)) :
    ∃ n : ℕ, 0 < n ∧ (∀ k < n, t0 a < mn a (scaled_iterate a p k)) ∧
      (∀ i, 0 < scaled_iterate a p n i) ∧ (∑ i, scaled_iterate a p n i = 1) ∧
      0 < mn a (scaled_iterate a p n) ∧ mn a (scaled_iterate a p n) ≤ t0 a ∧
      support_gap a p = support_gap a (scaled_iterate a p n) / (B a ^ 2) ^ n := by
  have hB := bpos a
  have hB8 := bge a ha
  have hlt : mn a p < 1 / (B a + 1) := by
    refine lt_of_le_of_ne (minimum_upper a p hs) ?_
    intro H
    exact hnu (uniform_of_min a p hs H)
  have gap : 0 < 1 / (B a + 1) - mn a p := sub_pos.mpr hlt
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
    ((1 / (B a + 1) - t0 a) / (1 / (B a + 1) - mn a p))
    (show 1 < B a ^ 2 by nlinarith)
  have ex : ∃ j : ℕ, T a p j ≤ t0 a := by
    refine ⟨j, ?_⟩
    have H := (div_lt_iff₀ gap).mp hj
    dsimp only
    linarith
  let n := Nat.find ex
  have hn : T a p n ≤ t0 a := Nat.find_spec ex
  have before (k : ℕ) (hk : k < n) : t0 a < mn a (scaled_iterate a p k) := by
    rw [r_min]
    exact lt_of_not_ge (Nat.find_min ex hk)
  have hnpos : 0 < n := by
    by_contra H
    have HZ : n = 0 := by omega
    have HE : T a p 0 = mn a p := by simp
    rw [HZ, HE] at hn
    linarith
  have propagated (k : ℕ) (hk : k ≤ n) :
      (∀ i, 0 < scaled_iterate a p k i) ∧
        support_gap a p = support_gap a (scaled_iterate a p k) / (B a ^ 2) ^ k := by
    induction k with
    | zero =>
      rw [r_zero]
      refine ⟨?_, by simp⟩
      intro i
      have htpos : 0 < t0 a := div_pos (by linarith) (sq_pos_of_pos hB)
      exact htpos.trans (ht.trans_le (mn_le a p i))
    | succ k ih =>
      have hklt : k < n := by omega
      have HD := high_scaling a ha (scaled_iterate a p k) (r_sum a p hs k) (before k hklt)
      have HE := HD.2.2.2
      have ih' := ih (by omega)
      rw [r_next]
      refine ⟨HD.1, ?_⟩
      rw [ih'.2, HE, pow_succ]
      field_simp [hB.ne']
      rw [pow_succ]
      ring
  have HP := propagated n le_rfl
  refine ⟨n, hnpos, before, HP.1, r_sum a p hs n, ?_, ?_, HP.2⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun i _ => HP.1 i)
  · rwa [r_min]

/-- The second affine support holds on the entire real probability simplex. -/
theorem global_support (a : ℕ) (ha : 3 ≤ a)
    (p : Fin (2 ^ a + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    C a * mn a p - d0 a ≤ cost p := by
  by_cases hlo : mn a p ≤ t0 a
  · exact result a ha p hp hs hlo
  by_cases hu : p = fun _ => 1 / (B a + 1)
  · rw [hu]
    have H := uniform_gap_zero a ha
    unfold support_gap at H
    linarith
  obtain ⟨n, _, _, hpn, hsn, _, htn, hd⟩ := finite_exit a ha p hs (lt_of_not_ge hlo) hu
  have HL := result a ha (scaled_iterate a p n) (fun i => (hpn i).le) hsn htn
  have HD : 0 ≤ support_gap a (scaled_iterate a p n) := by unfold support_gap; linarith
  have H : 0 ≤ support_gap a p := by rw [hd]; positivity
  unfold support_gap at H
  linarith


end D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
