/- GID: D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder
   mirror-E: none(waiver:source-fixed-window-consumer)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer]
   utility: none
   digest: Finite elementary coefficients and ordered product residuals supply the complete actual-source fixed-window consumer. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow

open scoped BigOperators

def fallingReal (j k : ℕ) : ℝ := (j.descFactorial k : ℝ)

def elementarySymmetric (r j : ℕ) : ℝ :=
  ∑ s ∈ (Finset.range j).powersetCard r, ∏ i ∈ s, (i : ℝ)

def correctionCoeff : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => 0
  | r + 1, k + 2 =>
      (((k + 1 : ℕ) : ℝ) * correctionCoeff r (k + 1) + correctionCoeff r k) /
        ((k + 2 : ℕ) : ℝ)

private theorem correctionCoeff_nonneg (r k : ℕ) : 0 ≤ correctionCoeff r k := by
  induction r generalizing k with
  | zero => cases k <;> simp [correctionCoeff]
  | succ r ih =>
    rcases k with _ | _ | k
    · simp [correctionCoeff]
    · simp [correctionCoeff]
    · exact div_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih _)) (ih _))
        (Nat.cast_nonneg _)

private theorem correctionCoeff_support (r k : ℕ) (hk : correctionCoeff r k ≠ 0) :
    r = 0 ∧ k = 0 ∨ r + 1 ≤ k ∧ k ≤ 2 * r := by
  induction r generalizing k with
  | zero =>
    cases k with
    | zero => exact Or.inl ⟨rfl, rfl⟩
    | succ k => exact False.elim (hk (by simp [correctionCoeff]))
  | succ r ih =>
    rcases k with _ | _ | k
    · exact False.elim (hk (by simp [correctionCoeff]))
    · exact False.elim (hk (by simp [correctionCoeff]))
    · have hp : correctionCoeff r (k + 1) ≠ 0 ∨ correctionCoeff r k ≠ 0 := by
        by_contra h
        push Not at h
        exact hk (by simp [correctionCoeff, h.1, h.2])
      rcases hp with h | h
      · rcases ih _ h with h | h <;> omega
      · rcases ih _ h with h | h <;> omega

private theorem correctionCoeff_above (r k : ℕ) (hk : 2 * r < k) :
    correctionCoeff r k = 0 := by
  by_contra h
  rcases correctionCoeff_support r k h with h | h <;> omega

private theorem correctionCoeff_top (r : ℕ) :
    correctionCoeff r (2 * r) = 1 / (2 ^ r * (r.factorial : ℝ)) := by
  induction r with
  | zero => norm_num [correctionCoeff]
  | succ r ih =>
    have hz := correctionCoeff_above r (2 * r + 1) (by omega)
    rw [show 2 * (r + 1) = 2 * r + 2 by omega, correctionCoeff, hz, mul_zero, zero_add, ih]
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp

private theorem elementary_zero (j : ℕ) : elementarySymmetric 0 j = 1 := by
  simp [elementarySymmetric]

private theorem elementary_succ (r j : ℕ) :
    elementarySymmetric (r + 1) (j + 1) =
      elementarySymmetric (r + 1) j + (j : ℝ) * elementarySymmetric r j := by
  classical
  have hj : j ∉ Finset.range j := by simp
  have hd : Disjoint ((Finset.range j).powersetCard (r + 1))
      (((Finset.range j).powersetCard r).image (insert j)) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    have hjmem : j ∈ Finset.range j :=
      (Finset.mem_powersetCard.mp hs).1 (Finset.mem_insert_self _ _)
    exact hj hjmem
  have hinj : Set.InjOn (fun s : Finset ℕ => insert j s)
      ((Finset.range j).powersetCard r : Set (Finset ℕ)) := by
    intro a ha b hb he
    have hja : j ∉ a := fun h => hj ((Finset.mem_powersetCard.mp ha).1 h)
    have hjb : j ∉ b := fun h => hj ((Finset.mem_powersetCard.mp hb).1 h)
    simpa [hja, hjb] using congrArg (fun s : Finset ℕ => s.erase j) he
  unfold elementarySymmetric
  rw [Finset.range_add_one, Finset.powersetCard_succ_insert hj, Finset.sum_union hd,
    Finset.sum_image hinj, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact Finset.prod_insert (fun h => hj ((Finset.mem_powersetCard.mp ha).1 h))

private theorem falling_increment (j k : ℕ) :
    fallingReal (j + 1) (k + 1) - fallingReal j (k + 1) =
      ((k + 1 : ℕ) : ℝ) * fallingReal j k := by
  unfold fallingReal
  rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
  by_cases hk : k ≤ j
  · rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk]
    push_cast
    ring
  · have hz : j.descFactorial k = 0 := Nat.descFactorial_of_lt (by omega)
    simp [hz]

private theorem falling_mul (j k : ℕ) :
    (j : ℝ) * fallingReal j k = fallingReal j (k + 1) + (k : ℝ) * fallingReal j k := by
  unfold fallingReal
  rw [Nat.descFactorial_succ]
  by_cases hk : k ≤ j
  · rw [Nat.cast_mul, Nat.cast_sub hk]
    ring
  · have hz : j.descFactorial k = 0 := Nat.descFactorial_of_lt (by omega)
    simp [hz]

def correctionSum (r j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 * r + 1), correctionCoeff r k * fallingReal j k

private theorem correctionSum_increment (r j : ℕ) :
    correctionSum (r + 1) (j + 1) - correctionSum (r + 1) j =
      (j : ℝ) * correctionSum r j := by
  have hcoeff (k : ℕ) : ((k + 2 : ℕ) : ℝ) * correctionCoeff (r + 1) (k + 2) =
      ((k + 1 : ℕ) : ℝ) * correctionCoeff r (k + 1) + correctionCoeff r k := by
    rw [correctionCoeff, mul_div_cancel₀ _ (by positivity)]
  have htop := correctionCoeff_above r (2 * r + 1) (by omega)
  have hdiff : correctionSum (r + 1) (j + 1) - correctionSum (r + 1) j =
      ∑ k ∈ Finset.range (2 * r + 1),
        (((k + 1 : ℕ) : ℝ) * correctionCoeff r (k + 1) + correctionCoeff r k) *
          fallingReal j (k + 1) := by
    unfold correctionSum
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [correctionCoeff, zero_mul, zero_add, add_zero]
    simp_rw [falling_increment]
    apply Finset.sum_congr rfl
    intro k _
    calc
      correctionCoeff (r + 1) (k + 2) *
          (((k + 2 : ℕ) : ℝ) * fallingReal j (k + 1)) =
        (((k + 2 : ℕ) : ℝ) * correctionCoeff (r + 1) (k + 2)) *
          fallingReal j (k + 1) := by ring
      _ = _ := by rw [hcoeff]
  let f : ℕ → ℝ := fun k => correctionCoeff r k * (k : ℝ) * fallingReal j k
  have hf0 : f 0 = 0 := by simp [f]
  have hftop : f (2 * r + 1) = 0 := by simp [f, htop]
  have hshift : (∑ k ∈ Finset.range (2 * r + 1),
      ((k + 1 : ℕ) : ℝ) * correctionCoeff r (k + 1) * fallingReal j (k + 1)) =
      ∑ k ∈ Finset.range (2 * r + 1), correctionCoeff r k * (k : ℝ) * fallingReal j k := by
    have hleft := Finset.sum_range_succ' f (2 * r + 1)
    have hright := Finset.sum_range_succ f (2 * r + 1)
    simp only [hf0, hftop, add_zero] at hleft hright
    simpa only [f, mul_comm, mul_left_comm, mul_assoc] using hleft.symm.trans hright
  rw [hdiff, correctionSum, Finset.mul_sum]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hshift]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_left_comm (j : ℝ), falling_mul]
  ring

private theorem elementary_at_zero (r : ℕ) : elementarySymmetric (r + 1) 0 = 0 := by
  unfold elementarySymmetric
  rw [Finset.range_zero, Finset.powersetCard_eq_empty.mpr (by simp), Finset.sum_empty]

private theorem elementary_falling_factorial (r j : ℕ) :
    elementarySymmetric r j = correctionSum r j := by
  have hall : ∀ j r, elementarySymmetric r j = correctionSum r j := by
    intro j
    induction j with
    | zero =>
      intro r
      cases r with
      | zero => simp [elementarySymmetric, correctionSum, correctionCoeff, fallingReal]
      | succ r =>
        rw [elementary_at_zero]
        unfold correctionSum
        rw [Finset.sum_range_succ']
        simp [correctionCoeff, fallingReal]
    | succ j ih =>
      intro r
      cases r with
      | zero => simp [elementary_zero, correctionSum, correctionCoeff, fallingReal]
      | succ r =>
        rw [elementary_succ, ih (r + 1), ih r]
        simpa only [add_comm] using (sub_eq_iff_eq_add.mp (correctionSum_increment r j)).symm
  exact hall j r

def bonferroniResidual (n K j : ℕ) : ℝ :=
  (n.descFactorial j : ℝ) / (n : ℝ) ^ j -
    ∑ r ∈ Finset.range (K + 1), (-1 : ℝ) ^ r * elementarySymmetric r j / (n : ℝ) ^ r

private theorem elementary_nonneg (r j : ℕ) : 0 ≤ elementarySymmetric r j := by
  unfold elementarySymmetric
  exact Finset.sum_nonneg fun s _ => Finset.prod_nonneg fun i _ => Nat.cast_nonneg i

private theorem elementary_initial_sum (r j : ℕ) :
    elementarySymmetric (r + 1) j =
      ∑ i ∈ Finset.range j, (i : ℝ) * elementarySymmetric r i := by
  induction j with
  | zero => simp [elementary_at_zero]
  | succ j ih => rw [elementary_succ, ih, Finset.sum_range_succ]

/- The nonnegative product estimate is obtained from the elementary subset
split and Mathlib's binomial lower bound.  It proves the same factorial
estimate as counting each selected subset once for each selected element. -/
private theorem elementary_factorial_bound (j r : ℕ) :
    (r.factorial : ℝ) * elementarySymmetric r j ≤
      (∑ i ∈ Finset.range j, (i : ℝ)) ^ r := by
  induction j generalizing r with
  | zero =>
    cases r with
    | zero => simp [elementarySymmetric]
    | succ r => simp [elementary_at_zero]
  | succ j ih =>
    cases r with
    | zero => simp [elementary_zero]
    | succ r =>
      let S : ℝ := ∑ i ∈ Finset.range j, (i : ℝ)
      have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Nat.cast_nonneg i
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hfirst := ih (r + 1)
      have hsecond := mul_le_mul_of_nonneg_left (ih r)
        (mul_nonneg (Nat.cast_nonneg (r + 1)) hj)
      have hbin := pow_add_mul_le_add_pow hS (by positivity : 0 ≤ 2 * S + j) (r + 1)
      rw [elementary_succ, Finset.sum_range_succ]
      calc
        _ = ((r + 1).factorial : ℝ) * elementarySymmetric (r + 1) j +
            ((r + 1 : ℕ) : ℝ) * (j : ℝ) *
              ((r.factorial : ℝ) * elementarySymmetric r j) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ S ^ (r + 1) + ((r + 1 : ℕ) : ℝ) * (j : ℝ) * S ^ r :=
          add_le_add hfirst hsecond
        _ ≤ (S + j) ^ (r + 1) := by
          simpa only [Nat.add_sub_cancel, mul_comm, mul_left_comm, mul_assoc] using hbin

private theorem index_sum_bound (j : ℕ) :
    (∑ i ∈ Finset.range j, (i : ℝ)) ≤ (j : ℝ) ^ 2 / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

private theorem elementary_bound (r j : ℕ) :
    elementarySymmetric r j ≤ (j : ℝ) ^ (2 * r) / (2 ^ r * (r.factorial : ℝ)) := by
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hs : 0 ≤ ∑ i ∈ Finset.range j, (i : ℝ) :=
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg i
  have h := (elementary_factorial_bound j r).trans
    (pow_le_pow_left₀ hs (index_sum_bound j) r)
  apply (le_div_iff₀ (mul_pos (by positivity) hf)).mpr
  have he : (j : ℝ) ^ (2 * r) = 2 ^ r * ((j : ℝ) ^ 2 / 2) ^ r := by
    rw [div_pow, pow_mul]
    field_simp
  calc
    _ = 2 ^ r * ((r.factorial : ℝ) * elementarySymmetric r j) := by ring
    _ ≤ 2 ^ r * ((j : ℝ) ^ 2 / 2) ^ r :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := he.symm

private theorem scaled_elementary_bound (n r j : ℕ) (hn : 1 ≤ n) :
    elementarySymmetric r j / (n : ℝ) ^ r ≤
      ((j : ℝ) ^ 2 / n) ^ r / 2 ^ r := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hf : (1 : ℝ) ≤ r.factorial := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos r))
  have hden : (2 : ℝ) ^ r ≤ 2 ^ r * (r.factorial : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf
      (show (0 : ℝ) ≤ 2 ^ r by positivity)
  calc
    _ ≤ ((j : ℝ) ^ (2 * r) / (2 ^ r * (r.factorial : ℝ))) / (n : ℝ) ^ r :=
      div_le_div_of_nonneg_right (elementary_bound r j) (by positivity)
    _ ≤ ((j : ℝ) ^ (2 * r) / 2 ^ r) / (n : ℝ) ^ r :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hden) (by positivity)
    _ = _ := by rw [div_pow, pow_mul]; ring

private theorem falling_normalized_product (n j : ℕ) (hn : 1 ≤ n) :
    (n.descFactorial j : ℝ) / (n : ℝ) ^ j =
      ∏ i ∈ Finset.range j, (1 - (i : ℝ) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [← descPochhammer_eval_eq_descFactorial ℝ n j,
    descPochhammer_eval_eq_prod_range]
  have hconst : (∏ _i ∈ Finset.range j, (n : ℝ)) = (n : ℝ) ^ j := by simp
  rw [← hconst, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  field_simp

/- Every recursive branch selects a strictly smaller next index.  Its leaf
is the full initial-segment product, including repeated zero factors. -/
private def orderedResidual (n : ℕ) : ℕ → ℕ → ℝ
  | 0, j => ∏ i ∈ Finset.range j, (1 - (i : ℝ) / n)
  | K + 1, j => ∑ i ∈ Finset.range j, (i : ℝ) / n * orderedResidual n K i

private theorem scaled_elementary_initial_sum (n r j : ℕ) :
    elementarySymmetric (r + 1) j / (n : ℝ) ^ (r + 1) =
      ∑ i ∈ Finset.range j, (i : ℝ) / n *
        (elementarySymmetric r i / (n : ℝ) ^ r) := by
  rw [elementary_initial_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

private theorem ordered_residual_step (n K j : ℕ) :
    orderedResidual n K j = elementarySymmetric K j / (n : ℝ) ^ K -
      orderedResidual n (K + 1) j := by
  induction K generalizing j with
  | zero =>
    rw [orderedResidual, Finset.prod_one_sub_ordered]
    simp only [elementary_zero, pow_zero, div_one, orderedResidual]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have hfilter : (Finset.range j).filter (fun h => h < i) = Finset.range i := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_range]
      have hij := Finset.mem_range.mp hi
      omega
    rw [hfilter]
  | succ K ih =>
    rw [orderedResidual, orderedResidual, scaled_elementary_initial_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih, mul_sub]

private theorem ordered_residual_bounds (n K j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) :
    0 ≤ orderedResidual n K j ∧
      orderedResidual n K j ≤ elementarySymmetric K j / (n : ℝ) ^ K := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  induction K generalizing j with
  | zero =>
    have hfactor (i : ℕ) (hi : i ∈ Finset.range j) :
        0 ≤ 1 - (i : ℝ) / n ∧ 1 - (i : ℝ) / n ≤ 1 := by
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hin : (i : ℝ) ≤ n := by exact_mod_cast
        (show i ≤ n by have := Finset.mem_range.mp hi; omega)
      exact ⟨sub_nonneg.mpr ((div_le_one hn0).mpr hin),
        sub_le_self _ (div_nonneg hi0 hn0.le)⟩
    constructor
    · exact Finset.prod_nonneg fun i hi => (hfactor i hi).1
    · simp only [elementary_zero, pow_zero, div_one]
      calc
        orderedResidual n 0 j ≤ ∏ _i ∈ Finset.range j, (1 : ℝ) :=
          Finset.prod_le_prod₀
            (fun i hi => (hfactor i hi).1)
            (fun i hi => (hfactor i hi).2)
        _ = 1 := by simp
  | succ K ih =>
    rw [orderedResidual, scaled_elementary_initial_sum]
    have ha (i : ℕ) : 0 ≤ (i : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn0.le
    constructor
    · apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (ha i) (ih i (by have := Finset.mem_range.mp hi; omega)).1
    · apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (ih i (by have := Finset.mem_range.mp hi; omega)).2 (ha i)

private theorem bonferroni_ordered_identity (n K j : ℕ) (hn : 1 ≤ n) :
    bonferroniResidual n K j = (-1 : ℝ) ^ (K + 1) * orderedResidual n (K + 1) j := by
  unfold bonferroniResidual
  rw [falling_normalized_product n j hn]
  change orderedResidual n 0 j - _ = _
  induction K with
  | zero =>
    simp only [Finset.sum_range_one, pow_zero, elementary_zero, div_one, one_mul, pow_one,
      Nat.zero_add]
    have h : orderedResidual n 0 j = 1 - orderedResidual n 1 j := by
      simpa only [elementary_zero, pow_zero, div_one] using ordered_residual_step n 0 j
    linarith
  | succ K ih =>
    rw [Finset.sum_range_succ, sub_add_eq_sub_sub, ih,
      ordered_residual_step n (K + 1) j, pow_succ]
    ring

private theorem bonferroni_residual_bound (n K j : ℕ) (hn : 1 ≤ n) :
    |bonferroniResidual n K j| ≤
      2 / (n : ℝ) ^ (K + 1) * (j : ℝ) ^ (2 * K + 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let x : ℝ := (j : ℝ) ^ 2 / n
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have htarget : 2 * x ^ (K + 1) =
      2 / (n : ℝ) ^ (K + 1) * (j : ℝ) ^ (2 * K + 2) := by
    dsimp [x]
    simp only [div_pow, show 2 * K + 2 = 2 * (K + 1) by omega, pow_mul]
    ring
  rw [← htarget]
  by_cases hj : j ≤ n
  · rw [bonferroni_ordered_identity n K j hn, abs_mul, abs_pow]
    norm_num only [abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_nonneg (ordered_residual_bounds n (K + 1) j hn hj).1]
    calc
      _ ≤ elementarySymmetric (K + 1) j / (n : ℝ) ^ (K + 1) :=
        (ordered_residual_bounds n (K + 1) j hn hj).2
      _ ≤ x ^ (K + 1) / 2 ^ (K + 1) := scaled_elementary_bound n (K + 1) j hn
      _ ≤ x ^ (K + 1) := div_le_self (by positivity) (one_le_pow₀ (by norm_num))
      _ ≤ 2 * x ^ (K + 1) := by nlinarith [pow_nonneg hx0 (K + 1)]
  · have hz : n.descFactorial j = 0 := Nat.descFactorial_of_lt (by omega)
    have hx : 1 ≤ x := by
      have hjn : (n : ℝ) < j := by exact_mod_cast (show n < j by omega)
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
      dsimp [x]
      apply (le_div_iff₀ hn0).mpr
      nlinarith
    rw [bonferroniResidual, hz, Nat.cast_zero, zero_div, zero_sub, abs_neg]
    calc
      _ ≤ ∑ r ∈ Finset.range (K + 1),
          |(-1 : ℝ) ^ r * elementarySymmetric r j / (n : ℝ) ^ r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r ∈ Finset.range (K + 1), elementarySymmetric r j / (n : ℝ) ^ r := by
        apply Finset.sum_congr rfl
        intro r _
        rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos hn0,
          abs_of_nonneg (elementary_nonneg r j)]
        norm_num
      _ ≤ ∑ r ∈ Finset.range (K + 1), x ^ (K + 1) / 2 ^ r := by
        apply Finset.sum_le_sum
        intro r hr
        exact (scaled_elementary_bound n r j hn).trans
          (div_le_div_of_nonneg_right
            (pow_le_pow_right₀ hx (by have := Finset.mem_range.mp hr; omega)) (by positivity))
      _ = x ^ (K + 1) * ∑ r ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ r := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        simp only [div_pow, one_pow]
        ring
      _ ≤ 2 * x ^ (K + 1) := by
        have hg : (∑ r ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ r) ≤ 2 := by
          have h := geom_sum_mul_neg (1 / 2 : ℝ) (K + 1)
          norm_num only at h
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (K + 1)]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hg (pow_nonneg hx0 _)

private theorem weighted_residual_bound (a : ℕ → ℂ) (n K b : ℕ) (R : ℝ)
    (hn : 1 ≤ n) (hR : 1 ≤ R)
    (hs : Summable (fun j => ‖a j‖ * (j : ℝ) ^ (2 * K + 2 + b) * R ^ j)) :
    ∑' j, ‖a j‖ * |bonferroniResidual n K j| *
      (j.descFactorial b : ℝ) * R ^ (j - b) ≤
      2 / (n : ℝ) ^ (K + 1) * ∑' j, ‖a j‖ * (j : ℝ) ^ (2 * K + 2 + b) * R ^ j := by
  let B := 2 / (n : ℝ) ^ (K + 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (j : ℕ) : ‖a j‖ * |bonferroniResidual n K j| *
      (j.descFactorial b : ℝ) * R ^ (j - b) ≤
      B * (‖a j‖ * (j : ℝ) ^ (2 * K + 2 + b) * R ^ j) := by
    by_cases hj : j < b
    · rw [Nat.descFactorial_of_lt hj, Nat.cast_zero, mul_zero, zero_mul]
      positivity
    · have hf : (j.descFactorial b : ℝ) ≤ (j : ℝ) ^ b := by
        exact_mod_cast Nat.descFactorial_le_pow j b
      have hp := pow_le_pow_right₀ hR (show j - b ≤ j by omega)
      have hr := bonferroni_residual_bound n K j hn
      calc
        _ ≤ ‖a j‖ * (B * (j : ℝ) ^ (2 * K + 2)) * ((j : ℝ) ^ b) * R ^ j :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hr (norm_nonneg _)) hf
            (Nat.cast_nonneg _) (by positivity)) hp (by positivity) (by positivity)
        _ = _ := by rw [pow_add]; ring
  have hmajor := hs.mul_left B
  have hminor : Summable (fun j => ‖a j‖ * |bonferroniResidual n K j| *
      (j.descFactorial b : ℝ) * R ^ (j - b)) :=
    hmajor.of_nonneg_of_le (fun j => by positivity) hpoint
  simpa [B, tsum_mul_left] using hminor.tsum_le_tsum hpoint hmajor


#print axioms correctionCoeff_top
#print axioms elementary_falling_factorial
#print axioms elementary_bound
#print axioms bonferroni_ordered_identity
#print axioms bonferroni_residual_bound
#print axioms weighted_residual_bound

end D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
