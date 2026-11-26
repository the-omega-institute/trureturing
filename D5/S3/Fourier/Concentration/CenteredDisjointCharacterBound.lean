/- GID: D5/S3/Fourier/Concentration/CenteredDisjointCharacterBound
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CenteredDisjointCharacterBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered exponential differences admit a quadratic exponential coefficient majorant. -/

import D5.S3.Fourier.Concentration.DisjointCharacterRemainder
import D5.S3.Arith.DiophantineApproximation.CountingVolume
import Mathlib.RingTheory.PowerSeries.Expand

/-! The centered phase sum and squared phase norms control overlap coefficients. -/

open Finset PowerSeries
open scoped PowerSeries

noncomputable section

namespace D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound

open DisjointCharacterEnvelope DisjointCharacterRemainder

def evenPart (a : ℂ) : ℂ⟦X⟧ :=
  expand 2 (by decide) (PowerSeries.mk fun m => (a / 2) ^ (2*m) / ((2*m+1).factorial : ℂ))

def quadraticAxis (v : ℝ) : ℝ⟦X⟧ := expand 2 (by decide) (realAxis v)

theorem axis_coeff (a : ℂ) (n : ℕ) : coeff n (axis a) = a ^ n / n.factorial := by
  simp [axis, coeff_exp, div_eq_mul_inv]

private theorem centered_difference (a : ℂ) :
    axis (-a/2) - axis (a/2) = C (-a) * (X * evenPart a) := by
  apply PowerSeries.ext
  intro n
  rw [map_sub, axis_coeff, axis_coeff, coeff_C_mul, ← pow_one (X : ℂ⟦X⟧), coeff_X_pow_mul']
  cases n with
  | zero => simp
  | succ n =>
    rw [ite_eq_left (by omega : 1 ≤ n+1), Nat.succ_sub_one]
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · rw [hm, evenPart, coeff_expand_mul, coeff_mk]
      rw [neg_div, pow_succ, pow_succ, neg_pow,
        (show Even (2*m) from ⟨m, by omega⟩).neg_one_pow, one_mul]
      ring
    · rw [hm, evenPart, coeff_expand_of_not_dvd 2 (by decide) _ (by omega)]
      rw [neg_div, (show Even (2*m+1+1) from ⟨m+1, by omega⟩).neg_pow]
      ring

private theorem tail_factorization (a : ℂ) :
    axis (-a) - 1 = C (-a) * X * (axis (-a/2) * evenPart a) := by
  have hneg : (-a/2) + (-a/2) = -a := by ring
  have hzero : (-a/2) + (a/2) = 0 := by ring
  calc
    _ = axis (-a/2) * (axis (-a/2) - axis (a/2)) := by
      rw [mul_sub, ← axis_add, ← axis_add, hneg, hzero, axis_zero]
    _ = _ := by rw [centered_difference]; ring

theorem centered_product {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) :
    axis c * ∏ j ∈ t, (axis (-a j) - 1) =
      C (∏ j ∈ t, -a j) * (X ^ t.card *
        (axis (c - (∑ j ∈ t, a j)/2) * ∏ j ∈ t, evenPart (a j))) := by
  classical
  induction t using Finset.induction_on generalizing c with
  | empty => simp
  | insert j t hj ih =>
    rw [prod_insert hj, tail_factorization]
    calc
      _ = C (-a j) * X * evenPart (a j) *
          (axis (c + (-a j/2)) * ∏ i ∈ t, (axis (-a i) - 1)) := by
        rw [axis_add]; ring
      _ = _ := by
        rw [ih, prod_insert hj, prod_insert hj, card_insert_of_notMem hj, sum_insert hj,
          map_mul, pow_succ]
        have h : c + -a j / 2 - (∑ i ∈ t, a i) / 2 =
            c - (a j + ∑ i ∈ t, a i) / 2 := by ring
        rw [h]
        ring

private theorem evenPart_majorized (a : ℂ) (n : ℕ) :
    ‖coeff n (evenPart a)‖ ≤ coeff n (quadraticAxis (‖a‖^2/24)) := by
  by_cases h : 2 ∣ n
  · obtain ⟨m,rfl⟩ := h
    rw [evenPart, quadraticAxis, coeff_expand_mul, coeff_expand_mul, coeff_mk,
      realAxis_coeff, norm_div, norm_pow, norm_div, Complex.norm_natCast,
      show ‖(2:ℂ)‖=2 by norm_num,
      pow_mul]
    have hfact : (6:ℝ)^m * m.factorial ≤ (2*m+1).factorial := by
      exact_mod_cast Nat.six_pow_mul_factorial_le m
    calc
      _ ≤ ((‖a‖/2)^2)^m / ((6:ℝ)^m * m.factorial) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfact
      _ = _ := by
        rw [div_mul_eq_div_div, ← div_pow]
        congr 2
        ring
  · rw [evenPart, quadraticAxis, coeff_expand_of_not_dvd 2 (by decide) _ h,
      coeff_expand_of_not_dvd 2 (by decide) _ h, norm_zero]

private theorem quadraticAxis_mul (u v : ℝ) :
    quadraticAxis u * quadraticAxis v = quadraticAxis (u+v) := by
  rw [quadraticAxis, quadraticAxis, quadraticAxis, ← map_mul, realAxis_mul]

theorem centered_product_majorized {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) (n : ℕ) :
    ‖coeff n (axis c * ∏ j ∈ t, evenPart (a j))‖ ≤
      coeff n (realAxis ‖c‖ * quadraticAxis (∑ j ∈ t, ‖a j‖^2/24)) := by
  classical
  have hp : ∀ m, ‖coeff m (∏ j ∈ t, evenPart (a j))‖ ≤
      coeff m (quadraticAxis (∑ j ∈ t, ‖a j‖^2/24)) := by
    induction t using Finset.induction_on with
    | empty =>
      intro m
      have h : quadraticAxis 0 = 1 := by simp [quadraticAxis, realAxis]
      rw [prod_empty, sum_empty, h]
      by_cases hm : m=0 <;> simp [hm]
    | insert j t hj ih =>
      intro m
      rw [prod_insert hj, sum_insert hj, ← quadraticAxis_mul]
      exact coeff_mul_majorized _ _ _ _ (evenPart_majorized (a j)) ih m
  exact coeff_mul_majorized _ _ _ _ (fun m => by rw [axis_norm_coeff, realAxis_coeff]) hp n

theorem quadratic_coefficient (u v : ℝ) (n : ℕ) :
    coeff n (realAxis u * quadraticAxis v) =
      ∑ m ∈ range (n/2+1), u^(n-2*m) / ((n-2*m).factorial : ℝ) *
        (v^m / (m.factorial : ℝ)) := by
  rw [mul_comm (realAxis u) (quadraticAxis v), coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [quadraticAxis, coeff_expand, realAxis_coeff, ite_mul, zero_mul]
  rw [← sum_filter]
  symm
  refine sum_bij (fun m _ => 2*m) ?_ ?_ ?_ ?_
  · intro m hm
    have hm' := mem_range.mp hm
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), dvd_mul_right _ _⟩
  · intro m hm m' hm' he
    omega
  · intro q hq
    obtain ⟨hq, hdvd⟩ := mem_filter.mp hq
    obtain ⟨m, rfl⟩ := hdvd
    exact ⟨m, mem_range.mpr (by have := mem_range.mp hq; omega), rfl⟩
  · intro m hm
    rw [Nat.mul_div_cancel_left m (by decide : 0 < 2)]
    ring

/-- A centered bound retaining the signed phase sum and the quadratic local penalty. -/
theorem centered_overlap_bound {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ) :
    let k := t.card
    let u := c - (∑ j ∈ t, a j)/2
    let v := (∑ j ∈ t, ‖a j‖^2)/24
    let term := expTermNorm
    ‖overlapCoefficient t c a d‖ ≤
      if k ≤ d then (∏ j ∈ t, ‖a j‖) *
        (∑ m ∈ range ((d-k)/2+1), term (‖u‖, d-k-2*m) * term (v, m)) else 0 := by
  classical
  dsimp only
  rw [overlapCoefficient, centered_product, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with h
  · rw [norm_mul, norm_prod]
    simp only [norm_neg]
    have hb := centered_product_majorized t (c - (∑ j ∈ t, a j)/2) a (d-t.card)
    rw [quadratic_coefficient, ← Finset.sum_div] at hb
    simpa only [expTermNorm] using mul_le_mul_of_nonneg_left hb
      (prod_nonneg fun j _ => norm_nonneg _)
  · simp

#print axioms centered_overlap_bound

end D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound
