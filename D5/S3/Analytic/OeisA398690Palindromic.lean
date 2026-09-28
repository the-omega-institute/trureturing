/- GID: D5/S3/Analytic/OeisA398690Palindromic
   generality: G
   mirror-B: D5/B/S3/Analytic/OeisA398690Palindromic
   mirror-E: none(waiver:formal-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema]
   utility: none
   digest: The simplified Verlinde row numerators have exact degree and palindromic coefficients. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic
import D5.S3.Analytic.PolynomialReflectionNumerator

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.OeisA398690Palindromic

open Polynomial Polynomial.Chebyshev
open scoped BigOperators

private theorem chebyshev_cassini (q : ℕ) :
    (U ℝ (q : ℤ)) ^ 2 + (U ℝ ((q : ℤ) - 1)) ^ 2 -
      2 * X * (U ℝ (q : ℤ)) * (U ℝ ((q : ℤ) - 1)) = 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
      have h : U ℝ ((q + 1 : ℕ) : ℤ) =
          2 * X * U ℝ (q : ℤ) - U ℝ ((q : ℤ) - 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using U_add_one ℝ (q : ℤ)
      rw [h]
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      linear_combination ih

private theorem chebyshev_factorization (q : ℕ) :
    (1 : ℝ[X]) - (-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ) =
      (1 - (-1 : ℝ[X]) ^ q * X) *
        (U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)) ^ 2 := by
  have hc := chebyshev_cassini q
  have hmul := T_mul_T ℝ ((q : ℤ) + 1) (q : ℤ)
  have h1 := T_eq_U_sub_X_mul_U (R := ℝ) (q : ℤ)
  have h2 := T_eq_X_mul_U_sub_U (R := ℝ) ((q : ℤ) - 1)
  have hcast : (((q : ℤ) + 1) + q) = ((2 * q + 1 : ℕ) : ℤ) := by omega
  rw [hcast, show (q : ℤ) + 1 - q = 1 by omega, T_one] at hmul
  rw [show (q : ℤ) - 1 + 2 = (q : ℤ) + 1 by omega] at h2
  let A : ℝ[X] := U ℝ (q : ℤ)
  let B : ℝ[X] := U ℝ ((q : ℤ) - 1)
  let e : ℝ[X] := (-1 : ℝ[X]) ^ q
  have he : e ^ 2 = 1 := by dsimp [e]; simp [← pow_mul]
  have hc' : A ^ 2 + B ^ 2 - 2 * X * A * B = 1 := hc
  have hTq : T ℝ (q : ℤ) = A - X * B := h1
  have hTq1 : T ℝ ((q : ℤ) + 1) = X * A - B := by simpa [A, B] using h2
  have hm : T ℝ ((2 * q + 1 : ℕ) : ℤ) =
      2 * (X * A - B) * (A - X * B) - X := by
    calc
      _ = 2 * T ℝ ((q : ℤ) + 1) * T ℝ (q : ℤ) - X := by linear_combination -hmul
      _ = _ := by rw [hTq, hTq1]
  change 1 - e * T ℝ ((2 * q + 1 : ℕ) : ℤ) = (1 - e * X) * (A + e * B) ^ 2
  rw [hm]
  linear_combination (norm := ring)
    (-(1 + e * X)) * hc' +
    (-B ^ 2 + 2 * X * A * B + e * X * B ^ 2) * he

private def node (q j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.pi / (2 * (2 * q + 1 : ℕ)))

private theorem node_eq_cos (q j : ℕ) :
    node q j = Real.cos (((q * (2 * j + 1) : ℕ) : ℝ) * Real.pi / (2 * q + 1 : ℕ)) := by
  have hm : ((2 * q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hangle :
      (((q * (2 * j + 1) : ℕ) : ℝ) * Real.pi / (2 * q + 1 : ℕ)) =
        (Real.pi / 2 - (((2 * j + 1 : ℕ) : ℝ) * Real.pi / (2 * (2 * q + 1 : ℕ)))) +
          (j : ℝ) * Real.pi := by
    field_simp
    push_cast
    ring
  rw [hangle, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two_sub]
  rfl

private theorem node_offcenter_abs_lt_one (q j : ℕ) (hj : j < q) : |node q j| < 1 := by
  let theta : ℝ := (((2 * j + 1 : ℕ) : ℝ) * Real.pi / (2 * (2 * q + 1 : ℕ)))
  have hm : (0 : ℝ) < (2 * q + 1 : ℕ) := by positivity
  have hnum : ((2 * j + 1 : ℕ) : ℝ) < (2 * q + 1 : ℕ) := by
    exact_mod_cast (by omega : 2 * j + 1 < 2 * q + 1)
  have htheta0 : 0 < theta := by dsimp [theta]; positivity
  have htheta1 : theta < Real.pi / 2 := by
    dsimp [theta]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * q + 1 : ℕ))).mpr
    nlinarith [mul_lt_mul_of_pos_right hnum Real.pi_pos]
  have hsin0 : 0 ≤ Real.sin theta :=
    (Real.sin_pos_of_pos_of_lt_pi htheta0 (by linarith [Real.pi_pos])).le
  have hsin1 : Real.sin theta < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := theta) (y := Real.pi / 2) (by linarith [Real.pi_pos]) le_rfl htheta1
    simpa using h
  unfold node
  rw [abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg hsin0]
  exact hsin1

private theorem node_offcenter_root (q j : ℕ) (hj : j < q) :
    (U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)).eval (node q j) = 0 := by
  let phi : ℝ := ((q * (2 * j + 1 : ℕ) : ℕ) : ℝ) * Real.pi / (2 * q + 1 : ℕ)
  have hm : ((2 * q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsin_phi : Real.sin phi ≠ 0 := by
    intro hz
    have hcos := Real.sin_eq_zero_iff_cos_eq.mp hz
    have hnode : Real.cos phi = node q j := (node_eq_cos q j).symm
    rw [hnode] at hcos
    have habs := node_offcenter_abs_lt_one q j hj
    rcases hcos with h | h <;> simp [h] at habs
  have hphase : ((2 * q + 1 : ℕ) : ℝ) * phi =
      ((q * (2 * j + 1 : ℕ) : ℕ) : ℝ) * Real.pi := by
    dsimp [phi]
    field_simp
  have hsin_phase : Real.sin (((2 * q + 1 : ℕ) : ℝ) * phi) = 0 := by
    rw [hphase, Real.sin_nat_mul_pi]
  have hcos_phase : Real.cos (((2 * q + 1 : ℕ) : ℝ) * phi) = (-1 : ℝ) ^ q := by
    rw [hphase, Real.cos_nat_mul_pi]
    rw [Nat.mul_comm q (2 * j + 1), pow_mul]
    simp [pow_add, pow_mul]
  have hsplit : ((q : ℝ) + 1) * phi =
      ((2 * q + 1 : ℕ) : ℝ) * phi - (q : ℝ) * phi := by
    push_cast
    ring
  have hsin_relation : Real.sin (((q : ℝ) + 1) * phi) +
      (-1 : ℝ) ^ q * Real.sin ((q : ℝ) * phi) = 0 := by
    rw [hsplit, Real.sin_sub, hsin_phase, hcos_phase]
    ring
  have huq : (U ℝ (q : ℤ)).eval (Real.cos phi) * Real.sin phi =
      Real.sin (((q : ℝ) + 1) * phi) := by
    simp
  have huqm : (U ℝ ((q : ℤ) - 1)).eval (Real.cos phi) * Real.sin phi =
      Real.sin ((q : ℝ) * phi) := by
    simp
  rw [node_eq_cos q j]
  change (U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)).eval
    (Real.cos phi) = 0
  apply (mul_eq_zero_iff_right hsin_phi).mp
  calc
    (U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)).eval
        (Real.cos phi) * Real.sin phi =
        (U ℝ (q : ℤ)).eval (Real.cos phi) * Real.sin phi +
          (-1 : ℝ) ^ q *
            ((U ℝ ((q : ℤ) - 1)).eval (Real.cos phi) * Real.sin phi) := by
          simp [add_mul, mul_assoc]
    _ = 0 := by rw [huq, huqm]; exact hsin_relation

private theorem node_abs_strict (q j l : ℕ) (hjl : j < l) (hlq : l < q) :
    |node q j| < |node q l| := by
  let tj : ℝ := (((2 * j + 1 : ℕ) : ℝ) * Real.pi / (2 * (2 * q + 1 : ℕ)))
  let tl : ℝ := (((2 * l + 1 : ℕ) : ℝ) * Real.pi / (2 * (2 * q + 1 : ℕ)))
  have hnum : ((2 * j + 1 : ℕ) : ℝ) < (2 * l + 1 : ℕ) := by
    exact_mod_cast (by omega : 2 * j + 1 < 2 * l + 1)
  have hnumq : ((2 * l + 1 : ℕ) : ℝ) < (2 * q + 1 : ℕ) := by
    exact_mod_cast (by omega : 2 * l + 1 < 2 * q + 1)
  have htj0 : 0 < tj := by dsimp [tj]; positivity
  have htl0 : 0 < tl := by dsimp [tl]; positivity
  have htjl : tj < tl := by
    dsimp [tj, tl]
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * q + 1 : ℕ))
      (by positivity : (0 : ℝ) < 2 * (2 * q + 1 : ℕ))).mpr
    nlinarith [mul_lt_mul_of_pos_right hnum Real.pi_pos]
  have htl1 : tl < Real.pi / 2 := by
    dsimp [tl]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * q + 1 : ℕ))).mpr
    nlinarith [mul_lt_mul_of_pos_right hnumq Real.pi_pos]
  have hsinlt := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := tj) (y := tl) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) htjl
  have hsj : 0 ≤ Real.sin tj :=
    (Real.sin_pos_of_pos_of_lt_pi htj0 (by linarith [Real.pi_pos])).le
  have hsl : 0 ≤ Real.sin tl :=
    (Real.sin_pos_of_pos_of_lt_pi htl0 (by linarith [Real.pi_pos])).le
  unfold node
  rw [abs_mul, abs_mul, abs_neg_one_pow, abs_neg_one_pow, one_mul, one_mul,
    abs_of_nonneg hsj, abs_of_nonneg hsl]
  exact hsinlt

private theorem factor_roots (q : ℕ) :
    (U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)).roots =
      ((Finset.range q).image (node q)).val := by
  let Q : ℝ[X] := U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)
  have hinj : Set.InjOn (node q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · have hh := node_abs_strict q a b h (Finset.mem_range.mp hb)
      rw [hab] at hh
      exact (lt_irrefl _ hh).elim
    · exact h
    · have hh := node_abs_strict q b a h (Finset.mem_range.mp ha)
      rw [hab] at hh
      exact (lt_irrefl _ hh).elim
  have hcard : ((Finset.range q).image (node q)).card = q := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hroots : ∀ x ∈ (Finset.range q).image (node q), Q.eval x = 0 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact node_offcenter_root q j (Finset.mem_range.mp hj)
  have hQle : Q.natDegree ≤ q := by
    cases q with
    | zero => simp [Q]
    | succ p =>
        have hidx : (((p + 1 : ℕ) : ℤ) - 1) = (p : ℤ) := by omega
        have hA : (U ℝ (((p + 1 : ℕ) : ℤ))).natDegree = p + 1 :=
          natDegree_U_natCast ℝ (p + 1)
        have hB : (U ℝ (((p + 1 : ℕ) : ℤ) - 1)).natDegree = p := by
          rw [hidx]
          simp
        have he : ((-1 : ℝ[X]) ^ (p + 1)).natDegree = 0 := by
          rcases neg_one_pow_eq_or ℝ[X] (p + 1) with hs | hs <;> simp [hs]
        exact (natDegree_add_le _ _).trans (max_le (by simpa [Q] using hA.le)
          (by
            have hm := natDegree_mul_le
              (p := (-1 : ℝ[X]) ^ (p + 1))
              (q := U ℝ (((p + 1 : ℕ) : ℤ) - 1))
            have hmp : ((-1 : ℝ[X]) ^ (p + 1) *
                U ℝ (((p + 1 : ℕ) : ℤ) - 1)).natDegree ≤ p := by
              simpa [he, hB] using hm
            exact hmp.trans (Nat.le_succ p)))
  have hQne : Q ≠ 0 := by
    cases q with
    | zero => simp [Q]
    | succ p =>
        have hidx : (((p + 1 : ℕ) : ℤ) - 1) = (p : ℤ) := by omega
        have hval : Q.eval 1 = (p + 2 : ℝ) + (-1 : ℝ) ^ (p + 1) * (p + 1 : ℝ) := by
          dsimp [Q]
          rw [show (p : ℤ) + 1 - 1 = (p : ℤ) by ring]
          simp only [eval_add, eval_mul, eval_pow, eval_neg, eval_one, U_eval_one]
          push_cast
          ring
        intro hz
        have hv : Q.eval 1 = 0 := by rw [hz]; simp
        rw [hval] at hv
        rcases neg_one_pow_eq_or ℝ (p + 1) with hs | hs <;> rw [hs] at hv <;>
          nlinarith
  change Q.roots = _
  apply roots_eq_of_natDegree_le_card_of_ne_zero hroots (by simpa [hcard] using hQle) hQne

private theorem node_center (q : ℕ) : node q q = (-1 : ℝ) ^ q := by
  have hm : 2 * (q : ℝ) + 1 ≠ 0 := by positivity
  have htheta : ((2 * (q : ℝ) + 1) * Real.pi /
      (2 * (2 * (q : ℝ) + 1))) = Real.pi / 2 := by
    field_simp
  unfold node
  push_cast
  rw [htheta, Real.sin_pi_div_two]
  ring

private theorem node_reflect (q j : ℕ) (hj : j ≤ q) :
    node q (2 * q - j) = node q j := by
  have hidx : 2 * q - j = 2 * (q - j) + j := by omega
  have hsign : (-1 : ℝ) ^ (2 * q - j) = (-1 : ℝ) ^ j := by
    rw [hidx, pow_add]
    simp [pow_mul]
  have htheta :
      (((2 * (2 * q - j) + 1 : ℕ) : ℝ) * Real.pi /
        (2 * (2 * q + 1 : ℕ))) =
        Real.pi - (((2 * j + 1 : ℕ) : ℝ) * Real.pi /
          (2 * (2 * q + 1 : ℕ))) := by
    have hsub : j ≤ 2 * q := by omega
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hsub]
    push_cast
    have hm : ((2 * q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  unfold node
  rw [hsign, htheta, Real.sin_pi_sub]

private theorem node_product_pair {M : Type*} [CommMonoid M] (q : ℕ) (f : ℝ → M) :
    (∏ j ∈ Finset.range (2 * q + 1), f (node q j)) =
      f ((-1 : ℝ) ^ q) * (∏ j ∈ Finset.range q, f (node q j)) ^ 2 := by
  have htail : (∏ j ∈ Finset.range q, f (node q (q + 1 + j))) =
      ∏ j ∈ Finset.range q, f (node q j) := by
    calc
      _ = ∏ j ∈ Finset.range q, f (node q (q + 1 + (q - 1 - j))) :=
        (Finset.prod_range_reflect (fun j => f (node q (q + 1 + j))) q).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j hj
        have hjq : j < q := Finset.mem_range.mp hj
        have hidx : q + 1 + (q - 1 - j) = 2 * q - j := by omega
        rw [hidx, node_reflect q j (by omega)]
  rw [show 2 * q + 1 = (q + 1) + q by omega,
    Finset.prod_range_add, Finset.prod_range_succ, htail, node_center]
  simp only [pow_two]
  ac_rfl

private theorem node_ne_zero (q j : ℕ) (hj : j < 2 * q + 1) : node q j ≠ 0 := by
  have hnum : ((2 * j + 1 : ℕ) : ℝ) < 2 * (2 * q + 1 : ℕ) := by
    exact_mod_cast (by omega : 2 * j + 1 < 2 * (2 * q + 1))
  have htheta0 : 0 < (((2 * j + 1 : ℕ) : ℝ) * Real.pi /
      (2 * (2 * q + 1 : ℕ))) := by positivity
  have htheta1 : (((2 * j + 1 : ℕ) : ℝ) * Real.pi /
      (2 * (2 * q + 1 : ℕ))) < Real.pi := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * q + 1 : ℕ))).mpr
    nlinarith [mul_lt_mul_of_pos_right hnum Real.pi_pos]
  unfold node
  exact mul_ne_zero (by simp) (Real.sin_pos_of_pos_of_lt_pi htheta0 htheta1).ne'

private theorem factor_normalized (q : ℕ) :
    C ((U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)).eval 0) *
      (∏ j ∈ Finset.range q, (1 - C ((node q j)⁻¹) * X)) =
        U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1) := by
  let Q : ℝ[X] := U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)
  let R : ℝ[X] := ∏ j ∈ Finset.range q, (1 - C ((node q j)⁻¹) * X)
  have hfactor (j : ℕ) : (1 - C ((node q j)⁻¹) * X : ℝ[X]).natDegree ≤ 1 := by
    calc
      _ ≤ max (1 : ℝ[X]).natDegree (C ((node q j)⁻¹) * X).natDegree :=
        natDegree_sub_le _ _
      _ ≤ 1 := by
        apply max_le
        · simp
        · simpa using (natDegree_C_mul_le ((node q j)⁻¹) (X : ℝ[X])).trans natDegree_X_le
  have hRdeg : R.natDegree ≤ q := by
    calc
      _ ≤ ∑ j ∈ Finset.range q, (1 - C ((node q j)⁻¹) * X : ℝ[X]).natDegree :=
        natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ Finset.range q, 1 := Finset.sum_le_sum (fun j _ => hfactor j)
      _ = q := by simp
  have hQdeg : Q.natDegree ≤ q := by
    cases q with
    | zero => simp [Q]
    | succ p =>
        have hidx : (((p + 1 : ℕ) : ℤ) - 1) = (p : ℤ) := by omega
        have hA : (U ℝ (((p + 1 : ℕ) : ℤ))).natDegree = p + 1 :=
          natDegree_U_natCast ℝ (p + 1)
        have hB : (U ℝ (((p + 1 : ℕ) : ℤ) - 1)).natDegree = p := by
          rw [hidx]
          simp
        have he : ((-1 : ℝ[X]) ^ (p + 1)).natDegree = 0 := by
          rcases neg_one_pow_eq_or ℝ[X] (p + 1) with hs | hs <;> simp [hs]
        exact (natDegree_add_le _ _).trans (max_le (by simpa [Q] using hA.le)
          (by
            have hm := natDegree_mul_le
              (p := (-1 : ℝ[X]) ^ (p + 1))
              (q := U ℝ (((p + 1 : ℕ) : ℤ) - 1))
            have hmp : ((-1 : ℝ[X]) ^ (p + 1) *
                U ℝ (((p + 1 : ℕ) : ℤ) - 1)).natDegree ≤ p := by
              simpa [he, hB] using hm
            exact hmp.trans (Nat.le_succ p)))
  have hinj : Set.InjOn (node q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · have hh := node_abs_strict q a b h (Finset.mem_range.mp hb)
      rw [hab] at hh
      exact (lt_irrefl _ hh).elim
    · exact h
    · have hh := node_abs_strict q b a h (Finset.mem_range.mp ha)
      rw [hab] at hh
      exact (lt_irrefl _ hh).elim
  have hnot : 0 ∉ (Finset.range q).image (node q) := by
    intro hz
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp hz
    exact node_ne_zero q j (by have := Finset.mem_range.mp hj; omega) hj0
  let S : Finset ℝ := insert 0 ((Finset.range q).image (node q))
  have hScard : S.card = q + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj,
      Finset.card_range]
  have hReval0 : R.eval 0 = 1 := by
    simp [R, eval_prod]
  have hReval_node (j : ℕ) (hj : j < q) : R.eval (node q j) = 0 := by
    dsimp [R]
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
    simp [node_ne_zero q j (by omega)]
  have heval : ∀ x ∈ S, (C (Q.eval 0) * R).eval x = Q.eval x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp [hReval0]
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hr := hReval_node j (Finset.mem_range.mp hj)
      have hq : Q.eval (node q j) = 0 := node_offcenter_root q j
        (Finset.mem_range.mp hj)
      simp [hr, hq]
  change C (Q.eval 0) * R = Q
  apply eq_of_natDegree_lt_card_of_eval_eq' _ _ S heval
  rw [hScard]
  apply max_lt
  · exact (natDegree_C_mul_le _ _).trans hRdeg |>.trans_lt (Nat.lt_succ_self q)
  · exact hQdeg.trans_lt (Nat.lt_succ_self q)

private theorem factor_eval_zero_sq (q : ℕ) :
    ((U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)).eval 0) ^ 2 = 1 := by
  have hodd : Odd (((2 * q + 1 : ℕ) : ℤ)) := by
    refine ⟨q, ?_⟩
    omega
  have hf := congrArg (fun p : ℝ[X] => p.eval 0) (chebyshev_factorization q)
  simp only [eval_sub, eval_mul, eval_pow, eval_one, eval_X, mul_zero, sub_zero,
    one_mul, T_eval_zero_of_odd (R := ℝ) hodd] at hf
  exact hf.symm

private theorem node_product_chebyshev (q : ℕ) :
    (∏ j ∈ Finset.range (2 * q + 1),
      (1 - C ((node q j)⁻¹) * X : ℝ[X])) =
        1 - (-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ) := by
  let Q : ℝ[X] := U ℝ (q : ℤ) + (-1 : ℝ[X]) ^ q * U ℝ ((q : ℤ) - 1)
  let R : ℝ[X] := ∏ j ∈ Finset.range q, (1 - C ((node q j)⁻¹) * X)
  let e : ℝ := (-1 : ℝ) ^ q
  have he : e⁻¹ = e := by
    dsimp [e]
    rcases neg_one_pow_eq_or ℝ q with h | h <;> simp [h]
  have hepoly : C e = (-1 : ℝ[X]) ^ q := by
    dsimp [e]
    rw [map_pow]
    simp
  have hnorm : C (Q.eval 0) * R = Q := factor_normalized q
  have hsq : (Q.eval 0) ^ 2 = 1 := factor_eval_zero_sq q
  have hR : R ^ 2 = Q ^ 2 := by
    have h := congrArg (fun p : ℝ[X] => p ^ 2) hnorm
    simp only [mul_pow, ← map_pow, hsq, map_one, one_mul] at h
    exact h
  calc
    (∏ j ∈ Finset.range (2 * q + 1),
      (1 - C ((node q j)⁻¹) * X : ℝ[X])) =
        (1 - C (e⁻¹) * X) * R ^ 2 := by
          exact node_product_pair q
            (fun y : ℝ => (1 - C (y⁻¹) * X : ℝ[X]))
    _ = (1 - (-1 : ℝ[X]) ^ q * X) * Q ^ 2 := by
      rw [he, hR, hepoly]
    _ = 1 - (-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ) :=
      (chebyshev_factorization q).symm

private theorem geom_factor (a : ℝ) :
    PowerSeries.mk (fun n => a ^ (n + 1)) *
      (1 - PowerSeries.C a * PowerSeries.X) = PowerSeries.C a := by
  have hgeom : PowerSeries.mk (fun n => a ^ n) *
      (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
    have h := congrArg (PowerSeries.rescale a)
      (PowerSeries.mk_one_mul_one_sub_eq_one ℝ)
    simpa [PowerSeries.rescale_mk, PowerSeries.rescale_X] using h
  have hshift : PowerSeries.mk (fun n => a ^ (n + 1)) =
      PowerSeries.C a * PowerSeries.mk (fun n => a ^ n) := by
    ext n
    simp [PowerSeries.coeff_mk, pow_succ, mul_comm]
  rw [hshift]
  calc
    (PowerSeries.C a * PowerSeries.mk (fun n => a ^ n)) *
        (1 - PowerSeries.C a * PowerSeries.X) =
        PowerSeries.C a *
          (PowerSeries.mk (fun n => a ^ n) *
            (1 - PowerSeries.C a * PowerSeries.X)) := by ac_rfl
    _ = PowerSeries.C a := by rw [hgeom]; ring

private theorem finite_log_deriv {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) :
    (∏ j ∈ s, (1 - PowerSeries.C (a j) * PowerSeries.X : PowerSeries ℝ)) *
      (∑ j ∈ s, PowerSeries.mk (fun n => a j ^ (n + 1))) =
        -(PowerSeries.derivative ℝ)
          (∏ j ∈ s, (1 - PowerSeries.C (a j) * PowerSeries.X : PowerSeries ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      let A : PowerSeries ℝ := 1 - PowerSeries.C (a i) * PowerSeries.X
      let P : PowerSeries ℝ :=
        ∏ j ∈ s, (1 - PowerSeries.C (a j) * PowerSeries.X : PowerSeries ℝ)
      let G : PowerSeries ℝ := PowerSeries.mk (fun n => a i ^ (n + 1))
      let S : PowerSeries ℝ := ∑ j ∈ s, PowerSeries.mk (fun n => a j ^ (n + 1))
      have hA : (PowerSeries.derivative ℝ) A = -PowerSeries.C (a i) := by
        dsimp [A]
        simp [(PowerSeries.derivative ℝ).leibniz, smul_eq_mul]
      have hG : G * A = PowerSeries.C (a i) := geom_factor (a i)
      have hP : P * S = -(PowerSeries.derivative ℝ) P := ih
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      change (A * P) * (G + S) = -(PowerSeries.derivative ℝ) (A * P)
      calc
        (A * P) * (G + S) = P * (G * A) + A * (P * S) := by ring
        _ = P * PowerSeries.C (a i) - A * (PowerSeries.derivative ℝ) P := by
          rw [hG, hP]
          ring
        _ = -(PowerSeries.derivative ℝ) (A * P) := by
          rw [(PowerSeries.derivative ℝ).leibniz, hA]
          simp only [smul_eq_mul]
          ring

private theorem node_moment_derivative (q : ℕ) :
    (((1 : ℝ[X]) - (-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ) : ℝ[X]) :
      PowerSeries ℝ) *
      PowerSeries.mk (fun n => ∑ j ∈ Finset.range (2 * q + 1),
        (node q j)⁻¹ ^ (n + 1)) =
        ((((-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ)).derivative : ℝ[X]) :
          PowerSeries ℝ) := by
  let f : ℕ → ℝ := fun j => (node q j)⁻¹
  let P : ℝ[X] := 1 - (-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ)
  have hmk : (∑ j ∈ Finset.range (2 * q + 1),
      PowerSeries.mk (fun n => f j ^ (n + 1))) =
      PowerSeries.mk (fun n => ∑ j ∈ Finset.range (2 * q + 1), f j ^ (n + 1)) := by
    ext n
    simp
  have hcoe :
      (∏ j ∈ Finset.range (2 * q + 1),
        (1 - PowerSeries.C (f j) * PowerSeries.X : PowerSeries ℝ)) =
          (P : PowerSeries ℝ) := by
    calc
      _ = ((∏ j ∈ Finset.range (2 * q + 1),
          (1 - C ((node q j)⁻¹) * X : ℝ[X])) : PowerSeries ℝ) := by
            simp [f]
      _ = (P : PowerSeries ℝ) := by
        have hcast_prod := map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℝ))
          (fun j => (1 - C ((node q j)⁻¹) * X : ℝ[X]))
          (Finset.range (2 * q + 1))
        simp only [Polynomial.coeToPowerSeries.ringHom_apply] at hcast_prod
        rw [← hcast_prod]
        simpa only [P] using congrArg (fun p : ℝ[X] => (p : PowerSeries ℝ))
          (node_product_chebyshev q)
  have h := finite_log_deriv (Finset.range (2 * q + 1)) f
  rw [hmk, hcoe, PowerSeries.derivative_coe] at h
  change (P : PowerSeries ℝ) * PowerSeries.mk
    (fun n => ∑ j ∈ Finset.range (2 * q + 1), f j ^ (n + 1)) = _
  have hd : (P.derivative : PowerSeries ℝ) =
      -((((-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ)).derivative : ℝ[X]) :
        PowerSeries ℝ) := by
    simp [P]
  rw [hd] at h
  simpa [f, P] using h


open Polynomial Polynomial.Chebyshev

private def derivativeModel : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | r + 2 => (C ((r + 1 : ℝ) ^ 2) - X ^ 2) * derivativeModel r

private theorem derivativeModel_eval (q r : ℕ) :
    (Polynomial.derivative^[r + 1]
      ((-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ))).eval 0 =
      (2 * q + 1 : ℝ) * (derivativeModel r).eval (2 * q + 1 : ℝ) := by
  induction r using Nat.twoStepInduction with
  | zero =>
      have hU : (U ℝ ((2 * q : ℕ) : ℤ)).eval 0 = (-1 : ℝ) ^ q := by
        simp
      change (derivative ((-1 : ℝ[X]) ^ q *
        T ℝ ((2 * q + 1 : ℕ) : ℤ))).eval 0 = _
      have hneg : (-1 : ℝ[X]) = C (-1 : ℝ) := by simp
      rw [hneg, ← map_pow (C : ℝ →+* ℝ[X]) (-1 : ℝ) q,
        derivative_C_mul, eval_mul, eval_C, T_derivative_eq_U]
      simp only [eval_mul, eval_intCast, derivativeModel, eval_one]
      rw [show ((2 * q + 1 : ℕ) : ℤ) - 1 = ((2 * q : ℕ) : ℤ) by omega, hU]
      push_cast
      have hs : ((-1 : ℝ) ^ q) ^ 2 = 1 := by simp [← pow_mul]
      calc
        (-1 : ℝ) ^ q * ((2 * q + 1 : ℝ) * (-1 : ℝ) ^ q) =
            (2 * q + 1 : ℝ) * ((-1 : ℝ) ^ q) ^ 2 := by ring
        _ = _ := by rw [hs]
  | one =>
      have hodd : Odd (((2 * q + 1 : ℕ) : ℤ)) := by
        refine ⟨q, ?_⟩
        omega
      have hzero : (T ℝ ((2 * q + 1 : ℕ) : ℤ)).eval 0 = 0 :=
        T_eval_zero_of_odd (R := ℝ) hodd
      have hrec := iterate_derivative_T_eval_zero_recurrence
        (R := ℝ) ((2 * q + 1 : ℕ) : ℤ) 0
      simp [hzero] at hrec
      have hrec' : (Polynomial.derivative^[2]
          (T ℝ ((2 * q + 1 : ℕ) : ℤ))).eval 0 = 0 := by
        simpa [Function.iterate_succ_apply', Function.iterate_one,
          Nat.cast_add, Nat.cast_mul] using hrec
      have hneg : (-1 : ℝ[X]) = C (-1 : ℝ) := by simp
      change (Polynomial.derivative^[2]
        ((-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ))).eval 0 = _
      rw [hneg, ← map_pow (C : ℝ →+* ℝ[X]) (-1 : ℝ) q,
        iterate_derivative_C_mul, eval_mul, hrec']
      simp [derivativeModel]
  | more r ih1 ih2 =>
      let m : ℤ := ((2 * q + 1 : ℕ) : ℤ)
      let A : ℝ[X] := (-1 : ℝ[X]) ^ q * T ℝ m
      have hneg : (-1 : ℝ[X]) = C (-1 : ℝ) := by simp
      have hiter (s : ℕ) : (Polynomial.derivative^[s] A).eval 0 =
          (-1 : ℝ) ^ q * (Polynomial.derivative^[s] (T ℝ m)).eval 0 := by
        dsimp [A]
        rw [hneg, ← map_pow (C : ℝ →+* ℝ[X]) (-1 : ℝ) q,
          iterate_derivative_C_mul, eval_mul, eval_C]
      have ht := iterate_derivative_T_eval_zero_recurrence (R := ℝ) m (r + 1)
      have hrec : (Polynomial.derivative^[r + 3] A).eval 0 =
          -(((m : ℝ) ^ 2) - ((r + 1 : ℝ) ^ 2)) *
            (Polynomial.derivative^[r + 1] A).eval 0 := by
        rw [hiter, hiter]
        convert congrArg (fun x : ℝ => (-1 : ℝ) ^ q * x) ht using 1 <;>
          push_cast <;> ring
      change (Polynomial.derivative^[r + 3] A).eval 0 = _
      rw [hrec, ih1]
      simp only [derivativeModel, eval_mul, eval_sub, eval_C, eval_pow, eval_X]
      dsimp [m]
      push_cast
      ring

private def coeffModel (r : ℕ) : ℝ[X] :=
  C (((r + 1).factorial : ℝ)⁻¹) * derivativeModel r

private theorem chebyshev_coeff_model (q r : ℕ) :
    (((-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ)).coeff (r + 1)) =
      (2 * q + 1 : ℝ) * (coeffModel r).eval (2 * q + 1 : ℝ) := by
  let A : ℝ[X] := (-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ)
  have hderiv := derivativeModel_eval q r
  have hcoeff := coeff_iterate_derivative A 0 (k := r + 1)
  have hfact : ((r + 1).factorial : ℝ) * A.coeff (r + 1) =
      (2 * q + 1 : ℝ) * (derivativeModel r).eval (2 * q + 1 : ℝ) := by
    have hcoeff' : ((r + 1).factorial : ℝ) * A.coeff (r + 1) =
        (Polynomial.derivative^[r + 1] A).eval 0 := by
      simpa only [Nat.zero_add, Nat.descFactorial_self,
        coeff_zero_eq_eval_zero, nsmul_eq_mul] using hcoeff.symm
    rw [hcoeff']
    exact hderiv
  have hfne : ((r + 1).factorial : ℝ) ≠ 0 := by positivity
  change A.coeff (r + 1) = _
  simp only [coeffModel, eval_mul, eval_C]
  field_simp
  nlinarith [hfact]

private theorem derivativeModel_degree_le (r : ℕ) :
    (derivativeModel r).natDegree ≤ r := by
  induction r using Nat.twoStepInduction with
  | zero => simp [derivativeModel]
  | one => simp [derivativeModel]
  | more r ih1 ih2 =>
      have hfactor : (C ((r + 1 : ℝ) ^ 2) - (X : ℝ[X]) ^ 2).natDegree ≤ 2 := by
        have hC : (C ((r + 1 : ℝ) ^ 2) : ℝ[X]).natDegree ≤ 2 := by
          simp only [natDegree_C]
          omega
        have hX : ((X : ℝ[X]) ^ 2).natDegree ≤ 2 := by simp
        exact (natDegree_sub_le _ _).trans (max_le hC hX)
      calc
        (derivativeModel (r + 2)).natDegree ≤
            (C ((r + 1 : ℝ) ^ 2) - (X : ℝ[X]) ^ 2).natDegree +
              (derivativeModel r).natDegree := by
                simp only [derivativeModel]
                exact natDegree_mul_le
        _ ≤ r + 2 := by omega

private theorem derivativeModel_parity (r : ℕ) :
    (derivativeModel r).comp (-X) = (-1 : ℝ[X]) ^ r * derivativeModel r := by
  induction r using Nat.twoStepInduction with
  | zero => simp [derivativeModel]
  | one => simp [derivativeModel]
  | more r ih1 ih2 =>
      have hfac : (C ((r + 1 : ℝ) ^ 2) - (X : ℝ[X]) ^ 2).comp (-X) =
          C ((r + 1 : ℝ) ^ 2) - X ^ 2 := by simp [sub_comp, pow_comp]
      simp only [derivativeModel, mul_comp, hfac, ih1]
      have hpow : (-1 : ℝ[X]) ^ (r + 2) = (-1 : ℝ[X]) ^ r := by
        simp [pow_add]
      rw [hpow]
      ring

private theorem coeffModel_degree_le (r : ℕ) : (coeffModel r).natDegree ≤ r := by
  unfold coeffModel
  exact (natDegree_C_mul_le _ _).trans (derivativeModel_degree_le r)

private theorem coeffModel_parity (r : ℕ) :
    (coeffModel r).comp (-X) = (-1 : ℝ[X]) ^ r * coeffModel r := by
  unfold coeffModel
  rw [mul_comp, C_comp, derivativeModel_parity]
  ring

private def momentModel : ℕ → ℝ[X] := fun n => Nat.strongRecOn n (fun n rec =>
  if hn : n = 0 then 1 else
    C (n + 1 : ℝ) * coeffModel n +
      X * ∑ i ∈ Finset.range n,
        coeffModel i * rec (n - 1 - i) (by omega))

private theorem momentModel_zero : momentModel 0 = 1 := by
  simp [momentModel, Nat.strongRecOn_eq]

private theorem momentModel_eq (n : ℕ) (hn : n ≠ 0) :
    momentModel n = C (n + 1 : ℝ) * coeffModel n +
      X * ∑ i ∈ Finset.range n, coeffModel i * momentModel (n - 1 - i) := by
  unfold momentModel
  rw [Nat.strongRecOn_eq]
  simp only [dif_neg hn]

private theorem momentModel_degree_le (n : ℕ) : (momentModel n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [momentModel_zero]
      rw [momentModel_eq n hn]
      apply (natDegree_add_le _ _).trans
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans (coeffModel_degree_le n)
      · have hsum : (∑ i ∈ Finset.range n,
            coeffModel i * momentModel (n - 1 - i)).natDegree ≤ n - 1 := by
          apply natDegree_sum_le_of_forall_le
          intro i hi
          have hin : i < n := Finset.mem_range.mp hi
          calc
            (coeffModel i * momentModel (n - 1 - i)).natDegree ≤
                (coeffModel i).natDegree + (momentModel (n - 1 - i)).natDegree :=
              natDegree_mul_le
            _ ≤ n - 1 := by
              have hprev := ih (n - 1 - i) (by omega)
              have hc := coeffModel_degree_le i
              omega
        have hmul := natDegree_mul_le (p := (X : ℝ[X]))
          (q := ∑ i ∈ Finset.range n, coeffModel i * momentModel (n - 1 - i))
        have hx : (X : ℝ[X]).natDegree = 1 := natDegree_X
        omega

private theorem momentModel_parity (n : ℕ) :
    (momentModel n).comp (-X) = (-1 : ℝ[X]) ^ n * momentModel n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [momentModel_zero]
      rw [momentModel_eq n hn, add_comp, mul_comp, mul_comp, C_comp, X_comp,
        sum_comp, coeffModel_parity]
      have hsum : (∑ i ∈ Finset.range n,
          (coeffModel i).comp (-X) * (momentModel (n - 1 - i)).comp (-X)) =
          (-1 : ℝ[X]) ^ (n - 1) *
            ∑ i ∈ Finset.range n, coeffModel i * momentModel (n - 1 - i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        rw [coeffModel_parity, ih (n - 1 - i) (by omega)]
        have hidx : i + (n - 1 - i) = n - 1 := by omega
        calc
          (-1 : ℝ[X]) ^ i * coeffModel i *
              ((-1 : ℝ[X]) ^ (n - 1 - i) * momentModel (n - 1 - i)) =
            ((-1 : ℝ[X]) ^ i * (-1 : ℝ[X]) ^ (n - 1 - i)) *
              (coeffModel i * momentModel (n - 1 - i)) := by ring
          _ = _ := by rw [← pow_add, hidx]
      simp_rw [mul_comp]
      rw [hsum]
      have hsign : -(-1 : ℝ[X]) ^ (n - 1) = (-1 : ℝ[X]) ^ n := by
        cases n with
        | zero => contradiction
        | succ k => simp [pow_succ]
      rw [← hsign]
      ring

private def chebPolynomial (q : ℕ) : ℝ[X] :=
  (-1 : ℝ[X]) ^ q * T ℝ ((2 * q + 1 : ℕ) : ℤ)

private def rawMoment (q n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (2 * q + 1),
    (node q j)⁻¹ ^ (n + 1)

private theorem chebPolynomial_zero (q : ℕ) : (chebPolynomial q).coeff 0 = 0 := by
  simp [chebPolynomial, coeff_zero_eq_eval_zero]

private theorem rawMoment_recurrence (q n : ℕ) :
    rawMoment q n = (n + 1 : ℝ) * (chebPolynomial q).coeff (n + 1) +
      ∑ i ∈ Finset.range n,
        (chebPolynomial q).coeff (i + 1) * rawMoment q (n - 1 - i) := by
  let A := chebPolynomial q
  let S : PowerSeries ℝ := PowerSeries.mk (rawMoment q)
  have hbridge : (1 - (A : PowerSeries ℝ)) * S =
      ((A.derivative : ℝ[X]) : PowerSeries ℝ) := by
    have hS : S = PowerSeries.mk (fun n => ∑ j ∈ Finset.range (2 * q + 1),
        (node q j)⁻¹ ^ (n + 1)) := rfl
    rw [hS]
    simpa only [A, chebPolynomial, Polynomial.coe_sub,
      Polynomial.coe_one] using node_moment_derivative q
  have hcoeff := congrArg (fun f : PowerSeries ℝ => f.coeff n) hbridge
  simp only [sub_mul, one_mul] at hcoeff
  have hcoeff' : rawMoment q n - ((A : PowerSeries ℝ) * S).coeff n =
      (n + 1 : ℝ) * A.coeff (n + 1) := by
    simpa [S, Polynomial.coeff_coe, coeff_derivative,
      mul_comm] using hcoeff
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff'
  rw [Finset.sum_range_succ'] at hcoeff'
  have hA0 : A.coeff 0 = 0 := chebPolynomial_zero q
  simp only [Polynomial.coeff_coe, hA0, zero_mul, Nat.sub_zero] at hcoeff'
  dsimp [S] at hcoeff'
  simp only [PowerSeries.coeff_mk, add_zero] at hcoeff'
  have hsum : (∑ i ∈ Finset.range n,
      A.coeff (i + 1) * rawMoment q (n - 1 - i)) =
      ∑ i ∈ Finset.range n,
        A.coeff (i + 1) * rawMoment q (n - (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have heq : n - 1 - i = n - (i + 1) := by omega
    rw [heq]
  rw [← hsum] at hcoeff'
  dsimp [S, A] at hcoeff'
  linear_combination hcoeff'

private def sourceMoment (n q : ℕ) : ℝ :=
  rawMoment q n / (2 * q + 1 : ℝ)

private theorem sourceMoment_recurrence (q n : ℕ) :
    sourceMoment n q = (n + 1 : ℝ) * (coeffModel n).eval (2 * q + 1 : ℝ) +
      (2 * q + 1 : ℝ) * ∑ i ∈ Finset.range n,
        (coeffModel i).eval (2 * q + 1 : ℝ) * sourceMoment (n - 1 - i) q := by
  let m : ℝ := 2 * q + 1
  have hm : m ≠ 0 := by dsimp [m]; positivity
  have hr := rawMoment_recurrence q n
  have hc (i : ℕ) : (chebPolynomial q).coeff (i + 1) =
      m * (coeffModel i).eval m := chebyshev_coeff_model q i
  have hsum : (∑ i ∈ Finset.range n,
      (chebPolynomial q).coeff (i + 1) * rawMoment q (n - 1 - i)) =
      m ^ 2 * ∑ i ∈ Finset.range n,
        (coeffModel i).eval m * sourceMoment (n - 1 - i) q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc]
    dsimp [sourceMoment]
    field_simp
    ring
  rw [hc n, hsum] at hr
  change rawMoment q n / m =
    (n + 1 : ℝ) * (coeffModel n).eval m +
      m * ∑ i ∈ Finset.range n,
        (coeffModel i).eval m * sourceMoment (n - 1 - i) q
  apply (div_eq_iff hm).mpr
  calc
    rawMoment q n = (n + 1 : ℝ) *
        (m * (coeffModel n).eval m) +
        m ^ 2 * ∑ i ∈ Finset.range n,
          (coeffModel i).eval m * sourceMoment (n - 1 - i) q := hr
    _ = _ := by ring

private theorem sourceMoment_eq_model (n q : ℕ) :
    sourceMoment n q = (momentModel n).eval (2 * q + 1 : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        rw [sourceMoment_recurrence q 0, momentModel_zero]
        simp [coeffModel, derivativeModel]
      rw [sourceMoment_recurrence q n, momentModel_eq n hn]
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_finsetSum]
      congr 1
      apply congrArg (fun x : ℝ => (2 * q + 1 : ℝ) * x)
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      rw [ih (n - 1 - i) (by omega)]

def simplifiedVerlinde (r q : ℕ) : ℝ :=
  (2 * q + 1 : ℝ)⁻¹ *
    ∑ j ∈ Finset.range (2 * q + 1),
      (-1 : ℝ) ^ (r * j) *
        (Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.pi /
          (2 * (2 * q + 1 : ℕ)))) ^ (2 - (r : ℤ))

private theorem sourceTerm_eq_node (n q j : ℕ) :
    (-1 : ℝ) ^ ((n + 3) * j) *
      (Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.pi /
        (2 * (2 * q + 1 : ℕ)))) ^ (2 - (((n + 3 : ℕ) : ℤ))) =
      (node q j)⁻¹ ^ (n + 1) := by
  let s : ℝ := Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.pi /
    (2 * (2 * q + 1 : ℕ)))
  have hsign : (-1 : ℝ) ^ ((n + 3) * j) = ((-1 : ℝ) ^ j) ^ (n + 1) := by
    calc
      (-1 : ℝ) ^ ((n + 3) * j) =
          (-1 : ℝ) ^ (j * (n + 1) + 2 * j) := by congr 1; ring
      _ = (-1 : ℝ) ^ (j * (n + 1)) := by
        rw [pow_add]
        simp [pow_mul]
      _ = ((-1 : ℝ) ^ j) ^ (n + 1) := by rw [pow_mul]
  have hpow : s ^ (2 - (((n + 3 : ℕ) : ℤ))) = s⁻¹ ^ (n + 1) := by
    have he : 2 - (((n + 3 : ℕ) : ℤ)) = -((n + 1 : ℕ) : ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast, inv_pow]
  change (-1 : ℝ) ^ ((n + 3) * j) * s ^ (2 - (((n + 3 : ℕ) : ℤ))) = _
  rw [hsign, hpow]
  unfold node
  change ((-1 : ℝ) ^ j) ^ (n + 1) * s⁻¹ ^ (n + 1) =
    (((-1 : ℝ) ^ j * s)⁻¹) ^ (n + 1)
  rw [mul_inv_rev, mul_pow]
  have hi : ((-1 : ℝ) ^ j)⁻¹ = (-1 : ℝ) ^ j := by
    rcases neg_one_pow_eq_or ℝ j with h | h <;> simp [h]
  rw [hi]
  ring

private theorem simplifiedVerlinde_eq_sourceMoment (n q : ℕ) :
    simplifiedVerlinde (n + 3) q = sourceMoment n q := by
  have hsum : (∑ j ∈ Finset.range (2 * q + 1),
      (-1 : ℝ) ^ ((n + 3) * j) *
        (Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.pi /
          (2 * (2 * q + 1 : ℕ)))) ^ (2 - (((n + 3 : ℕ) : ℤ)))) =
      ∑ j ∈ Finset.range (2 * q + 1), (node q j)⁻¹ ^ (n + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact sourceTerm_eq_node n q j
  unfold simplifiedVerlinde sourceMoment rawMoment
  rw [hsum, div_eq_mul_inv]
  ring

private def rowPolynomial (n : ℕ) : ℝ[X] :=
  (momentModel n).comp (2 * X + 1)

private theorem rowPolynomial_degree_le (n : ℕ) :
    (rowPolynomial n).natDegree ≤ n := by
  unfold rowPolynomial
  have hinner : (2 * X + 1 : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans (max_le
      (by exact (natDegree_C_mul_le (2 : ℝ) (X : ℝ[X])).trans natDegree_X_le)
      (by simp))
  have h := natDegree_comp_le (p := momentModel n) (q := (2 * X + 1 : ℝ[X]))
  nlinarith [momentModel_degree_le n]

private theorem rowPolynomial_reflection (n : ℕ) :
    (rowPolynomial n).comp (-1 - X) = (-1 : ℝ) ^ n • rowPolynomial n := by
  unfold rowPolynomial
  rw [comp_assoc]
  have hinner : (2 * X + 1 : ℝ[X]).comp (-1 - X) = -(2 * X + 1) := by
    simp [add_comp, mul_comp]
    ring
  rw [hinner, show -(2 * X + 1 : ℝ[X]) = (-X).comp (2 * X + 1) by simp,
    ← comp_assoc, momentModel_parity]
  simp [mul_comp, Polynomial.smul_eq_C_mul]

private theorem rowPolynomial_zero (n : ℕ) : (rowPolynomial n).eval 0 = 1 := by
  have hsource : sourceMoment n 0 = 1 := by
    simp [sourceMoment, rawMoment, node, Real.sin_pi_div_two]
  rw [sourceMoment_eq_model] at hsource
  simpa [rowPolynomial] using hsource

theorem result (n : ℕ) :
    ∃ r : ℝ[X], r.natDegree = n ∧
      (PowerSeries.mk (fun q => simplifiedVerlinde (n + 3) q)) *
        (1 - PowerSeries.X) ^ (n + 1) = (r : PowerSeries ℝ) ∧
      ∀ j ≤ n, r.coeff j = r.coeff (n - j) := by
  obtain ⟨r, hdeg, hseries, hpal⟩ :=
    PolynomialReflectionNumerator.palindromic_numerator_of_reflection
      n (rowPolynomial n) (rowPolynomial_degree_le n)
      (rowPolynomial_reflection n) (rowPolynomial_zero n)
  refine ⟨r, hdeg, ?_, hpal⟩
  change PowerSeries.mk (fun q => (rowPolynomial n).eval (q : ℝ)) *
    (1 - PowerSeries.X) ^ (n + 1) = (r : PowerSeries ℝ) at hseries
  convert hseries using 2
  congr 1
  ext q
  rw [simplifiedVerlinde_eq_sourceMoment, sourceMoment_eq_model]
  simp [rowPolynomial]

end D5.S3.Analytic.OeisA398690Palindromic
