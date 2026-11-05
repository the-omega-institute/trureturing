/- GID: D5/S3/Analytic/Interpolation/SublinearMomentGrowth
   generality: I
   mirror-B: D5/B/S3/Analytic/Interpolation/SublinearMomentGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Group.ForwardDiff, mathlib/module/Mathlib.Topology.Order.Compact]
   utility: none
   digest: Subexponential growth from sublinear-order finite atomic moment positivity. -/

import D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Truncated Newton remainders, translated Gram bounds and finite dyadic lifting. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset Filter Function Real
open scoped BigOperators ComplexConjugate Topology fwdDiff

namespace D5.S3.Analytic.Interpolation.SublinearMomentGrowth

open D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis

/-- Finite summation by parts, including the empty sum. -/
private lemma finite_summation_by_parts (w a : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range N, (w j - w (j + 1)) * a j) =
      w 0 * a 0 - w N * a N +
        ∑ j ∈ range N, w (j + 1) * (a (j + 1) - a j) := by
  calc
    _ = (∑ j ∈ range N, (w j * a j - w (j + 1) * a (j + 1))) +
        ∑ j ∈ range N, w (j + 1) * (a (j + 1) - a j) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [sum_range_sub' (fun j => w j * a j) N]

/--
One finite summation-by-parts step for the exact remainder. The terminal
coefficient is `choose (p-1) p = 0`, rather than an omitted boundary term.
-/
private lemma binomial_remainder_step (a : ℕ → ℝ) (n p : ℕ)
    (hp : 1 ≤ p) (hpn : p ≤ n) :
    (∑ j ∈ range (n - p + 1),
      ((n - 1 - j).choose (p - 1) : ℝ) * a j) =
      (n.choose p : ℝ) * a 0 +
        ∑ j ∈ range (n - p),
          ((n - 1 - j).choose p : ℝ) * (a (j + 1) - a j) := by
  have hc (j : ℕ) (hj : j ∈ range (n - p + 1)) :
      ((n - j).choose p : ℝ) - ((n - (j + 1)).choose p : ℝ) =
        ((n - 1 - j).choose (p - 1) : ℝ) := by
    have hjn : j < n := by have := mem_range.mp hj; omega
    have hn : n - j = (n - 1 - j) + 1 := by omega
    have hn' : n - (j + 1) = n - 1 - j := by omega
    have hp' : p - 1 + 1 = p := by omega
    have hpas := congrArg (fun z : ℕ => (z : ℝ))
      (Nat.choose_succ_succ' (n - 1 - j) (p - 1))
    rw [hp', ← hn, Nat.cast_add] at hpas
    rw [hn']
    linarith
  have hz : ((n - (n - p + 1)).choose p : ℝ) = 0 := by
    rw [show n - (n - p + 1) = p - 1 by omega,
      Nat.choose_eq_zero_of_lt (by omega)]
    simp
  calc
    _ = ∑ j ∈ range (n - p + 1),
        (((n - j).choose p : ℝ) - ((n - (j + 1)).choose p : ℝ)) * a j := by
      apply sum_congr rfl
      intro j hj
      rw [hc j hj]
    _ = (n.choose p : ℝ) * a 0 +
        ∑ j ∈ range (n - p),
          ((n - 1 - j).choose p : ℝ) * (a (j + 1) - a j) := by
      rw [finite_summation_by_parts, Nat.sub_zero, hz, zero_mul, sub_zero,
        sum_range_succ, hz, zero_mul, add_zero]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [show n - (j + 1) = n - 1 - j by omega]

private lemma shift_eq_value_add_sum_diff (f : ℝ → ℝ) (r : ℝ) (n : ℕ) :
    f ((n : ℝ) + r) = f r +
      ∑ j ∈ range n, fwdDiff (1 : ℝ) f (r + j) := by
  have h := finite_summation_by_parts (fun _ => 1) (fun j => f (r + j)) n
  simp only [sub_self, zero_mul, sum_const_zero, one_mul,
    Nat.cast_zero, add_zero] at h
  have hs : (∑ j ∈ range n, (f (r + (j + 1 : ℕ)) - f (r + j))) =
      ∑ j ∈ range n, fwdDiff (1 : ℝ) f (r + j) := by
    apply sum_congr rfl
    intro j hj
    simp only [fwdDiff, Nat.cast_add, Nat.cast_one, add_assoc]
  rw [hs] at h
  rw [add_comm (n : ℝ) r]
  linarith

/--
The exact positive-coefficient truncated Newton remainder, for arbitrary `f`.
There is no continuity, growth, derivative, or infinite-series premise.
-/
private lemma truncated_newton (f : ℝ → ℝ) (n p : ℕ) (r : ℝ)
    (hp : 1 ≤ p) (hpn : p ≤ n) :
    f ((n : ℝ) + r) =
      (∑ k ∈ range p, (n.choose k : ℝ) *
        (fwdDiff (1 : ℝ))^[k] f r) +
      ∑ j ∈ range (n - p + 1),
        ((n - 1 - j).choose (p - 1) : ℝ) *
          (fwdDiff (1 : ℝ))^[p] f (r + j) := by
  revert hpn
  induction p, hp using Nat.le_induction with
  | base =>
      intro hn
      simpa only [sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul,
        Function.iterate_zero_apply, Function.iterate_one, Nat.sub_self,
        show n - 1 + 1 = n by omega] using shift_eq_value_add_sum_diff f r n
  | succ p hp ih =>
      intro hn
      have hs := binomial_remainder_step
        (fun j => (fwdDiff (1 : ℝ))^[p] f (r + j)) n p hp (by omega)
      have hd (j : ℕ) :
          (fwdDiff (1 : ℝ))^[p] f (r + (j + 1 : ℕ)) -
              (fwdDiff (1 : ℝ))^[p] f (r + j) =
            (fwdDiff (1 : ℝ))^[p + 1] f (r + j) := by
        simp only [Function.iterate_succ_apply', fwdDiff,
          Nat.cast_add, Nat.cast_one, add_assoc]
      simp_rw [hd] at hs
      simp only [Nat.cast_zero, add_zero] at hs
      rw [ih (by omega), hs, sum_range_succ,
        show n - (p + 1) + 1 = n - p by omega,
        show p + 1 - 1 = p by omega]
      ring

/-- The exact diagonal coefficient sum; also covers `p=n`. -/
private lemma remainder_coefficient_sum (n p : ℕ) (hp : 1 ≤ p) (hpn : p ≤ n) :
    (∑ j ∈ range (n - p + 1),
      ((n - 1 - j).choose (p - 1) : ℝ)) = (n.choose p : ℝ) := by
  have h := binomial_remainder_step (fun _ => 1) n p hp hpn
  simpa only [mul_one, sub_self, mul_zero, sum_const_zero, add_zero] using h

/-- A finite inequality consuming the exact identity and its coefficient sum. -/
private lemma truncated_newton_abs_le (f : ℝ → ℝ) (n p : ℕ) (r : ℝ)
    (hp : 1 ≤ p) (hpn : p ≤ n) (A : ℕ → ℝ) (B : ℝ)
    (hA : ∀ k ∈ range p, |(fwdDiff (1 : ℝ))^[k] f r| ≤ A k)
    (hB : ∀ j ∈ range (n - p + 1),
      |(fwdDiff (1 : ℝ))^[p] f (r + j)| ≤ B) :
    |f ((n : ℝ) + r)| ≤
      (∑ k ∈ range p, (n.choose k : ℝ) * A k) + (n.choose p : ℝ) * B := by
  rw [truncated_newton f n p r hp hpn]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hA k hk) (Nat.cast_nonneg _)
  · calc
      _ ≤ ∑ j ∈ range (n - p + 1),
          |((n - 1 - j).choose (p - 1) : ℝ) *
            (fwdDiff (1 : ℝ))^[p] f (r + j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range (n - p + 1),
          ((n - 1 - j).choose (p - 1) : ℝ) * B := by
        apply sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hB j hj) (Nat.cast_nonneg _)
      _ = (n.choose p : ℝ) * B := by
        rw [← sum_mul, remainder_coefficient_sum n p hp hpn]

/-- The translated version of the convolution identity. -/
private lemma double_weighted_shift_translate (k : ℕ) (g : ℝ → ℝ) (u : ℝ) :
    ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
      weight k i * weight k j * g (u + (i : ℝ) - j) =
      (-1 : ℝ) ^ k * (fwdDiff (1 : ℝ))^[2 * k] g (u - k) := by
  have h := double_weighted_shift k (fun x : ℝ => g (x + u))
  rw [fwdDiff_iter_comp_add] at h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

/-- Every translated power of degree below `k` is killed by the stencil. -/
private lemma stencil_moment_zero (k r : ℕ) (x : ℝ) (hr : r < k) :
    ∑ j ∈ range (k + 1), weight k j * (x + j) ^ r = 0 := by
  change (∑ j ∈ range (k + 1), weight k j * (fun y : ℝ => y ^ r) (x + j)) = 0
  rw [weighted_shift k (fun y : ℝ => y ^ r) x, fwdDiff_iter_pow_eq_zero_of_lt hr]
  simp

private lemma stencil_weight_abs (k j : ℕ) :
    |weight k j| = (k.choose j : ℝ) := by
  rw [weight, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]

private lemma stencil_weight_abs_sum (k : ℕ) :
    (∑ j ∈ range (k + 1), |weight k j|) = (2 : ℝ) ^ k := by
  simp_rw [stencil_weight_abs]
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

/-- The exact finite family telescope from the original hypothesis. -/
def momentPositive (F : ℝ → ℝ) (m : ℝ → ℕ) : Prop :=
  ∀ᶠ D : ℝ in atTop,
    ∀ (n : ℕ) (x : Fin n → ℝ) (a : Fin n → ℂ),
      (∀ i, 0 ≤ x i ∧ x i ≤ D) →
      (∀ r : ℕ, r < m D →
        ∑ i, a i * ((x i : ℂ) ^ r) = 0) →
      0 ≤ (∑ i, ∑ j,
        a i * conj (a j) * (F (x i - x j) : ℂ)).re

/-- The compact envelope, finite on nonnegative radii by continuity. -/
private def envelope (F : ℝ → ℝ) (R : ℝ) : ℝ :=
  max 1 (sSup ((fun x : ℝ => |F x|) '' Set.Icc 0 R))

private lemma abs_le_envelope {F : ℝ → ℝ} (hF : Continuous F)
    {R x : ℝ} (hx : x ∈ Set.Icc 0 R) : |F x| ≤ envelope F R := by
  exact (le_csSup (isCompact_Icc.bddAbove_image hF.abs.continuousOn)
    (Set.mem_image_of_mem (fun y : ℝ => |F y|) hx)).trans (le_max_right _ _)

private lemma envelope_mono {F : ℝ → ℝ} (hF : Continuous F)
    {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) : envelope F R ≤ envelope F S := by
  refine max_le (le_max_left _ _) ?_
  refine csSup_le ⟨|F 0|, ⟨0, ⟨le_rfl, hR⟩, rfl⟩⟩ ?_
  rintro y ⟨x, hx, rfl⟩
  exact abs_le_envelope hF ⟨hx.1, hx.2.trans hRS⟩

private lemma abs_le_envelope_of_even {F : ℝ → ℝ} (hF : Continuous F)
    (heven : ∀ t : ℝ, F (-t) = F t) {R x : ℝ} (hx : |x| ≤ R) :
    |F x| ≤ envelope F R := by
  have h := abs_le_envelope hF ⟨abs_nonneg x, hx⟩
  rcases le_total 0 x with hx0 | hx0
  · simpa only [abs_of_nonneg hx0] using h
  · simpa only [abs_of_nonpos hx0, heven] using h

/--
Transport the given `Fin n` hypothesis to an arbitrary finite index type.
Only the indices are bijected. In particular, no injectivity of `x` is used.
-/
private lemma real_quadratic_nonneg {F : ℝ → ℝ} {D : ℝ} {k : ℕ}
    (hD : ∀ (n : ℕ) (x : Fin n → ℝ) (a : Fin n → ℂ),
      (∀ i, 0 ≤ x i ∧ x i ≤ D) →
      (∀ r : ℕ, r < k → ∑ i, a i * ((x i : ℂ) ^ r) = 0) →
      0 ≤ (∑ i, ∑ j, a i * conj (a j) * (F (x i - x j) : ℂ)).re)
    {ι : Type*} [Fintype ι] (x a : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ D)
    (ha : ∀ r : ℕ, r < k → ∑ i, a i * (x i) ^ r = 0) :
    0 ≤ ∑ i, ∑ j, a i * a j * F (x i - x j) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hm (r : ℕ) (hr : r < k) :
      ∑ i : Fin (Fintype.card ι),
        (a (e.symm i) : ℂ) * (x (e.symm i) : ℂ) ^ r = 0 := by
    rw [e.symm.sum_comp (fun i : ι => (a i : ℂ) * (x i : ℂ) ^ r)]
    have h := congrArg (fun y : ℝ => (y : ℂ)) (ha r hr)
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_zero] using h
  have h := hD (Fintype.card ι) (fun i => x (e.symm i))
    (fun i => (a (e.symm i) : ℂ)) (fun i => hx (e.symm i)) hm
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re] at h
  have hsum : (∑ i : Fin (Fintype.card ι), ∑ j : Fin (Fintype.card ι),
      a (e.symm i) * a (e.symm j) * F (x (e.symm i) - x (e.symm j))) =
      ∑ i : ι, ∑ j : ι, a i * a j * F (x i - x j) := by
    apply Fintype.sum_equiv e.symm
    intro i
    exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)
  rwa [hsum] at h

/-- The convolution retains the individual stencil indices. -/
private def stencilConvolution (F : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
    weight k i * weight k j * F (u + (i : ℝ) - j)

private lemma stencil_convolution_difference (F : ℝ → ℝ) (k : ℕ) (u : ℝ) :
    stencilConvolution F k u =
      (-1 : ℝ) ^ k * (fwdDiff (1 : ℝ))^[2 * k] F (u - k) := by
  unfold stencilConvolution
  simpa only [Finset.sum_range] using double_weighted_shift_translate k F u

private lemma stencil_convolution_neg (F : ℝ → ℝ)
    (heven : ∀ t : ℝ, F (-t) = F t) (k : ℕ) (u : ℝ) :
    stencilConvolution F k (-u) = stencilConvolution F k u := by
  unfold stencilConvolution
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [show -u + (j : ℝ) - i = -(u + (i : ℝ) - j) by ring, heven]
  ring

private lemma scaled_stencil_pair (F : ℝ → ℝ) (k : ℕ) (s t u v : ℝ) :
    (∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
      (s * weight k i) * (t * weight k j) *
        F ((u + (i : ℝ)) - (v + (j : ℝ)))) =
      (s * t) * stencilConvolution F k (u - v) := by
  unfold stencilConvolution
  simp only [mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [show (u + (i : ℝ)) - (v + (j : ℝ)) =
    u - v + (i : ℝ) - j by ring]
  ring

/--
Apply positivity to the sum and difference of the two translated stencils.
The two blocks have the same diagonal, so both signs suffice even if it is zero.
-/
private lemma stencil_gram_bound {F : ℝ → ℝ} {D : ℝ} (k : ℕ)
    (heven : ∀ t : ℝ, F (-t) = F t)
    (hD : ∀ (n : ℕ) (x : Fin n → ℝ) (a : Fin n → ℂ),
      (∀ i, 0 ≤ x i ∧ x i ≤ D) →
      (∀ r : ℕ, r < k → ∑ i, a i * ((x i : ℂ) ^ r) = 0) →
      0 ≤ (∑ i, ∑ j, a i * conj (a j) * (F (x i - x j) : ℂ)).re)
    {u : ℝ} (hu : 0 ≤ u) (huD : u + k ≤ D) :
    |stencilConvolution F k u| ≤ stencilConvolution F k 0 := by
  classical
  let x : Fin (k + 1) ⊕ Fin (k + 1) → ℝ :=
    Sum.elim (fun i => 0 + (i : ℝ)) (fun i => u + (i : ℝ))
  have hx : ∀ i, 0 ≤ x i ∧ x i ≤ D := by
    intro i
    cases i with
    | inl i =>
        have hi : (i : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
        have hi0 : (0 : ℝ) ≤ i := by positivity
        dsimp [x]
        constructor <;> linarith
    | inr i =>
        have hi : (i : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
        have hi0 : (0 : ℝ) ≤ i := by positivity
        dsimp [x]
        constructor <;> linarith
  have hq (s : ℝ) :
      0 ≤ (1 + s * s) * stencilConvolution F k 0 +
        2 * s * stencilConvolution F k u := by
    let a : Fin (k + 1) ⊕ Fin (k + 1) → ℝ :=
      Sum.elim (fun i => 1 * weight k i) (fun i => s * weight k i)
    have ha : ∀ r : ℕ, r < k → ∑ i, a i * (x i) ^ r = 0 := by
      intro r hr
      have hzero (v : ℝ) :
          (∑ i : Fin (k + 1), weight k i * (v + (i : ℝ)) ^ r) = 0 := by
        simpa only [Finset.sum_range] using stencil_moment_zero k r v hr
      simp only [a, x, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul]
      simp_rw [mul_assoc, ← mul_sum]
      rw [hzero 0, hzero u, mul_zero, add_zero]
    have h := real_quadratic_nonneg hD x a hx ha
    simp only [a, x, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      sum_add_distrib] at h
    rw [scaled_stencil_pair, scaled_stencil_pair, scaled_stencil_pair,
      scaled_stencil_pair] at h
    simp only [sub_self, zero_sub, sub_zero,
      stencil_convolution_neg F heven k u] at h
    nlinarith [h]
  have hplus := hq 1
  have hminus := hq (-1)
  apply abs_le.mpr
  constructor <;> nlinarith

private lemma stencil_diagonal_le {F : ℝ → ℝ} (hF : Continuous F)
    (heven : ∀ t : ℝ, F (-t) = F t) (k : ℕ) :
    |stencilConvolution F k 0| ≤ (2 : ℝ) ^ (2 * k) * envelope F k := by
  have hw : (∑ i : Fin (k + 1), |weight k i|) = (2 : ℝ) ^ k := by
    simpa only [Finset.sum_range] using stencil_weight_abs_sum k
  calc
    _ ≤ ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
        |weight k i * weight k j * F (0 + (i : ℝ) - j)| := by
      unfold stencilConvolution
      exact (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun i hi => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
        |weight k i| * |weight k j| * envelope F k := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hi' : (i : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
      have hj' : (j : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
      have hi0 : (0 : ℝ) ≤ i := by positivity
      have hj0 : (0 : ℝ) ≤ j := by positivity
      have harg : |0 + (i : ℝ) - j| ≤ (k : ℝ) := by
        apply abs_le.mpr
        constructor <;> linarith
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le_envelope_of_even hF heven harg)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i : Fin (k + 1), |weight k i|) *
        (∑ j : Fin (k + 1), |weight k j|) * envelope F k := by
      simp only [sum_mul, mul_sum, mul_assoc, mul_left_comm]
    _ = (2 : ℝ) ^ (2 * k) * envelope F k := by
      rw [hw, ← pow_add, show k + k = 2 * k by omega]

/-- Local estimate at the order occurring in the positivity telescope. -/
private lemma finite_stencil_bound {F : ℝ → ℝ} (hF : Continuous F)
    (heven : ∀ t : ℝ, F (-t) = F t) {D : ℝ} (k : ℕ)
    (hD : ∀ (n : ℕ) (x : Fin n → ℝ) (a : Fin n → ℂ),
      (∀ i, 0 ≤ x i ∧ x i ≤ D) →
      (∀ r : ℕ, r < k → ∑ i, a i * ((x i : ℂ) ^ r) = 0) →
      0 ≤ (∑ i, ∑ j, a i * conj (a j) * (F (x i - x j) : ℂ)).re)
    {v : ℝ} (hv : 0 ≤ v) (hvD : v + 2 * k ≤ D) :
    |(fwdDiff (1 : ℝ))^[2 * k] F v| ≤
      (2 : ℝ) ^ (2 * k) * envelope F k := by
  have hgram := stencil_gram_bound k heven hD
    (u := v + k) (by positivity) (by nlinarith)
  have hd : |stencilConvolution F k (v + k)| =
      |(fwdDiff (1 : ℝ))^[2 * k] F v| := by
    rw [stencil_convolution_difference, add_sub_cancel_right, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul]
  calc
    _ = |stencilConvolution F k (v + k)| := hd.symm
    _ ≤ stencilConvolution F k 0 := hgram
    _ ≤ |stencilConvolution F k 0| := le_abs_self _
    _ ≤ (2 : ℝ) ^ (2 * k) * envelope F k := stencil_diagonal_le hF heven k

private lemma difference_le_envelope {F : ℝ → ℝ} (hF : Continuous F)
    (q : ℕ) {r R : ℝ} (hr : 0 ≤ r) (hrq : r + q ≤ R) :
    |(fwdDiff (1 : ℝ))^[q] F r| ≤ (2 : ℝ) ^ q * envelope F R := by
  calc
    _ = |∑ j ∈ range (q + 1), weight q j * F (r + j)| := by
      rw [weighted_shift, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    _ ≤ ∑ j ∈ range (q + 1), |weight q j * F (r + j)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (q + 1), |weight q j| * envelope F R := by
      apply sum_le_sum
      intro j hj
      have hjq : (j : ℝ) ≤ q := by exact_mod_cast (Nat.le_of_lt_succ (mem_range.mp hj))
      have hj0 : (0 : ℝ) ≤ j := by positivity
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le_envelope hF ⟨by linarith, by linarith⟩)
        (abs_nonneg _)
    _ = (2 : ℝ) ^ q * envelope F R := by
      rw [← sum_mul, stencil_weight_abs_sum]

/--
Finite Newton envelope estimate. Its high difference bound is derived from
positivity at `D = n+r` with order exactly `k`. The low differences use only
continuity on `[0,2k+1]`. Thus both finite joins above are consumed here.
-/
private lemma finite_newton_envelope {F : ℝ → ℝ} (hF : Continuous F)
    (heven : ∀ t : ℝ, F (-t) = F t) (k n : ℕ) (r : ℝ)
    (hk : 1 ≤ k) (hkn : 2 * k ≤ n) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hD : ∀ (N : ℕ) (x : Fin N → ℝ) (a : Fin N → ℂ),
      (∀ i, 0 ≤ x i ∧ x i ≤ (n : ℝ) + r) →
      (∀ s : ℕ, s < k → ∑ i, a i * ((x i : ℂ) ^ s) = 0) →
      0 ≤ (∑ i, ∑ j, a i * conj (a j) * (F (x i - x j) : ℂ)).re) :
    |F ((n : ℝ) + r)| ≤ envelope F (2 * k + 1 : ℕ) *
      ∑ q ∈ range (2 * k + 1), (2 : ℝ) ^ q * (n.choose q : ℝ) := by
  have hlow (q : ℕ) (hq : q ∈ range (2 * k)) :
      |(fwdDiff (1 : ℝ))^[q] F r| ≤
        (2 : ℝ) ^ q * envelope F (2 * k + 1 : ℕ) := by
    have hq' : (q : ℝ) ≤ (2 * k : ℕ) := by
      exact_mod_cast (Nat.le_of_lt (mem_range.mp hq))
    apply difference_le_envelope hF q hr0
    push_cast
    push_cast at hq'
    linarith
  have hM : envelope F k ≤ envelope F (2 * k + 1 : ℕ) := by
    apply envelope_mono hF (by positivity)
    exact_mod_cast (show k ≤ 2 * k + 1 by omega)
  have hhigh (j : ℕ) (hj : j ∈ range (n - 2 * k + 1)) :
      |(fwdDiff (1 : ℝ))^[2 * k] F (r + j)| ≤
        (2 : ℝ) ^ (2 * k) * envelope F (2 * k + 1 : ℕ) := by
    have hj' : (j : ℝ) + (2 * k : ℕ) ≤ (n : ℝ) := by
      exact_mod_cast (show j + 2 * k ≤ n by have := mem_range.mp hj; omega)
    have hbound := finite_stencil_bound hF heven k hD
      (v := r + j) (by positivity) (by push_cast at hj' ⊢; linarith)
    exact hbound.trans (mul_le_mul_of_nonneg_left hM (by positivity))
  calc
    _ ≤ (∑ q ∈ range (2 * k), (n.choose q : ℝ) *
        ((2 : ℝ) ^ q * envelope F (2 * k + 1 : ℕ))) +
        (n.choose (2 * k) : ℝ) *
          ((2 : ℝ) ^ (2 * k) * envelope F (2 * k + 1 : ℕ)) :=
      truncated_newton_abs_le F n (2 * k) r (by omega) hkn
        (fun q => (2 : ℝ) ^ q * envelope F (2 * k + 1 : ℕ))
        ((2 : ℝ) ^ (2 * k) * envelope F (2 * k + 1 : ℕ)) hlow hhigh
    _ = envelope F (2 * k + 1 : ℕ) *
        ∑ q ∈ range (2 * k + 1), (2 : ℝ) ^ q * (n.choose q : ℝ) := by
      rw [sum_range_succ, mul_add, mul_sum]
      congr 1
      · apply sum_congr rfl
        intro q hq
        ring
      · ring

/--
Specialize at every sufficiently large real `t`, with `n=floor t` and
`r=t-floor t`. The order need not be monotone. The extra radius inequality is
what permits comparison with `M(t/2)` in the analytic lifting below.
-/
private lemma eventual_newton_envelope {F : ℝ → ℝ} {m : ℝ → ℕ}
    (hF : Continuous F) (heven : ∀ t : ℝ, F (-t) = F t)
    (hm : ∀ᶠ t : ℝ in atTop, 1 ≤ m t)
    (hsub : Tendsto (fun t : ℝ => (m t : ℝ) / t) atTop (𝓝 0))
    (hpos : momentPositive F m) :
    ∀ᶠ t : ℝ in atTop,
      ((2 * m t + 1 : ℕ) : ℝ) ≤ t / 2 ∧
      |F t| ≤ envelope F (2 * m t + 1 : ℕ) *
        ∑ q ∈ range (2 * m t + 1),
          (2 : ℝ) ^ q * ((Nat.floor t).choose q : ℝ) := by
  have hsmall : ∀ᶠ t : ℝ in atTop, (m t : ℝ) / t < (1 / 8 : ℝ) :=
    hsub.eventually_lt_const (by norm_num)
  filter_upwards [hpos, hm, hsmall, eventually_ge_atTop (4 : ℝ)] with t hD hm' hs ht
  have ht0 : 0 < t := by linarith
  have hmt : (m t : ℝ) < t / 8 := by
    have h := (div_lt_iff₀ ht0).mp hs
    linarith
  have horder : ((2 * m t + 1 : ℕ) : ℝ) ≤ t / 2 := by
    push_cast
    linarith
  have hkn : 2 * m t ≤ Nat.floor t := by
    apply Nat.le_floor
    push_cast
    linarith
  have hfloor := Nat.floor_le ht0.le
  have hr0 : 0 ≤ t - (Nat.floor t : ℝ) := sub_nonneg.mpr hfloor
  have hr1 : t - (Nat.floor t : ℝ) ≤ 1 := by
    linarith [Nat.lt_floor_add_one t]
  have heq : (Nat.floor t : ℝ) + (t - (Nat.floor t : ℝ)) = t := by ring
  refine ⟨horder, ?_⟩
  have h := finite_newton_envelope hF heven (m t) (Nat.floor t)
    (t - (Nat.floor t : ℝ)) hm' hkn hr0 hr1 (by simpa only [heq] using hD)
  simpa only [heq] using h

/-- A fixed auxiliary generating-function parameter suffices; it is not a
fixed moment order. The bound is deliberately weaker than the optimized
entropy bound, but has the same sublinear-order consequence. -/
private lemma binomial_sum_exp (n p : ℕ) (z : ℝ) (hpn : p ≤ n)
    (hz : 0 < z) (hz1 : z ≤ 1) :
    (∑ q ∈ range (p + 1), (2 : ℝ) ^ q * (n.choose q : ℝ)) ≤
      exp ((p : ℝ) / z + 2 * (n : ℝ) * z) := by
  have hweighted :
      z ^ p * (∑ q ∈ range (p + 1), (2 : ℝ) ^ q * (n.choose q : ℝ)) ≤
        (2 * z + 1) ^ n := by
    calc
      _ = ∑ q ∈ range (p + 1), z ^ p *
          ((2 : ℝ) ^ q * (n.choose q : ℝ)) := by rw [mul_sum]
      _ ≤ ∑ q ∈ range (p + 1), (2 * z) ^ q * (n.choose q : ℝ) := by
        apply sum_le_sum
        intro q hq
        have hqp : q ≤ p := Nat.le_of_lt_succ (mem_range.mp hq)
        have hpow := pow_le_pow_of_le_one hz.le hz1 hqp
        calc
          _ ≤ z ^ q * ((2 : ℝ) ^ q * (n.choose q : ℝ)) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
          _ = _ := by rw [mul_pow]; ring
      _ ≤ ∑ q ∈ range (n + 1), (2 * z) ^ q * (n.choose q : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.add_le_add_right hpn 1))
        intro q hq hnot
        positivity
      _ = (2 * z + 1) ^ n := by
        rw [add_pow]
        simp only [one_pow, mul_one]
  have hinv : z⁻¹ ≤ exp (z⁻¹) := by linarith [add_one_le_exp (z⁻¹)]
  have hbase : 2 * z + 1 ≤ exp (2 * z) := add_one_le_exp (2 * z)
  calc
    _ = (z⁻¹) ^ p * (z ^ p *
        (∑ q ∈ range (p + 1), (2 : ℝ) ^ q * (n.choose q : ℝ))) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hz.ne', one_pow, one_mul]
    _ ≤ (z⁻¹) ^ p * (2 * z + 1) ^ n :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ ≤ exp (z⁻¹) ^ p * exp (2 * z) ^ n :=
      mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr hz.le) hinv p)
        (pow_le_pow_left₀ (by positivity) hbase n) (by positivity) (by positivity)
    _ = exp ((p : ℝ) / z + 2 * (n : ℝ) * z) := by
      rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
      congr 1
      simp only [div_eq_mul_inv]
      ring

/-- Uniform at all sufficiently large real arguments, conditional only on the
finite Newton truncation lying below floor(t). No regularity of m is used. -/
private lemma eventual_binomial_exp {m : ℝ → ℕ}
    (hsub : Tendsto (fun t : ℝ => (m t : ℝ) / t) atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, 2 * m t ≤ Nat.floor t →
      (∑ q ∈ range (2 * m t + 1),
        (2 : ℝ) ^ q * ((Nat.floor t).choose q : ℝ)) ≤ exp (η * t) := by
  let z : ℝ := min 1 (η / 6)
  have hz : 0 < z := lt_min zero_lt_one (by positivity)
  have hz1 : z ≤ 1 := min_le_left _ _
  have hzη : 3 * z ≤ η := by
    have hh : z ≤ η / 6 := min_le_right _ _
    linarith
  have hs : ∀ᶠ t : ℝ in atTop, (m t : ℝ) / t < z * z / 2 :=
    hsub.eventually_lt_const (by positivity)
  filter_upwards [hs, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  intro hpn
  have hmt : 2 * (m t : ℝ) ≤ (z * z) * t := by
    have hh := (div_lt_iff₀ ht0).mp ht
    nlinarith
  have hpz : ((2 * m t : ℕ) : ℝ) / z ≤ z * t := by
    apply (div_le_iff₀ hz).mpr
    push_cast
    nlinarith
  have hfloor : (Nat.floor t : ℝ) ≤ t := Nat.floor_le ht0.le
  have hexp : ((2 * m t : ℕ) : ℝ) / z + 2 * (Nat.floor t : ℝ) * z ≤ η * t := by
    have hnz := mul_le_mul_of_nonneg_right hfloor hz.le
    have hηt := mul_le_mul_of_nonneg_right hzη ht0.le
    nlinarith
  exact (binomial_sum_exp (Nat.floor t) (2 * m t) z hpn hz hz1).trans
    (exp_le_exp.mpr hexp)

private lemma envelope_pos (F : ℝ → ℝ) (R : ℝ) : 0 < envelope F R :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- The pointwise estimate closes both the variable-order combinatorial and
radius joins for every sufficiently large real t. -/
private lemma eventual_half_envelope {F : ℝ → ℝ} {m : ℝ → ℕ}
    (hF : Continuous F) (heven : ∀ t : ℝ, F (-t) = F t)
    (hm : ∀ᶠ t : ℝ in atTop, 1 ≤ m t)
    (hsub : Tendsto (fun t : ℝ => (m t : ℝ) / t) atTop (𝓝 0))
    (hpos : momentPositive F m) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, |F t| ≤ envelope F (t / 2) * exp (η * t) := by
  filter_upwards [eventual_newton_envelope hF heven hm hsub hpos,
    eventual_binomial_exp hsub η hη, eventually_ge_atTop (0 : ℝ)] with t hn hb ht
  have hpn : 2 * m t ≤ Nat.floor t := by
    apply Nat.le_floor
    have hr := hn.1
    push_cast at hr ⊢
    linarith
  have hrad : envelope F (2 * m t + 1 : ℕ) ≤ envelope F (t / 2) :=
    envelope_mono hF (by positivity) hn.1
  exact hn.2.trans (mul_le_mul hrad (hb hpn)
    (sum_nonneg (fun q hq => by positivity)) (envelope_pos F (t / 2)).le)

/-- A real-radius step; the small-t part is absorbed by the half-radius
compact envelope. Only compact, nonempty interval suprema are used. -/
private lemma envelope_half_step {F : ℝ → ℝ} (hF : Continuous F)
    {η T : ℝ} (hη : 0 < η) (hT : 0 < T)
    (htail : ∀ t : ℝ, T ≤ t → |F t| ≤ envelope F (t / 2) * exp (η * t))
    (R : ℝ) (hR : 2 * T ≤ R) :
    envelope F R ≤ envelope F (R / 2) * exp (η * R) := by
  have hR0 : 0 ≤ R := by linarith
  have hM0 := (envelope_pos F (R / 2)).le
  have hone : 1 ≤ exp (η * R) := one_le_exp (mul_nonneg hη.le hR0)
  have habsorb : envelope F (R / 2) ≤ envelope F (R / 2) * exp (η * R) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hM0
  refine max_le ((le_max_left _ _).trans habsorb) ?_
  refine csSup_le ⟨|F 0|, ⟨0, ⟨le_rfl, hR0⟩, rfl⟩⟩ ?_
  rintro y ⟨t, ht, rfl⟩
  by_cases htT : t ≤ T
  · exact (abs_le_envelope hF ⟨ht.1, by linarith⟩).trans habsorb
  · have htT' : T ≤ t := (lt_of_not_ge htT).le
    have hmono : envelope F (t / 2) ≤ envelope F (R / 2) :=
      envelope_mono hF (by linarith [ht.1]) (by linarith [ht.2])
    have he : exp (η * t) ≤ exp (η * R) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hη.le)
    exact (htail t htT').trans (mul_le_mul hmono he (exp_pos _).le hM0)

/-- Finite dyadic induction. At depth N only radii at most 2T*2^N are
considered, so no infinite iteration or a priori growth bound enters. The
induction invariant accounts for the geometric sum by 2ηR. -/
private lemma envelope_dyadic {F : ℝ → ℝ} (hF : Continuous F)
    {η T : ℝ} (hη : 0 < η) (hT : 0 < T)
    (hstep : ∀ R : ℝ, 2 * T ≤ R →
      envelope F R ≤ envelope F (R / 2) * exp (η * R)) :
    ∀ R : ℝ, 0 ≤ R → envelope F R ≤ envelope F (2 * T) * exp (2 * η * R) := by
  have hsmall (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 2 * T) :
      envelope F R ≤ envelope F (2 * T) * exp (2 * η * R) := by
    have hmono := envelope_mono hF hR0 hR
    have he : 1 ≤ exp (2 * η * R) := one_le_exp (by positivity)
    exact hmono.trans (by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left he (envelope_pos F (2 * T)).le)
  have hfinite : ∀ N : ℕ, ∀ R : ℝ, 0 ≤ R → R ≤ 2 * T * (2 : ℝ) ^ N →
      envelope F R ≤ envelope F (2 * T) * exp (2 * η * R) := by
    intro N
    induction N with
    | zero =>
        intro R hR0 hR
        exact hsmall R hR0 (by simpa only [pow_zero, mul_one] using hR)
    | succ N ih =>
        intro R hR0 hR
        by_cases hsmallR : R ≤ 2 * T
        · exact hsmall R hR0 hsmallR
        · have hhalf : R / 2 ≤ 2 * T * (2 : ℝ) ^ N := by
            rw [pow_succ] at hR
            nlinarith
          calc
            _ ≤ envelope F (R / 2) * exp (η * R) := hstep R (le_of_lt (lt_of_not_ge hsmallR))
            _ ≤ (envelope F (2 * T) * exp (2 * η * (R / 2))) * exp (η * R) :=
              mul_le_mul_of_nonneg_right (ih (R / 2) (by positivity) hhalf) (exp_pos _).le
            _ = envelope F (2 * T) * exp (2 * η * R) := by
              rw [mul_assoc, ← exp_add]
              congr 2
              ring
  intro R hR0
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R / (2 * T)) (by norm_num : (1 : ℝ) < 2)
  have hbound : R ≤ 2 * T * (2 : ℝ) ^ N := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 2 * T)).mp hN
    nlinarith
  exact hfinite N R hR0 hbound

/-- The original all-real subexponential conclusion, with every original
hypothesis retained. -/
theorem sublinear_moment_growth (F : ℝ → ℝ) (m : ℝ → ℕ)
    (hF : Continuous F) (heven : ∀ t : ℝ, F (-t) = F t)
    (hm : ∀ᶠ D : ℝ in atTop, 1 ≤ m D)
    (hsub : Tendsto (fun D : ℝ => (m D : ℝ) / D) atTop (𝓝 0))
    (hpos : momentPositive F m) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, |F t| ≤ C * exp (ε * |t|) := by
  intro ε hε
  have hη : 0 < ε / 2 := by positivity
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (eventual_half_envelope hF heven hm hsub hpos (ε / 2) hη)
  let T : ℝ := max 1 T₀
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have htail (t : ℝ) (ht : T ≤ t) :
      |F t| ≤ envelope F (t / 2) * exp ((ε / 2) * t) :=
    hT₀ t ((le_max_right _ _).trans ht)
  have hstep := envelope_half_step hF hη hT htail
  refine ⟨envelope F (2 * T), envelope_pos F (2 * T), ?_⟩
  intro t
  have h := envelope_dyadic hF hη hT hstep |t| (abs_nonneg t)
  have he : 2 * (ε / 2) * |t| = ε * |t| := by ring
  rw [he] at h
  exact (abs_le_envelope_of_even hF heven (R := |t|) le_rfl).trans h

end D5.S3.Analytic.Interpolation.SublinearMomentGrowth
