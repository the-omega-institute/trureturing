/- GID: D5/S3/Quantum/Schatten/WordTraceExponentBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/WordTraceExponentBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint diagonal word-trace witnesses and their common trace normalization. -/

import D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation
import D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Joint diagonal realizations retain the common coordinate labels in every assertion. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Observer.Hankel.WordHankelRealization (wordProduct)
open D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation (word_diagonal norm_diagonal)
open D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal

namespace D5.S3.Quantum.Schatten.WordTraceExponentBoundary

/-- Subsets name the actual shared coordinates, rather than four independent spectra. -/
def coordinates (q : ℕ) : Fin (2 ^ q) ≃ Finset (Fin q) :=
  Fintype.equivOfCardEq (by simp)

private lemma sum_coordinates (q : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin (2 ^ q), f ((coordinates q i).card)) =
      ∑ a ∈ range (q + 1), (q.choose a : ℝ) * f a := by
  rw [(coordinates q).sum_comp (fun S => f S.card)]
  simpa only [powerset_univ, card_univ, Fintype.card_fin, nsmul_eq_mul] using
    (sum_powerset_apply_card f (x := (univ : Finset (Fin q))))

/-- The mark is one on the positive part of the q-th difference. -/
def mark (q a : ℕ) : ℝ := if Even (q - a) then 1 else 0

private lemma mark_cases (q a : ℕ) : mark q a = 0 ∨ mark q a = 1 := by
  unfold mark
  split_ifs <;> simp

private lemma mark_sign (q a : ℕ) : 2 * mark q a - 1 = (-1 : ℝ) ^ (q - a) := by
  rw [neg_one_pow_eq_ite]
  unfold mark
  split_ifs <;> norm_num

private lemma signed_sum (q : ℕ) (u : ℝ) (f : ℝ → ℝ) :
    (∑ a ∈ range (q + 1), (q.choose a : ℝ) * (2 * mark q a - 1) * f (u + a)) =
      (fwdDiff 1)^[q] f u := by
  rw [fwdDiff_iter_eq_sum_shift]
  apply sum_congr rfl
  intro a ha
  rw [mark_sign]
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast]
  ring

/-- Source entries, with j = a + epsilon and therefore j - epsilon = a. -/
def higherDiagonal (q : ℕ) (u c : ℝ) (b : Bool) (i : Fin (2 ^ q)) : ℝ :=
  if b then c + mark q ((coordinates q i).card) else u + (coordinates q i).card

def higherOtherDiagonal (q : ℕ) (u c : ℝ) (b : Bool) (i : Fin (2 ^ q)) : ℝ :=
  if b then c + 1 - mark q ((coordinates q i).card) else u + (coordinates q i).card

private lemma higher_word_difference (q : ℕ) (u c : ℝ) (s : List Bool) :
    (wordProduct (fun b => diagonal (fun i => (higherDiagonal q u c b i : ℂ))) s).trace -
      (wordProduct (fun b => diagonal (fun i => (higherOtherDiagonal q u c b i : ℂ))) s).trace =
      ((((c + 1) ^ s.count true - c ^ s.count true) *
        (fwdDiff 1)^[q] (fun x : ℝ => x ^ s.count false) u : ℝ) : ℂ) := by
  have hw (d : Bool → Fin (2 ^ q) → ℝ) :
      wordProduct (fun b => diagonal (fun i => (d b i : ℂ))) s =
        diagonal (fun i => ((d false i ^ s.count false * d true i ^ s.count true : ℝ) : ℂ)) := by
    have hd : (fun b => diagonal (fun i => (d b i : ℂ))) =
        (fun b : Bool => if b then diagonal (fun i => (d true i : ℂ)) else
          diagonal (fun i => (d false i : ℂ))) := by
      funext b
      cases b <;> rfl
    rw [hd]
    simpa only [Bool.false_eq_true, reduceIte, Complex.ofReal_mul, Complex.ofReal_pow] using
      word_diagonal (fun i => (d false i : ℂ)) (fun i => (d true i : ℂ)) s
  rw [hw, hw, trace_diagonal, trace_diagonal, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
    ← Complex.ofReal_sub]
  congr 1
  simp only [higherDiagonal, higherOtherDiagonal, Bool.false_eq_true, reduceIte]
  rw [sum_coordinates q (fun a => (u + a) ^ s.count false * (c + mark q a) ^ s.count true),
    sum_coordinates q (fun a => (u + a) ^ s.count false * (c + 1 - mark q a) ^ s.count true),
    ← sum_sub_distrib]
  rw [← signed_sum, mul_sum]
  apply sum_congr rfl
  intro a ha
  rcases mark_cases q a with h | h <;>
    simp only [higherDiagonal, higherOtherDiagonal, Bool.false_eq_true, reduceIte] at *
  · rw [h]
    simp only [add_zero, sub_zero]
    ring
  · rw [h]
    ring

private lemma higher_sum_difference (q : ℕ) (u c : ℝ) (f : ℝ → ℝ) :
    (∑ i : Fin (2 ^ q), f (higherDiagonal q u c false i + higherDiagonal q u c true i)) -
      (∑ i : Fin (2 ^ q), f (higherOtherDiagonal q u c false i + higherOtherDiagonal q u c true i)) =
      (fwdDiff 1)^[q + 1] f (u + c) := by
  simp only [higherDiagonal, higherOtherDiagonal, Bool.false_eq_true, reduceIte]
  rw [sum_coordinates q (fun a => f (u + a + (c + mark q a))),
    sum_coordinates q (fun a => f (u + a + (c + 1 - mark q a))),
    ← sum_sub_distrib, Function.iterate_succ_apply, ← signed_sum]
  apply sum_congr rfl
  intro a ha
  rcases mark_cases q a with h | h <;>
    simp only [h, add_zero, sub_zero, add_sub_cancel_right, fwdDiff,
      add_assoc, add_left_comm, add_comm] <;> ring

private lemma power_smooth (p : ℝ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (iteratedDeriv n (fun y : ℝ => y ^ p)) x := by
  have he : iteratedDeriv n (fun y : ℝ => y ^ p) =
      fun y : ℝ => (descPochhammer ℝ n).eval p * y ^ (p - n) := by
    funext y
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  rw [he]
  exact ((Real.hasDerivAt_rpow_const (p := p - n) (Or.inl hx.ne')).const_mul _).differentiableAt

private lemma power_difference_negative (q : ℕ) (hq : 1 ≤ q) (p x : ℝ)
    (hx : 0 < x) (hp : (q : ℝ) - 1 < p) (hp' : p < q) :
    (fwdDiff 1)^[q + 1] (fun y : ℝ => y ^ p) x < 0 := by
  obtain ⟨y, hy, he⟩ := exists_fwd_diff_iter_eq_iterated_deriv
    (fun y : ℝ => y ^ p) (q + 1) (x := x) (by norm_num : (0 : ℝ) < 1)
    (fun n _ y hy => power_smooth p n y (lt_of_lt_of_le hx hy.1))
  rw [he, one_pow, one_mul, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const,
    descPochhammer_eval_eq_prod_range, prod_range_succ]
  have hprod : 0 < ∏ a ∈ range q, (p - a) := by
    apply prod_pos
    intro a ha
    have ha' : (a : ℝ) ≤ (q : ℝ) - 1 := by
      have : a + 1 ≤ q := mem_range.mp ha
      have ht : (a : ℝ) + 1 ≤ q := by exact_mod_cast this
      linarith
    linarith
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hprod (sub_neg.mpr hp'))
    (Real.rpow_pos_of_pos (lt_of_lt_of_le hx hy.1) _)

private lemma nat_power_difference_nonnegative (q m : ℕ) (u : ℝ) (hu : 0 < u) :
    0 ≤ (fwdDiff 1)^[q] (fun y : ℝ => y ^ m) u := by
  by_cases hmq : m < q
  · have h := congr_fun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hmq) u
    simpa only [Pi.zero_apply, h] using (le_refl (0 : ℝ))
  · have hqm : q ≤ m := Nat.le_of_not_gt hmq
    have hn (y : ℝ) : y ^ m = y ^ (m : ℝ) := (Real.rpow_natCast y m).symm
    simp_rw [hn]
    obtain ⟨y, hy, he⟩ := exists_fwd_diff_iter_eq_iterated_deriv
      (fun y : ℝ => y ^ (m : ℝ)) q (x := u) (by norm_num : (0 : ℝ) < 1)
      (fun n _ y hy => power_smooth m n y (lt_of_lt_of_le hu hy.1))
    rw [he, one_pow, one_mul, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const,
      descPochhammer_eval_eq_prod_range]
    apply mul_nonneg _ (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hu hy.1)) _)
    apply prod_nonneg
    intro a ha
    have : a ≤ m := le_trans (Nat.le_of_lt (mem_range.mp ha)) hqm
    exact sub_nonneg.mpr (by exact_mod_cast this)

private lemma first_power_difference_negative (p : ℝ) (hp : 1 < p) (hp' : p < 2) :
    2 * (3 : ℝ) ^ p + 6 ^ p - 2 ^ p - 2 * 5 ^ p < 0 := by
  have h₂ := power_difference_negative 2 (by omega) p 2 (by norm_num) (by simpa using hp) hp'
  have h₃ := power_difference_negative 2 (by omega) p 3 (by norm_num) (by simpa using hp) hp'
  norm_num [Function.iterate_succ_apply', fwdDiff] at h₂ h₃
  linarith

end D5.S3.Quantum.Schatten.WordTraceExponentBoundary
