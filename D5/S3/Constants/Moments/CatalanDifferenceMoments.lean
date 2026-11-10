/- GID: D5/S3/Constants/Moments/CatalanDifferenceMoments
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/CatalanDifferenceMoments
   mirror-E: none(waiver:universal-catalan-difference-envelope)
   anchors: [mathlib/module/Mathlib.Algebra.Group.ForwardDiff]
   utility: none
   digest: Unit Catalan moment differences have a uniform two-sided ratio envelope. -/

import D5.S3.Constants.Moments.CatalanSquareHankelGrowth
import Mathlib.Algebra.Group.ForwardDiff

/-! # Uniform ratio bounds for unit Catalan moment differences -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Constants.Moments.CatalanDifferenceMoments

open CatalanSquareHankelGrowth

local notation "M" => catalanMoment
local notation "Δ" => fwdDiff (1 : Nat)

private lemma difference_shift (L k : Nat) :
    Δ^[k] M (L + 1) = Δ^[k] M L + Δ^[k + 1] M L := by
  rw [Function.iterate_succ_apply', fwdDiff]
  ring

private lemma initial_ratio (L : Nat) :
    ((L : Real) + 2) * Δ^[1] M L = 3 * L * Δ^[0] M L := by
  have h0 : ((L : Real) + 1) * (catalan L : Real) = (Nat.centralBinom L : Real) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom L
  have h1 : ((L : Real) + 2) * (catalan (L + 1) : Real) =
      (Nat.centralBinom (L + 1) : Real) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom (L + 1)
  have hc : ((L : Real) + 1) * (Nat.centralBinom (L + 1) : Real) =
      2 * (2 * L + 1) * (Nat.centralBinom L : Real) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ L
  have hpos : (0 : Real) < (L : Real) + 1 := by positivity
  have hratio : ((L : Real) + 2) * (catalan (L + 1) : Real) =
      (4 * L + 2) * (catalan L : Real) := by
    nlinarith [h0, h1, hc]
  simpa only [Function.iterate_one, Function.iterate_zero, id_eq, fwdDiff,
    beta_moment_formula] using (show
      ((L : Real) + 2) * ((catalan (L + 1) : Real) - (catalan L : Real)) =
        3 * L * (catalan L : Real) by nlinarith [hratio])

private lemma difference_recurrence (s L : Nat) :
    ((L : Real) + s + 3) * Δ^[s + 2] M L =
      (3 * L + 2 * s + 2) * Δ^[s + 1] M L +
        3 * (s + 1) * Δ^[s] M L := by
  induction s generalizing L with
  | zero =>
      have h := initial_ratio L
      have ht := initial_ratio (L + 1)
      rw [difference_shift L 1, difference_shift L 0] at ht
      push_cast at ht
      norm_num only [Nat.cast_zero, zero_add, add_zero, mul_zero, zero_mul,
        Nat.reduceAdd] at *
      nlinarith [h, ht]
  | succ s ih =>
      have h := ih L
      have ht := ih (L + 1)
      rw [difference_shift L (s + 2), difference_shift L (s + 1),
        difference_shift L s] at ht
      push_cast at ht ⊢
      convert (show ((L : Real) + s + 4) * Δ^[s + 2 + 1] M L =
          (3 * L + 2 * s + 4) * Δ^[s + 2] M L +
            3 * (s + 2) * Δ^[s + 1] M L by nlinarith [h, ht]) using 1 <;>
        congr 1 <;> ring

/-- All unit differences of the original Catalan moment sequence satisfy a positive
    lower ratio envelope and a strict upper ratio of three. -/
theorem catalan_difference_ratio_envelope (L k : Nat) (hL : 1 ≤ L) :
    0 < Δ^[k] M L ∧
      3 * ((L : Real) + k) * Δ^[k] M L ≤
        ((L : Real) + k + 2) * Δ^[k + 1] M L ∧
      Δ^[k + 1] M L < 3 * Δ^[k] M L := by
  have hLR : (1 : Real) ≤ L := by exact_mod_cast hL
  induction k with
  | zero =>
      have hp : (0 : Real) < Δ^[0] M L := by
        simp only [Function.iterate_zero, id_eq, beta_moment_formula]
        have hc : (0 : Real) < (Nat.centralBinom L : Real) := by
          exact_mod_cast Nat.centralBinom_pos L
        have he : ((L : Real) + 1) * (catalan L : Real) =
            (Nat.centralBinom L : Real) := by
          exact_mod_cast succ_mul_catalan_eq_centralBinom L
        nlinarith [he]
      have hb := initial_ratio L
      norm_num only [Nat.cast_zero, add_zero, Nat.zero_add] at *
      refine ⟨hp, le_of_eq hb.symm, ?_⟩
      nlinarith [hb]
  | succ k ih =>
      have hk : (0 : Real) ≤ k := by positivity
      have hr := difference_recurrence k L
      obtain ⟨hp, hlo, hup⟩ := ih
      have hp' : 0 < Δ^[k + 1] M L := by nlinarith [hlo]
      have hlo' : 3 * ((L : Real) + k + 1) * Δ^[k + 1] M L ≤
          ((L : Real) + k + 3) * Δ^[k + 2] M L := by
        nlinarith [mul_nonneg (by positivity : (0 : Real) ≤ k + 1)
          (le_of_lt (sub_pos.mpr hup))]
      have hgap : ((L : Real) + k + 3) *
          (3 * Δ^[k + 1] M L - Δ^[k + 2] M L) =
          ((k : Real) + 7) * Δ^[k + 1] M L -
            3 * (k + 1) * Δ^[k] M L := by nlinarith [hr]
      have hbound := mul_le_mul_of_nonneg_left hlo
        (by positivity : (0 : Real) ≤ (k : Real) + 1)
      have hid : (((k : Real) + 7) * ((L : Real) + k) -
          (k + 1) * ((L : Real) + k + 2)) * Δ^[k + 1] M L =
          (6 * L + 4 * k - 2) * Δ^[k + 1] M L := by ring
      have hpositive : (0 : Real) < (6 * L + 4 * k - 2) * Δ^[k + 1] M L :=
        mul_pos (by linarith) hp'
      have hupper : Δ^[k + 2] M L < 3 * Δ^[k + 1] M L := by
        have hm := congrArg (fun x : Real => ((L : Real) + k) * x) hgap
        have hprod : (0 : Real) < (((L : Real) + k) * ((L : Real) + k + 3)) *
            (3 * Δ^[k + 1] M L - Δ^[k + 2] M L) := by
          nlinarith only [hm, hbound, hid, hpositive]
        have hcoeff : (0 : Real) < ((L : Real) + k) * ((L : Real) + k + 3) := by
          positivity
        have := (mul_pos_iff_of_pos_left hcoeff).mp hprod
        linarith
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      rw [show k + 1 + 1 = k + 2 by omega,
        show (L : Real) + ((k : Real) + 1) = (L : Real) + k + 1 by ring,
        show (L : Real) + k + 1 + 2 = (L : Real) + k + 3 by ring]
      exact ⟨hp', hlo', hupper⟩

end D5.S3.Constants.Moments.CatalanDifferenceMoments
