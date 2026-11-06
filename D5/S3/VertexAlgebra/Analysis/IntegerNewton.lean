/- GID: D5/S3/VertexAlgebra/Analysis/IntegerNewton
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/IntegerNewton
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer Newton reconstruction and finite diagonal contact coefficients. -/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Binomial
import Mathlib.Analysis.Complex.Norm
import D5.S3.VertexAlgebra.FieldNormalProductLocality
import Mathlib.Tactic

/-!
SOURCE-ONLY / UNCOMPILED.

The forward difference and its finite shift expansion are Mathlib suppliers
(Apache 2.0; the authors are recorded in Algebra/Group/ForwardDiff).
Ring.choose is Mathlib's binomial-ring coefficient, including negative inputs.
The extra argument here extends finite Newton reconstruction to all integers.
The diagonal recurrence is the one used by the Banach-valued contact proof;
it is not a statement about operator closures.

proof_shape: int_newton_of_fwdDiff_iter_eq_zero: content; delta_newton: content
admission_basis: escape-witness
escape_witness: Pascal's integer recursion and two-sided induction reconstruct
every diagonal; the contact consumer uses these values and their norm bound.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Function

namespace D5.S3.VertexAlgebra.Analysis.IntegerNewton
open D5.S3.VertexAlgebra.FieldNormalProductLocality (delta)

section Additive
variable {V : Type*} [AddCommGroup V]

/-- A sequence killed by its N-th difference is its finite Newton polynomial,
also at negative integers. For N = 0 both sides are zero. -/
theorem int_newton_of_fwdDiff_iter_eq_zero (q : ℤ → V) (N : ℕ)
    (hq : (fwdDiff (1 : ℤ))^[N] q = 0) (m : ℤ) :
    q m = ∑ j ∈ range N,
      (Ring.choose m j : ℤ) • ((fwdDiff (1 : ℤ))^[j] q) 0 := by
  induction N generalizing q m with
  | zero =>
    have hz : q = 0 := by simpa using hq
    simp [hz]
  | succ N ih =>
    let d : ℤ → V := fwdDiff (1 : ℤ) q
    have hd : (fwdDiff (1 : ℤ))^[N] d = 0 := by
      simpa only [d, Function.iterate_succ_apply] using hq
    let p : ℤ → V := fun x => q 0 + ∑ j ∈ range N,
      (Ring.choose x (j+1) : ℤ) • ((fwdDiff (1 : ℤ))^[j] d) 0
    have hp0 : p 0 = q 0 := by simp [p]
    have hpstep (x : ℤ) : p (x+1) = p x + d x := by
      rw [ih d hd x]
      dsimp only [p]
      simp_rw [Ring.choose_succ_succ, add_smul]
      rw [sum_add_distrib]
      abel
    have hqstep (x : ℤ) : q (x+1) = q x + d x := by
      dsimp [d, fwdDiff]
      abel
    have hqp (x : ℤ) : q x = p x := by
      refine Int.induction_on x hp0.symm ?_ ?_
      · intro i hi
        rw [hqstep, hpstep, hi]
      · intro i hi
        have hi' : q ((-(i : ℤ)-1)+1) = p ((-(i : ℤ)-1)+1) := by
          simpa using hi
        rw [hqstep, hpstep] at hi'
        exact add_right_cancel hi'
    calc
      q m = p m := hqp m
      _ = (∑ j ∈ range N,
          (Ring.choose m (j+1) : ℤ) • ((fwdDiff (1 : ℤ))^[j] d) 0) + q 0 := by
        dsimp only [p]
        abel
      _ = ∑ j ∈ range (N+1),
          (Ring.choose m j : ℤ) • ((fwdDiff (1 : ℤ))^[j] q) 0 := by
        rw [sum_range_succ']
        simp only [Ring.choose_zero_right, one_smul, Function.iterate_zero, id_eq]
        congr 1

private theorem diagonal_difference (C : ℤ → ℤ → V) (t m : ℤ) (j : ℕ) :
    ((fwdDiff (1 : ℤ))^[j] (fun x => C x (t-x))) m =
      (delta^[j] C) m (t-m-j) := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change
      ((fwdDiff (1 : ℤ))^[j] (fun x => C x (t-x))) (m+1) -
          ((fwdDiff (1 : ℤ))^[j] (fun x => C x (t-x))) m =
        (delta^[j] C) (m+1) (t-m-(j+1 : ℕ)) -
          (delta^[j] C) m (t-m-(j+1 : ℕ)+1)
    rw [ih, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    congr 1 <;> congr 1 <;> ring

/-- Finite contact coefficients, expressed using the original C values. -/
def contactCoefficient (C : ℤ → ℤ → V) (j : ℕ) (t : ℤ) : V :=
  ∑ i ∈ range (j+1),
    ((-1 : ℤ)^(j-i) * (j.choose i : ℤ)) • C i (t-i)

private theorem contactCoefficient_eq_difference (C : ℤ → ℤ → V)
    (j : ℕ) (t : ℤ) :
    contactCoefficient C j t =
      ((fwdDiff (1 : ℤ))^[j] (fun x => C x (t-x))) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp [contactCoefficient]

/-- All-integer diagonal reconstruction; no positivity condition on either mode. -/
theorem delta_newton (C : ℤ → ℤ → V) (N : ℕ) (hC : delta^[N] C = 0)
    (m n : ℤ) :
    C m n = ∑ j ∈ range N,
      (Ring.choose m j : ℤ) • contactCoefficient C j (m+n) := by
  have hq : (fwdDiff (1 : ℤ))^[N] (fun x => C x (m+n-x)) = 0 := by
    funext x
    rw [diagonal_difference, hC]
    rfl
  have h := int_newton_of_fwdDiff_iter_eq_zero (fun x => C x (m+n-x)) N hq m
  simpa only [add_sub_cancel_left, ← contactCoefficient_eq_difference] using h

end Additive

section ChooseBound

/-- The descending-factorial recursion, shared by the norm and Fourier proofs. -/
theorem choose_succ_mul {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (x : 𝕜) (j : ℕ) :
    (j+1 : 𝕜) * Ring.choose x (j+1) = (x-j) * Ring.choose x j := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose x (j+1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
    Ring.descPochhammer_eq_factorial_smul_choose] at h
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
    pow_one, pow_zero, nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, mul_one, one_mul, Int.cast_natCast] at h
  have hj : (j.factorial : 𝕜) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  apply mul_left_cancel₀ hj
  calc
    _ = ((j+1 : 𝕜) * j.factorial) * Ring.choose x (j+1) := by ring
    _ = (j.factorial * Ring.choose x j) * (x-j) := h.symm
    _ = _ := by ring

/-- The factorial in the binomial cancels the growth of the descending factors.
The estimate is valid for negative modes and for j = 0. -/
theorem norm_int_choose_le_pow (m : ℤ) (j : ℕ) :
    ‖((Ring.choose m j : ℤ) : ℂ)‖ ≤ (1+|(m : ℝ)|)^j := by
  have hcast (k : ℕ) : ((Ring.choose m k : ℤ) : ℝ) = Ring.choose (m : ℝ) k :=
    Ring.map_choose (Int.castRingHom ℝ) m k
  have hb (k : ℕ) : |Ring.choose (m : ℝ) k| ≤ (1+|(m : ℝ)|)^k := by
    induction k with
    | zero => simp [Ring.choose_zero_right]
    | succ k ih =>
      have hstep := congrArg abs (choose_succ_mul (m : ℝ) k)
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < k+1)] at hstep
      have hfactor : |(m : ℝ)-k| ≤ (1+|(m : ℝ)|) * (k+1) := by
        have htri := abs_sub_le (m : ℝ) (k : ℝ) 0
        simp only [sub_zero, zero_sub, abs_neg] at htri
        rw [abs_of_nonneg (Nat.cast_nonneg k)] at htri
        nlinarith [abs_nonneg (m : ℝ)]
      have hmul := mul_le_mul hfactor ih (abs_nonneg _) (by positivity)
      have hscaled : (k+1 : ℝ) * |Ring.choose (m : ℝ) (k+1)| ≤
          (k+1 : ℝ) * (1+|(m : ℝ)|)^(k+1) := by
        calc
          _ = |(m : ℝ)-k| * |Ring.choose (m : ℝ) k| := hstep
          _ ≤ ((1+|(m : ℝ)|) * (k+1)) * (1+|(m : ℝ)|)^k := hmul
          _ = _ := by rw [pow_succ]; ring
      exact le_of_mul_le_mul_left hscaled (by positivity)
  simpa only [Complex.norm_intCast, ← hcast j] using hb j

end ChooseBound
end D5.S3.VertexAlgebra.Analysis.IntegerNewton
