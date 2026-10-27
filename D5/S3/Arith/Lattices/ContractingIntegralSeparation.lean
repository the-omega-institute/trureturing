/- GID: D5/S3/Arith/Lattices/ContractingIntegralSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/ContractingIntegralSeparation
   mirror-E: none(waiver:algebraic-law-separation)
   anchors: []
   utility: none
   digest: Contracting rational polynomials of integer matrices separate from every power. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Rat
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-! Integral lattice orbits separate contracting polynomial laws from native powers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Lattices.ContractingIntegralSeparation

open Matrix Filter Topology Polynomial
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem equal_power_orbit (F B : Matrix n n ℚ) (hcomm : Commute F B)
    (v : n → ℚ) (hv : F *ᵥ v = B *ᵥ v) (j : ℕ) :
    F ^ j *ᵥ v = B ^ j *ᵥ v := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        F ^ (j + 1) *ᵥ v = F *ᵥ (F ^ j *ᵥ v) := by
          rw [pow_succ', mulVec_mulVec]
        _ = F *ᵥ (B ^ j *ᵥ v) := by rw [ih]
        _ = B ^ j *ᵥ (F *ᵥ v) := by
          simp only [mulVec_mulVec, (hcomm.pow_right j).eq]
        _ = B ^ (j + 1) *ᵥ v := by rw [hv, pow_succ, mulVec_mulVec]

/-- The lattice orbit of an integral vector cannot converge to zero under an
injective contraction while agreeing with all powers of an integral matrix. -/
private theorem integral_orbit_zero (B : Matrix n n ℤ) (F : Matrix n n ℚ)
    (hF : IsUnit F) (hc : ‖F.map (algebraMap ℚ ℝ)‖ < 1)
    (w : n → ℤ)
    (horbit : ∀ j : ℕ, F ^ j *ᵥ (fun i => (w i : ℚ)) =
      (B.map (Int.castRingHom ℚ)) ^ j *ᵥ (fun i => (w i : ℚ))) : w = 0 := by
  cases isEmpty_or_nonempty n with
  | inl empty =>
      letI := empty
      exact Subsingleton.elim _ _
  | inr inhabited =>
      letI := inhabited
      let R : Matrix n n ℝ := F.map (algebraMap ℚ ℝ)
      let v : EuclideanSpace ℝ n := WithLp.toLp 2 (fun i => (w i : ℝ))
      have hlim : Tendsto (fun j : ℕ => ‖R‖ ^ j * ‖v‖) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg R) hc).mul_const ‖v‖
      obtain ⟨j, hj⟩ := ((hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists)
      have real_orbit : R ^ j *ᵥ (fun i => (w i : ℝ)) =
          fun i => ((B ^ j *ᵥ w) i : ℝ) := by
        have qeq : F ^ j *ᵥ (fun i => (w i : ℚ)) =
            fun i => ((B ^ j *ᵥ w) i : ℚ) := by
          rw [horbit j, ← Matrix.map_pow]
          ext i
          exact (RingHom.map_mulVec (Int.castRingHom ℚ) (B ^ j) w i).symm
        ext i
        have hi := congrArg (fun z : n → ℚ => (algebraMap ℚ ℝ) (z i)) qeq
        rw [RingHom.map_mulVec] at hi
        simpa [R, Matrix.map_pow, Function.comp_def] using hi
      have integral_zero : B ^ j *ᵥ w = 0 := by
        ext i
        have hbound := (R ^ j).l2_opNorm_mulVec v
        have hsmall : ‖WithLp.toLp 2 (fun i => ((B ^ j *ᵥ w) i : ℝ))‖ < 1 := by
          calc
            _ = ‖WithLp.toLp 2 (R ^ j *ᵥ (fun i => (w i : ℝ)))‖ := by rw [real_orbit]
            _ ≤ ‖R ^ j‖ * ‖v‖ := hbound
            _ ≤ ‖R‖ ^ j * ‖v‖ := mul_le_mul_of_nonneg_right (norm_pow_le R j) (norm_nonneg v)
            _ < 1 := hj
        have hi : |((B ^ j *ᵥ w) i : ℝ)| < 1 :=
          (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => ((B ^ j *ᵥ w) i : ℝ))) i).trans_lt hsmall
        have hi' : |(B ^ j *ᵥ w) i| < (1 : ℤ) := by exact_mod_cast hi
        exact Int.abs_lt_one_iff.mp hi'
      have rational_zero : F ^ j *ᵥ (fun i => (w i : ℚ)) = 0 := by
        rw [horbit j, ← Matrix.map_pow]
        ext i
        simpa [integral_zero, Function.comp_def] using
          (RingHom.map_mulVec (Int.castRingHom ℚ) (B ^ j) w i).symm
      have hw : (fun i => (w i : ℚ)) = (0 : n → ℚ) :=
        Matrix.mulVec_injective_of_isUnit (hF.pow j) (rational_zero.trans (by simp))
      ext i
      have hi := congrFun hw i
      have hi' : (w i : ℚ) = 0 := by simpa only [Pi.zero_apply] using hi
      exact Int.cast_eq_zero.mp hi'

/-- Strict contraction is measured in the real Euclidean operator norm. Neither
symmetry nor invertibility of the integral matrix is needed. -/
theorem polynomial_sub_pow_isUnit (A : Matrix n n ℤ) (f : ℚ[X])
    (hF : IsUnit (Polynomial.aeval (A.map (Int.castRingHom ℚ)) f))
    (hc : ‖(Polynomial.aeval (A.map (Int.castRingHom ℚ)) f).map
      (algebraMap ℚ ℝ)‖ < 1) (k : ℕ) :
    IsUnit (Polynomial.aeval (A.map (Int.castRingHom ℚ)) f -
      (A.map (Int.castRingHom ℚ)) ^ k) := by
  let Q := A.map (Int.castRingHom ℚ)
  let F : Matrix n n ℚ := Polynomial.aeval Q f
  have commute : Commute F Q := by
    simpa [F] using (Commute.all f (Polynomial.X : ℚ[X])).map (Polynomial.aeval Q)
  have kernel (z : n → ℚ) (hz : (F - Q ^ k) *ᵥ z = 0) : z = 0 := by
    have hz' : F *ᵥ z = Q ^ k *ᵥ z := by
      simpa only [Matrix.sub_mulVec, sub_eq_zero] using hz
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors ℤ) z
    choose w hw using hb
    have hw' : (fun i => (w i : ℚ)) = (b : ℤ) • z := by
      ext i
      exact hw i
    have initial : F *ᵥ (fun i => (w i : ℚ)) =
        Q ^ k *ᵥ (fun i => (w i : ℚ)) := by
      rw [hw', Matrix.mulVec_smul, Matrix.mulVec_smul, hz']
    have wz : w = 0 := integral_orbit_zero (A ^ k) F hF hc w (fun j => by
      have hm : (A ^ k).map (Int.castRingHom ℚ) = Q ^ k := by
        exact Matrix.map_pow A (Int.castRingHom ℚ) k
      rw [hm]
      exact equal_power_orbit F (Q ^ k) (commute.pow_right k) _ initial j)
    have bz : (b : ℤ) • z = 0 := by
      rw [← hw', wz]
      ext i
      simp
    have bq : ((b : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast nonZeroDivisors.coe_ne_zero b
    ext i
    have hi := congrFun bz i
    change ((b : ℤ) : ℚ) * z i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left bq
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply sub_eq_zero.mp
  apply kernel
  simpa only [Matrix.mulVec_sub, sub_eq_zero] using hxy

#print axioms polynomial_sub_pow_isUnit

end D5.S3.Arith.Lattices.ContractingIntegralSeparation
