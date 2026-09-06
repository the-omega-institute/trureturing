/- GID: D5/S3/Zeros/PochhammerDeformation/QuadraticInterval
   generality: G
   mirror-B: D5/B/S3/Zeros/PochhammerDeformation/QuadraticInterval
   mirror-E: none(waiver:general-theorems-no-computational-artifact)
   anchors: []
   utility: none
   digest: Quadratic Pochhammer root intervals and the sharp small-parameter counterexample. -/

import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.PochhammerDeformation.QuadraticInterval

open Polynomial

private def fallingSequence : Polynomial.Sequence ℝ where
  elems' := descPochhammer ℝ
  degree_eq' k := by
    rw [degree_eq_natDegree (monic_descPochhammer ℝ k).ne_zero,
      descPochhammer_natDegree]

private def fallingBasis : Module.Basis ℕ ℝ ℝ[X] :=
  fallingSequence.basis (fun k => by
    change IsUnit (descPochhammer ℝ k).leadingCoeff
    rw [(monic_descPochhammer ℝ k).leadingCoeff]
    exact isUnit_one)

/-- Definition 1.4, constructed on the falling Pochhammer basis. -/
def lOp (a : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  fallingBasis.constr ℝ (fun k => (ascPochhammer ℝ k).eval a • X ^ k)

/-- Every complex root is real and its real part is in the prescribed interval. -/
def RealRootsInUnitInterval (p : ℝ[X]) : Prop :=
  ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots,
    z.im = 0 ∧ z.re ∈ Set.Icc (-1) 0

/-- Example 6.4 at degree two; the condition quantifies over complex roots. -/
def m2 (a : ℝ) : Set ℝ :=
  {t | RealRootsInUnitInterval (lOp a ((X + C t) ^ 2))}

/-- The leftward extent of the real-root parameter set, independently of its closed form. -/
def c2 (a : ℝ) : ℝ := -sInf (m2 a)

private theorem lOp_on_basis (a : ℝ) (k : ℕ) :
    lOp a (descPochhammer ℝ k) = (ascPochhammer ℝ k).eval a • X ^ k := by
  have h := fallingBasis.constr_basis ℝ
    (fun j => (ascPochhammer ℝ j).eval a • (X : ℝ[X]) ^ j) k
  simpa only [lOp, fallingBasis, Polynomial.Sequence.basis_eq_self,
    fallingSequence] using h

theorem lOp_definition (a : ℝ) (ha : 0 < a) (k : ℕ) :
    lOp a (C ((ascPochhammer ℝ k).eval a)⁻¹ * descPochhammer ℝ k) = X ^ k := by
  rw [← smul_eq_C_mul, map_smul, lOp_on_basis, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (ascPochhammer_pos k a ha)), one_smul]

private theorem lOp_falling_of_pos (a : ℝ) (ha : 0 < a) (k : ℕ) :
    lOp a (descPochhammer ℝ k) = (ascPochhammer ℝ k).eval a • X ^ k := by
  have h := congrArg (fun p : ℝ[X] => (ascPochhammer ℝ k).eval a • p)
    (lOp_definition a ha k)
  simpa only [← smul_eq_C_mul, ← map_smul, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (ascPochhammer_pos k a ha)), one_smul] using h

theorem lOp_quadratic (a t : ℝ) (ha : 0 < a) :
    lOp a ((X + C t) ^ 2) =
      C (a * (a + 1)) * X ^ 2 + C (a * (1 + 2 * t)) * X + C (t ^ 2) := by
  have hExpand : (X + C t) ^ 2 = descPochhammer ℝ 2 +
      (1 + 2 * t) • descPochhammer ℝ 1 + t ^ 2 • descPochhammer ℝ 0 := by
    simp only [descPochhammer_succ_right, descPochhammer_zero,
      Nat.cast_one, smul_eq_C_mul, map_add, map_mul, map_pow, map_one, map_ofNat]
    ring
  rw [hExpand, map_add, map_add, map_smul, map_smul,
    lOp_falling_of_pos a ha 2, lOp_falling_of_pos a ha 1, lOp_falling_of_pos a ha 0]
  simp only [ascPochhammer_succ_right, ascPochhammer_zero,
    eval_mul, eval_add, eval_X, eval_one, eval_natCast, pow_zero, pow_one,
    smul_eq_C_mul, mul_one, map_mul, map_add, map_one, map_ofNat]
  norm_num only [Nat.cast_zero, Nat.cast_one, map_zero, map_one]
  ring

theorem quadratic_endpoint_squares (a t : ℝ) (ha : 0 < a) :
    (lOp a ((X + C t) ^ 2)).eval 0 = t ^ 2 ∧
    0 ≤ (lOp a ((X + C t) ^ 2)).eval 0 ∧
    (lOp a ((X + C t) ^ 2)).eval (-1) = (a - t) ^ 2 ∧
    0 ≤ (lOp a ((X + C t) ^ 2)).eval (-1) := by
  rw [lOp_quadratic a t ha]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  constructor
  · ring
  constructor
  · nlinarith [sq_nonneg t]
  constructor
  · ring
  · nlinarith [sq_nonneg (a - t)]

private theorem quadratic_discriminant (a t : ℝ) :
    discrim (a * (a + 1)) (a * (1 + 2 * t)) (t ^ 2) =
      a * (a + 4 * a * t - 4 * t ^ 2) := by
  unfold discrim
  ring

private theorem discriminant_interval (a t : ℝ) (ha : 0 < a) :
    0 ≤ discrim (a * (a + 1)) (a * (1 + 2 * t)) (t ^ 2) ↔
      t ∈ Set.Icc ((a - Real.sqrt (a ^ 2 + a)) / 2)
        ((a + Real.sqrt (a ^ 2 + a)) / 2) := by
  rw [quadratic_discriminant, mul_nonneg_iff_of_pos_left ha]
  have hs := Real.sq_sqrt (show 0 ≤ a ^ 2 + a by positivity)
  have hs0 := Real.sqrt_nonneg (a ^ 2 + a)
  constructor
  · intro hd
    constructor <;> nlinarith [sq_nonneg (2 * t - a - Real.sqrt (a ^ 2 + a)),
      sq_nonneg (2 * t - a + Real.sqrt (a ^ 2 + a))]
  · rintro ⟨hl, hu⟩
    nlinarith [mul_nonneg (show 0 ≤ 2 * t - a + Real.sqrt (a ^ 2 + a) by linarith)
      (show 0 ≤ Real.sqrt (a ^ 2 + a) - (2 * t - a) by linarith)]

private theorem discriminant_implies_vertex (a t : ℝ) (ha : 0 < a)
    (hd : 0 ≤ discrim (a * (a + 1)) (a * (1 + 2 * t)) (t ^ 2)) :
    0 < a * (1 + 2 * t) ∧ a * (1 + 2 * t) < 2 * (a * (a + 1)) := by
  have hs := Real.sq_sqrt (show 0 ≤ a ^ 2 + a by positivity)
  have hs0 := Real.sqrt_nonneg (a ^ 2 + a)
  have hslt : Real.sqrt (a ^ 2 + a) < a + 1 := by nlinarith
  obtain ⟨hl, hu⟩ := (discriminant_interval a t ha).mp hd
  constructor
  · exact mul_pos ha (by linarith)
  · nlinarith [mul_pos ha (show 0 < 2 * a + 1 - 2 * t by linarith)]

private theorem quadratic_complex_ne_zero (A B C' : ℝ) (hA : A ≠ 0) :
    (Polynomial.C (A : ℂ) * X ^ 2 + Polynomial.C (B : ℂ) * X +
      Polynomial.C (C' : ℂ) : ℂ[X]) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℂ[X] => p.coeff 2) h
  simp at hc
  exact hA hc

private theorem quadratic_complex_root_real (A B C' : ℝ) (hA : A ≠ 0)
    (hd : 0 ≤ discrim A B C') (z : ℂ)
    (hz : (A : ℂ) * (z * z) + (B : ℂ) * z + (C' : ℂ) = 0) : z.im = 0 := by
  have hs : discrim (A : ℂ) (B : ℂ) (C' : ℂ) =
      (Real.sqrt (discrim A B C') : ℂ) * Real.sqrt (discrim A B C') := by
    have hr := (Real.sq_sqrt hd).symm
    dsimp [discrim] at hr ⊢
    exact_mod_cast (by simpa only [sq] using hr)
  have hr := (quadratic_eq_zero_iff (show (A : ℂ) ≠ 0 by exact_mod_cast hA) hs z).mp hz
  have hr' : z = (((-B + Real.sqrt (discrim A B C')) / (2 * A) : ℝ) : ℂ) ∨
      z = (((-B - Real.sqrt (discrim A B C')) / (2 * A) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat] using hr
  rcases hr' with hr' | hr' <;> rw [hr'] <;> rfl

private theorem real_quadratic_root_in_interval (A B C' x : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hB' : B < 2 * A)
    (h0 : 0 ≤ C') (h1 : 0 ≤ A - B + C')
    (hx : A * (x * x) + B * x + C' = 0) : x ∈ Set.Icc (-1) 0 := by
  constructor
  · by_contra h
    have hx1 : x + 1 < 0 := by linarith
    have hp := mul_pos_of_neg_of_neg (show B - 2 * A < 0 by linarith) hx1
    have hs := mul_nonneg hA.le (sq_nonneg (x + 1))
    nlinarith
  · by_contra h
    have hx0 : 0 < x := by linarith
    have hp := mul_pos hB hx0
    have hs := mul_nonneg hA.le (sq_nonneg x)
    nlinarith

private theorem m2_iff_discriminant (a t : ℝ) (ha : 0 < a) :
    t ∈ m2 a ↔ 0 ≤ discrim (a * (a + 1)) (a * (1 + 2 * t)) (t ^ 2) := by
  have hA : 0 < a * (a + 1) := mul_pos ha (by linarith)
  have hp := quadratic_complex_ne_zero (a * (a + 1)) (a * (1 + 2 * t)) (t ^ 2) hA.ne'
  change RealRootsInUnitInterval (lOp a ((X + C t) ^ 2)) ↔ _
  rw [lOp_quadratic a t ha]
  simp only [RealRootsInUnitInterval, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  constructor
  · intro hroots
    obtain ⟨z, hz⟩ := Complex.exists_root (f := C (↑(a * (a + 1)) : ℂ) * X ^ 2 +
      C (↑(a * (1 + 2 * t)) : ℂ) * X + C (↑(t ^ 2) : ℂ)) (by
        rw [degree_quadratic (by exact_mod_cast hA.ne')]
        norm_num)
    have him := (hroots z ((mem_roots hp).mpr hz)).1
    have hzreal : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using him.symm)
    have heq : a * (a + 1) * (z.re * z.re) + a * (1 + 2 * t) * z.re + t ^ 2 = 0 := by
      apply Complex.ofReal_injective
      simpa only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X,
        Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_zero, hzreal, sq] using hz
    rw [discrim_eq_sq_of_quadratic_eq_zero heq]
    exact sq_nonneg _
  · intro hd z hz
    have heq : (↑(a * (a + 1)) : ℂ) * (z * z) +
        ↑(a * (1 + 2 * t)) * z + ↑(t ^ 2) = 0 := by
      simpa only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, sq]
        using (mem_roots hp).mp hz
    have him := quadratic_complex_root_real _ _ _ hA.ne' hd z heq
    refine ⟨him, ?_⟩
    have hzreal : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using him.symm)
    have heqR : a * (a + 1) * (z.re * z.re) + a * (1 + 2 * t) * z.re + t ^ 2 = 0 := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_zero, hzreal] using heq
    obtain ⟨hB, hB'⟩ := discriminant_implies_vertex a t ha hd
    have endpoints := quadratic_endpoint_squares a t ha
    have hleft : 0 ≤ a * (a + 1) - a * (1 + 2 * t) + t ^ 2 := by
      calc
        0 ≤ (a - t) ^ 2 := sq_nonneg _
        _ = (lOp a ((X + C t) ^ 2)).eval (-1) := endpoints.2.2.1.symm
        _ = a * (a + 1) - a * (1 + 2 * t) + t ^ 2 := by
          rw [lOp_quadratic a t ha]
          simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
          ring
    exact real_quadratic_root_in_interval _ _ _ _ hA hB hB' (sq_nonneg t) hleft heqR

theorem quadratic_interval_closed_form (a : ℝ) (ha : 0 < a) :
    m2 a = Set.Icc ((a - Real.sqrt (a ^ 2 + a)) / 2)
      ((a + Real.sqrt (a ^ 2 + a)) / 2) ∧
    c2 a = (Real.sqrt (a ^ 2 + a) - a) / 2 ∧
    m2 a = Set.Icc (-c2 a) (a + c2 a) := by
  have hset : m2 a = Set.Icc ((a - Real.sqrt (a ^ 2 + a)) / 2)
      ((a + Real.sqrt (a ^ 2 + a)) / 2) := by
    ext t
    exact (m2_iff_discriminant a t ha).trans (discriminant_interval a t ha)
  have hc : c2 a = (Real.sqrt (a ^ 2 + a) - a) / 2 := by
    rw [c2, hset, csInf_Icc (by linarith [Real.sqrt_nonneg (a ^ 2 + a)])]
    ring
  refine ⟨hset, hc, ?_⟩
  rw [hset, hc]
  congr 1 <;> ring

private theorem sqrt_threshold (a : ℝ) (ha : 0 < a) :
    Real.sqrt (a ^ 2 + a) < 5 * a ↔ 1 / 24 < a := by
  have hs := Real.sq_sqrt (show 0 ≤ a ^ 2 + a by positivity)
  have hs0 := Real.sqrt_nonneg (a ^ 2 + a)
  constructor
  · intro h
    have hprod := mul_pos (show 0 < 5 * a - Real.sqrt (a ^ 2 + a) by linarith)
      (show 0 < 5 * a + Real.sqrt (a ^ 2 + a) by linarith)
    have hmul : 0 < a * (24 * a - 1) := by nlinarith
    have := (mul_pos_iff_of_pos_left ha).mp hmul
    linarith
  · intro h
    have hmul := mul_pos ha (show 0 < 24 * a - 1 by linarith)
    nlinarith

theorem quadratic_conjecture_refutation (a : ℝ) (ha : 0 < a) :
    (c2 a < 2 * a ↔ 1 / 24 < a) ∧
    c2 (1 / 24) = 1 / 12 ∧ c2 (1 / 24) = 2 * (1 / 24) ∧
    (a ≤ 1 / 24 → 2 * a ≤ c2 a ∧ ¬(0 < c2 a ∧ c2 a < 2 * a)) := by
  have hiff : c2 a < 2 * a ↔ 1 / 24 < a := by
    rw [(quadratic_interval_closed_form a ha).2.1]
    exact (show (Real.sqrt (a ^ 2 + a) - a) / 2 < 2 * a ↔
      Real.sqrt (a ^ 2 + a) < 5 * a by constructor <;> intro h <;> linarith).trans
        (sqrt_threshold a ha)
  have hboundary : c2 (1 / 24) = 1 / 12 := by
    rw [(quadratic_interval_closed_form (1 / 24) (by norm_num)).2.1]
    have hs : Real.sqrt ((1 / 24 : ℝ) ^ 2 + 1 / 24) = 5 / 24 := by
      apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr
      norm_num
    rw [hs]
    norm_num
  refine ⟨hiff, hboundary, by rw [hboundary]; norm_num, ?_⟩
  intro hsmall
  have hn : ¬c2 a < 2 * a := fun h => (not_lt_of_ge hsmall) (hiff.mp h)
  exact ⟨le_of_not_gt hn, fun h => hn h.2⟩

#print axioms lOp_definition
#print axioms lOp_quadratic
#print axioms quadratic_endpoint_squares
#print axioms quadratic_interval_closed_form
#print axioms quadratic_conjecture_refutation

end D5.S3.Zeros.PochhammerDeformation.QuadraticInterval
