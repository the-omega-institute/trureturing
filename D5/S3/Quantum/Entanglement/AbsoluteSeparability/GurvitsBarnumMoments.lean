/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Corrected finite fourth moments give the product identity for complex quadratic forms. -/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open Finset Complex
open scoped ComplexConjugate
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
noncomputable section
variable {d : ℕ}
private def phase (s : Fin 4) : ℂ := Complex.I ^ s.val
private def rot (i : Fin d) : (Fin d → Fin 4) ≃ (Fin d → Fin 4) :=
  Equiv.piCongrRight (fun j => if j = i then finRotate 4 else Equiv.refl _)
private theorem phase_rot (s : Fin 4) : phase (finRotate 4 s) = I * phase s := by
  fin_cases s <;> norm_num [phase, finRotate_apply, Fin.add_def]
private theorem phase_unit (s : Fin 4) : conj (phase s) * phase s = 1 := by
  simp only [phase, map_pow, ← mul_pow, Complex.conj_I, neg_mul,
    Complex.I_mul_I, neg_neg, one_pow]
private theorem rot_apply (i j : Fin d) (z : Fin d → Fin 4) :
    phase (rot i z j) = (if j = i then I else 1) * phase (z j) := by
  by_cases h : j = i
  · subst j; simpa [rot, finRotate_apply] using phase_rot (z i)
  · simp [rot, h]
private theorem sum_vanish (i : Fin d) (f : (Fin d → Fin 4) → ℂ) (a : ℂ)
    (ha : a ≠ 1) (hf : ∀ z, f (rot i z) = a * f z) : ∑ z, f z = 0 := by
  have hs : ∑ z, f z = a * ∑ z, f z := by
    calc
      _ = ∑ z, f (rot i z) := (Equiv.sum_comp (rot i) f).symm
      _ = _ := by simp_rw [hf]; rw [mul_sum]
  have : (1-a) * ∑ z, f z = 0 := by linear_combination hs
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))
private theorem moment_two (i j : Fin d) :
    (∑ z : Fin d → Fin 4, conj (phase (z i)) * phase (z j)) =
      (4:ℂ)^d * (if i = j then 1 else 0) := by
  by_cases h : i = j
  · subst j; simp [phase_unit]
  · simp only [h, if_false, mul_zero]
    apply sum_vanish i _ (-I) (by intro h; have := congrArg Complex.im h; norm_num at this)
    intro z
    simp [rot_apply, Ne.symm h]
    ring
private theorem moment_four (i j k l : Fin d) :
    (∑ z : Fin d → Fin 4,
      conj (phase (z i)) * phase (z j) * conj (phase (z k)) * phase (z l)) =
      (4:ℂ)^d * ((if i = j ∧ k = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0) -
        (if i = j ∧ j = k ∧ k = l then 1 else 0)) := by
  by_cases hij : i = j
  · subst j
    simp_rw [phase_unit, one_mul]
    rw [moment_two]
    by_cases hkl : k = l <;> by_cases hik : i = k <;> simp_all
  · by_cases hil : i = l
    · subst l
      have hp (z : Fin d → Fin 4) :
          conj (phase (z i)) * phase (z j) * conj (phase (z k)) * phase (z i) =
            conj (phase (z k)) * phase (z j) := by
        calc
          _ = (conj (phase (z i)) * phase (z i)) *
            (conj (phase (z k)) * phase (z j)) := by ring
          _ = _ := by rw [phase_unit, one_mul]
      simp_rw [hp]
      rw [moment_two]
      by_cases hjk : j = k <;> simp_all [eq_comm]
    · have hz : (∑ z : Fin d → Fin 4,
          conj (phase (z i)) * phase (z j) * conj (phase (z k)) * phase (z l)) = 0 := by
        by_cases hik : i = k
        · subst k
          apply sum_vanish i _ (-1) (by norm_num)
          intro z
          simp [rot_apply, Ne.symm hij, Ne.symm hil]
          ring_nf
          simp
        · apply sum_vanish i _ (-I) (by intro h; have := congrArg Complex.im h; norm_num at this)
          intro z
          simp [rot_apply, Ne.symm hij, Ne.symm hil, Ne.symm hik]
          ring
      simp [hz, hij, hil]

/-- The phase sum corrected by a weighted sum over the standard basis. -/
def designSum (f : (Fin d → ℂ) → ℂ) : ℂ :=
  (∑ z : Fin d → Fin 4, f (fun i => phase (z i))) +
    (4 : ℂ)^d * ∑ a : Fin d, f (fun i => if i = a then 1 else 0)

theorem designSum_sum {ι : Type*} [Fintype ι]
    (f : ι → (Fin d → ℂ) → ℂ) :
    designSum (fun z => ∑ a, f a z) = ∑ a, designSum (f a) := by
  simp only [designSum, sum_add_distrib, ← mul_sum]
  congr 1
  · exact sum_comm
  · congr 1
    exact sum_comm

private theorem designSum_mul (f : (Fin d → ℂ) → ℂ) (a : ℂ) :
    designSum (fun z => f z * a) = designSum f * a := by
  dsimp [designSum]
  rw [← sum_mul, ← sum_mul]
  ring

private theorem design_four (i j k l : Fin d) :
    designSum (fun z => conj (z i) * z j * conj (z k) * z l) =
      (4:ℂ)^d * ((if i = j ∧ k = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) := by
  unfold designSum
  rw [moment_four]
  have hb : (∑ a : Fin d,
      conj (if i = a then (1:ℂ) else 0) * (if j = a then 1 else 0) *
        conj (if k = a then 1 else 0) * (if l = a then 1 else 0)) =
      if i = j ∧ j = k ∧ k = l then 1 else 0 := by
    have hh (a : Fin d) :
        conj (if i = a then (1:ℂ) else 0) * (if j = a then 1 else 0) *
          conj (if k = a then 1 else 0) * (if l = a then 1 else 0) =
        if i = a then (if i = j ∧ j = k ∧ k = l then 1 else 0) else 0 := by
      by_cases hi : i = a
      · subst a
        by_cases hj : i = j <;> by_cases hk : j = k <;> by_cases hl : k = l <;>
          simp_all [eq_comm]
      · simp [hi]
    simp_rw [hh]
    simp
  rw [hb]
  ring

/-- The corrected phase sum preserves pointwise inequalities of real parts. -/
theorem re_designSum_mono (f g : (Fin d → ℂ) → ℂ)
    (h : ∀ z, (f z).re ≤ (g z).re) : (designSum f).re ≤ (designSum g).re := by
  have hc : (4:ℂ)^d = Complex.ofReal ((4:ℝ)^d) := by simp
  unfold designSum
  rw [hc]
  simp only [Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact add_le_add (sum_le_sum (fun z _ => h _))
    (mul_le_mul_of_nonneg_left (sum_le_sum (fun a _ => h _))
      (pow_nonneg (show (0:ℝ) ≤ 4 by norm_num) d))

/-- A finite complex quadratic form. -/
def quadratic (T : Matrix (Fin d) (Fin d) ℂ) (z : Fin d → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (z i) * z j * T i j

/-- Exact second product of quadratic forms under the corrected fourth moment. -/
theorem quadratic_product_sum (T U : Matrix (Fin d) (Fin d) ℂ) :
    designSum (fun z => quadratic T z * quadratic U z) =
      (4:ℂ)^d * (Matrix.trace T * Matrix.trace U + ∑ i, ∑ j, T i j * U j i) := by
  have h (z : Fin d → ℂ) : quadratic T z * quadratic U z =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (conj (z i) * z j * conj (z k) * z l) * (T i j * U k l) := by
    dsimp [quadratic]
    rw [sum_mul]
    simp_rw [sum_mul]
    simp_rw [mul_sum]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro k _
    apply sum_congr rfl; intro l _
    ring
  simp_rw [h, designSum_sum, designSum_mul, design_four]
  simp only [mul_add, add_mul, sum_add_distrib, sum_ite_irrel, sum_const_zero,
    mul_ite, ite_mul, mul_zero, mul_one, zero_mul, ite_and, sum_ite_eq, mem_univ, if_true,
    Matrix.trace, Matrix.diag_apply]
  simp only [← mul_sum, ← sum_mul]

#print axioms quadratic_product_sum
end
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
