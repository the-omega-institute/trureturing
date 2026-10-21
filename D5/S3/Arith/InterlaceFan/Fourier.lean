/- GID: D5/S3/Arith/InterlaceFan/Fourier
   generality: G
   mirror-B: D5/B/S3/Arith/InterlaceFan/Fourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic, mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Basic, mathlib/module/Mathlib.Algebra.Polynomial.Roots, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Cosine evaluation isomorphism and the closed faces of the interlace fan. -/

import D5.S3.Arith.InterlaceFan.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

noncomputable section
open Finset Polynomial
open D5.S3.Arith.InterlaceFan.Defs

namespace D5.S3.Arith.InterlaceFan.Fourier

private def cosine (n j k : ℕ) : ℝ := Real.cos (2 * Real.pi * j * k / n)

private def evaluation (n : ℕ) :
    (Fin (n / 2 + 1) → ℝ) →ₗ[ℝ] (Fin (n / 2 + 1) → ℝ) where
  toFun a j := ∑ k : Fin (n / 2 + 1), cosine n j k * a k
  map_add' a b := by ext j; simp [mul_add, sum_add_distrib]
  map_smul' c a := by ext j; simp [mul_left_comm, ← mul_sum]

private lemma cosine_nodes_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (fun j : Fin (n / 2 + 1) => cosine n j 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb (j : Fin (n / 2 + 1)) :
      0 ≤ 2 * Real.pi * (j : ℕ) / n ∧ 2 * Real.pi * (j : ℕ) / n ≤ Real.pi := by
    constructor
    · positivity
    · apply (div_le_iff₀ hnR).mpr
      have hj : (2 : ℝ) * (j : ℕ) ≤ n := by exact_mod_cast (by omega : 2 * (j : ℕ) ≤ n)
      nlinarith [Real.pi_pos]
  intro i j hij
  have he : 2 * Real.pi * (i : ℕ) / n = 2 * Real.pi * (j : ℕ) / n :=
    Real.strictAntiOn_cos.injOn (hb i) (hb j) (by simpa [cosine] using hij)
  have hv : (i : ℕ) = (j : ℕ) := by
    have hr : ((i : ℕ) : ℝ) = (j : ℕ) := by
      apply mul_left_cancel₀ (show (2 : ℝ) * Real.pi ≠ 0 by positivity)
      exact (div_left_inj' hnR.ne').mp he
    exact_mod_cast hr
  exact Fin.ext hv

private lemma evaluation_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (evaluation n) := by
  intro a b hab
  let p : ℝ[X] := ∑ k : Fin (n / 2 + 1),
    (a k - b k) • Polynomial.Chebyshev.T ℝ (k : ℕ)
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (cosine_nodes_injective n hn)
    · intro j
      have hj := sub_eq_zero.mpr (congrFun hab j)
      simpa [p, evaluation, cosine, Polynomial.eval_finsetSum,
        Polynomial.eval_smul, Polynomial.Chebyshev.T_real_cos, mul_comm,
        mul_left_comm, mul_assoc, mul_div_assoc, mul_sub, sub_mul, sum_sub_distrib] using hj
    · have hd : p.natDegree ≤ n / 2 := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro k hk
        exact (Polynomial.natDegree_smul_le _ _).trans (by
          simp only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
          omega)
      simpa using (Nat.lt_succ_of_le hd)
  have hli := (Polynomial.Chebyshev.chebyshevTSequence ℝ).linearIndependent.comp
    (fun k : Fin (n / 2 + 1) => (k : ℕ)) Fin.val_injective
  have he := (Fintype.linearIndependent_iff.mp hli) (fun k => a k - b k) hp
  funext k
  exact sub_eq_zero.mp (he k)

/-- If all certificate values agree, the sigma-coordinate vector is zero. -/
theorem eq_zero_of_I_const (n : ℕ) (hn : 2 ≤ n) (x : Fin (n / 2) → ℝ)
    (c : ℝ) (h : ∀ j ∈ certIdx n, I n j x = c) : x = 0 := by
  let a : Fin (n / 2 + 1) → ℝ := Fin.cons (-c) (fun k => -x k)
  have ha : evaluation n a = evaluation n 0 := by
    ext j
    have hj := h j (by simp [certIdx]; omega)
    simpa [evaluation, a, Fin.sum_univ_succ, cosine, I, Fin.cons_zero,
      Fin.cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one,
      mul_neg, sum_neg_distrib, sub_eq_add_neg, add_comm] using sub_eq_zero.mpr hj
  have hz := evaluation_injective n hn ha
  funext k
  have hk := congrFun hz k.succ
  simpa [a] using hk

/-- Enlarging a required certificate set gives a smaller closed face. -/
theorem face_antitone (n : ℕ) {S T : Finset ℕ} (hST : S ⊆ T) :
    face n T ⊆ face n S := by
  intro x hx s hs j hj
  exact hx s (hST hs) j hj

end D5.S3.Arith.InterlaceFan.Fourier
