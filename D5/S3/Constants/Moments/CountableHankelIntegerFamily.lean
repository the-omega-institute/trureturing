/- GID: D5/S3/Constants/Moments/CountableHankelIntegerFamily
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/CountableHankelIntegerFamily
   mirror-E: none(waiver:countable-spectrum-classical-analysis)
   anchors: []
   utility: none
   digest: One integer matrix realizes a complete-spectrum negative polynomial subspace. -/

import D5.S3.Constants.Moments.CountableHankelIntegerWitness
import D5.S3.Constants.Moments.CountableHankelNegativeFamily
import D5.S3.Constants.Moments.IntegerNegativeFamilyQuadratic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! A common degree and simultaneous approximation retain the complete spectral form. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Polynomial
open scoped BigOperators ComplexConjugate

namespace D5.S3.Constants.Moments.CountableHankelNegativeWitness

/-- A single finite integer matrix is strictly negative on every nonzero real
combination for the complete weighted ordinary-square form. Its real
coefficient map is injective. The empty family is included. -/
theorem exists_integer_negative_family {ι : Type*} {k : ℕ} (z w : ι → ℂ)
    (c : Equiv.Perm ι) (hz : ∀ i, ‖z i‖ ≤ 1)
    (hzi : Function.Injective z) (hzc : ∀ i, z (c i) = conj (z i))
    (hwc : ∀ i, w (c i) = conj (w i))
    (hw : Summable (fun i => ‖w i‖))
    (hfinite : ∀ r : ℝ, 0 < r → {i | r ≤ ‖z i‖}.Finite)
    (s : Fin k → ι) (hs : Function.Injective s)
    (hsep : ∀ a b, s a ≠ c (s b)) (hws : ∀ j, w (s j) ≠ 0) :
    ∃ N : ℕ, ∃ U : Fin k → Fin (N + 1) → ℤ,
      (∀ t : Fin k → ℝ, t ≠ 0 →
        (∑' i, w i * (∑ j, (t j : ℂ) *
          ∑ a : Fin (N + 1), (U j a : ℂ) * z i ^ (a : ℕ)) ^ 2).re < 0) ∧
      Function.Injective
        (fun t : Fin k → ℝ => fun a : Fin (N + 1) => ∑ j, t j * (U j a : ℝ)) := by
  classical
  obtain ⟨p, hp⟩ := exists_real_negative_family z w c hz hzi hzc hwc hw hfinite s hs hsep hws
  let N := Finset.univ.sup (fun j => (p j).natDegree)
  let A : Fin k → Fin (N + 1) → ℝ := fun j a => (p j).coeff a
  have hdegree (j : Fin k) : (p j).natDegree < N + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ j))
  have heval (j : Fin k) (x : ℂ) : (p j).eval₂ Complex.ofRealHom x =
      ∑ a : Fin (N + 1), (A j a : ℂ) * x ^ (a : ℕ) := by
    rw [Polynomial.eval₂_eq_sum_range' Complex.ofRealHom (hdegree j)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  have hcombine (t : Fin k → ℝ) (x : ℂ) :
      (∑ j, t j • p j).eval₂ Complex.ofRealHom x =
        ∑ a : Fin (N + 1), ((∑ j, t j * A j a : ℝ) : ℂ) * x ^ (a : ℕ) := by
    calc
      _ = ∑ j, (t j : ℂ) * ∑ a : Fin (N + 1), (A j a : ℂ) * x ^ (a : ℕ) := by
        simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_smul,
          Complex.ofRealHom_eq_coe, heval]
      _ = _ := by
        simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro j _
        ring
  let M : Fin (N + 1) → Fin (N + 1) → ℝ := fun a b =>
    (∑' i, w i * z i ^ ((a : ℕ) + (b : ℕ))).re
  have hgap (t : Fin k → ℝ) :
      (∑ a, ∑ b, (∑ j, t j * A j a) * (∑ j, t j * A j b) * M a b) ≤
        -(∑ j, (t j) ^ 2) := by
    have h := hp t
    simp_rw [hcombine t] at h
    rw [quadratic_identity z w hz hw N] at h
    exact h
  obtain ⟨U, hU⟩ := exists_integer_negative_family_quadratic M A (by
    intro t ht
    have hS : 0 < ∑ j, (t j) ^ 2 := by
      refine lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) ?_
      intro hzero
      apply ht
      funext j
      exact ((Finset.sum_sq_eq_zero_iff Finset.univ t).mp hzero.symm) j (Finset.mem_univ _)
    exact lt_of_le_of_lt (hgap t) (by linarith))
  have hinteger (t : Fin k → ℝ) (x : ℂ) :
      (∑ a : Fin (N + 1), ((∑ j, t j * (U j a : ℝ) : ℝ) : ℂ) * x ^ (a : ℕ)) =
        ∑ j, (t j : ℂ) * ∑ a : Fin (N + 1), (U j a : ℂ) * x ^ (a : ℕ) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    ring
  refine ⟨N, U, ?_, ?_⟩
  · intro t ht
    have hid := quadratic_identity z w hz hw N (fun a => ∑ j, t j * (U j a : ℝ))
    simp_rw [hinteger t] at hid
    rw [hid]
    exact hU t ht
  · intro t v htv
    have hzero (a : Fin (N + 1)) : ∑ j, (t - v) j * (U j a : ℝ) = 0 := by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (congrFun htv a)
    have hdiff : t - v = 0 := by
      by_contra hdiff
      have hbad := hU (t - v) hdiff
      simp only [hzero, zero_mul, Finset.sum_const_zero] at hbad
      exact (lt_irrefl (0 : ℝ)) hbad
    exact sub_eq_zero.mp hdiff

end D5.S3.Constants.Moments.CountableHankelNegativeWitness
