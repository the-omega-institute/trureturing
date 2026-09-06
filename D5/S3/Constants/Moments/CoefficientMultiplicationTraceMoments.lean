/- GID: D5/S3/Constants/Moments/CoefficientMultiplicationTraceMoments
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/CoefficientMultiplicationTraceMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient matrix power traces equal root moments with algebraic multiplicity. -/

import D5.S3.Constants.Moments.CoefficientDrivenJacobiCharacteristicPolynomial
import D5.S3.Constants.NewtonHankelRealRootCriterion
import D5.S0.Observation.PowerTraceCharacteristicPolynomialSaturation

/- Library-search audit trail (2026-09-07):
   1. D5 searches for coefficientMultiplicationMatrix, trace/pow, charpoly/roots,
      companion and eigenvalue sums found no arbitrary-degree power-trace bridge.
      All public declarations of the six preregistered modules were enumerated and read.
      MatrixTracePowerSum is size two only. The exact matrix recurrence in
      power_trace_characteristic_polynomial_saturation is imported and applied below.
      The coefficient module's private multiplication_matrix_charpoly is not reproved.
   2. Pinned Mathlib v4.33.0 (db584cd6d46c92f209a44c0f1c829460d327499d): searched
      Matrix.Charpoly Basic/Coeff/Eigs/Minpoly, PowerBasis.leftMulMatrix,
      Algebra.charpoly_leftMulMatrix, AdjoinRoot, NewtonIdentities, Polynomial.roots,
      triangular and generalized-eigenspace APIs. trace_eq_sum_roots_charpoly only
      supplies the first power; roots_multiset_prod_X_sub_C retains multiplicity.
      No exact arbitrary-power result was found. Triangular charpoly, Cayley-Hamilton,
      inverse and trace primitives are reused, not reproved.
   3. Pinned batteries/aesop/Qq/Cli/LeanSearchClient/importGraph/plausible/proofwidgets:
      trace/pow, companion and Newton-identities searches returned no matches.
      Online NyxID/Tavily searches for Lean matrix power traces and characteristic roots
      returned the first-power Mathlib APIs and standard mathematical references, no exact
      third-party Lean result. Requests: 71788d27-cbbe-4d54-ba10-5479c916746d and
      c997fb64-8ab8-4406-82c6-31ba117914e2. This is a scoped negative.
   4. Original preregistered witness retained: the public conclusion is produced by
      the named Krylov construction on its live proof path. Unit subdiagonal entries
      give a determinant-one intertwiner with the lower triangular root matrix.
      Repeated and zero roots require no special case. The split factorization already
      forces monicity, so the statement needs no separate monicity premise.
      proof_shape: content; admission_basis: escape-witness.
      Computational content: none (arbitrary polynomial, root list and natural exponent).
      Import generalities: I, G, G respectively; hence this module is I. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Polynomial Finset
open D5.S3.Constants.Moments.CoefficientDrivenJacobiCharacteristicPolynomial
open D5.S3.Constants.NewtonHankelRealRootCriterion
open D5.S0.Observation.PowerTraceCharacteristicPolynomialSaturation

namespace D5.S3.Constants.Moments.CoefficientMultiplicationTraceMoments

private def rootBidiagonal {d : Nat} (roots : Fin d → Complex) :
    Matrix (Fin d) (Fin d) Complex :=
  fun i j => if i = j then roots i else if i.val = j.val + 1 then 1 else 0

private theorem root_bidiagonal_lower {d : Nat} (roots : Fin d → Complex) :
    (rootBidiagonal roots).IsLowerTriangular := by
  intro i j hij
  have h : i < j := hij
  simp [rootBidiagonal, ne_of_lt h, show i.val ≠ j.val + 1 by omega]

private theorem root_bidiagonal_charpoly {d : Nat} (roots : Fin d → Complex) :
    (rootBidiagonal roots).charpoly = ∏ j, (X - C (roots j)) := by
  have htri : (rootBidiagonal roots)ᵀ.IsUpperTriangular :=
    (root_bidiagonal_lower roots).transpose
  have h := Matrix.charpoly_of_isUpperTriangular (rootBidiagonal roots)ᵀ htri
  simpa [rootBidiagonal] using h

private theorem root_bidiagonal_power_band {d : Nat} (roots : Fin d → Complex)
    (n : Nat) (i j : Fin d) (h : j.val + n < i.val) :
    (rootBidiagonal roots ^ n) i j = 0 := by
  induction n generalizing i with
  | zero => simp [show i ≠ j by intro e; subst i; omega]
  | succ n ih =>
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : i = k
      · subst k
        rw [ih i (by omega), mul_zero]
      · by_cases hik' : i.val = k.val + 1
        · rw [ih k (by omega), mul_zero]
        · simp [rootBidiagonal, hik, hik']

private theorem root_bidiagonal_power_edge {d : Nat} (hd : 0 < d)
    (roots : Fin d → Complex) (n : Nat) (hn : n < d) :
    (rootBidiagonal roots ^ n) ⟨n, hn⟩ ⟨0, hd⟩ = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Matrix.mul_apply]
      rw [Finset.sum_eq_single (⟨n, by omega⟩ : Fin d)]
      · rw [ih (by omega)]
        simp [rootBidiagonal, Fin.ext_iff]
      · intro k _ hk
        by_cases hik : (⟨n + 1, hn⟩ : Fin d) = k
        · subst k
          rw [root_bidiagonal_power_band roots n _ _ (by simp), mul_zero]
        · have hkn : n ≠ k.val := by
            intro e
            apply hk
            exact Fin.ext e.symm
          simp [rootBidiagonal, hik, hkn]
      · simp

private def rootKrylov {d : Nat} (hd : 0 < d) (roots : Fin d → Complex) :
    Matrix (Fin d) (Fin d) Complex :=
  fun i j => (rootBidiagonal roots ^ j.val) i ⟨0, hd⟩

private theorem root_krylov_det {d : Nat} (hd : 0 < d) (roots : Fin d → Complex) :
    (rootKrylov hd roots).det = 1 := by
  have htri : (rootKrylov hd roots).IsUpperTriangular := by
    intro i j hij
    exact root_bidiagonal_power_band roots j.val i ⟨0, hd⟩ (by simpa using hij)
  rw [Matrix.det_of_isUpperTriangular htri]
  simp only [rootKrylov, root_bidiagonal_power_edge hd roots, Finset.prod_const_one]

private theorem root_krylov_shift {d : Nat} (hd : 0 < d) (roots : Fin d → Complex)
    (i j : Fin d) :
    (rootBidiagonal roots * rootKrylov hd roots) i j =
      (rootBidiagonal roots ^ (j.val + 1)) i ⟨0, hd⟩ := by
  rw [pow_succ', Matrix.mul_apply, Matrix.mul_apply]
  rfl

private theorem root_krylov_intertwines (q : Real[X]) (hd : 0 < q.natDegree)
    (roots : Fin q.natDegree → Complex)
    (hfactor : q.map Complex.ofRealHom = ∏ j, (X - C (roots j))) :
    rootKrylov hd roots * (coefficientMultiplicationMatrix q).map Complex.ofRealHom =
      rootBidiagonal roots * rootKrylov hd roots := by
  have hchar : (rootBidiagonal roots).charpoly = q.map Complex.ofRealHom :=
    (root_bidiagonal_charpoly roots).trans hfactor.symm
  have hcayley := (power_trace_characteristic_polynomial_saturation
    (rootBidiagonal roots)).1
  rw [hchar] at hcayley
  ext i j
  rw [root_krylov_shift, Matrix.mul_apply]
  by_cases hlast : j.val + 1 = q.natDegree
  · simp only [Matrix.map_apply, coefficientMultiplicationMatrix, hlast, if_true, map_neg]
    rw [hcayley]
    simp only [Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.coeff_map, mul_neg, ← Finset.sum_neg_distrib]
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [rootKrylov, mul_comm]
  · have hnext : j.val + 1 < q.natDegree := by omega
    simp only [Matrix.map_apply, coefficientMultiplicationMatrix, hlast, if_false,
      apply_ite, map_one, map_zero]
    rw [Finset.sum_eq_single (⟨j.val + 1, hnext⟩ : Fin q.natDegree)]
    · simp [rootKrylov]
    · intro k _ hk
      have hk' : k.val ≠ j.val + 1 := by
        intro e
        exact hk (Fin.ext e)
      simp [hk']
    · simp

private theorem root_bidiagonal_power_diagonal {d : Nat} (roots : Fin d → Complex)
    (n : Nat) (i : Fin d) : (rootBidiagonal roots ^ n) i i = roots i ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Matrix.mul_apply, Finset.sum_eq_single i]
      · simp [rootBidiagonal, ih, pow_succ, mul_comm]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with hki | hik
        · rw [(root_bidiagonal_lower roots).pow n hki, mul_zero]
        · rw [root_bidiagonal_lower roots hik, zero_mul]
      · simp

/-- Every normalized coefficient-multiplication power trace is the corresponding root
moment. The factorization indexes roots with algebraic multiplicity; repeated, nonreal
and zero roots are allowed, and the exponent includes zero. -/
theorem coefficient_multiplication_trace_pow_eq_rootPowerMoment
    (q : Real[X]) (hd : 0 < q.natDegree) (roots : Fin q.natDegree → Complex)
    (hfactor : q.map Complex.ofRealHom = ∏ j, (X - C (roots j))) (n : Nat) :
    Matrix.trace (coefficientMultiplicationMatrix q ^ n) / (q.natDegree : Real) =
      rootPowerMoment roots n := by
  let P := rootKrylov hd roots
  let S := (coefficientMultiplicationMatrix q).map Complex.ofRealHom
  let T := rootBidiagonal roots
  have hdet : IsUnit P.det := by rw [root_krylov_det]; exact isUnit_one
  have hunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hdet
  have hinter : SemiconjBy P S T := root_krylov_intertwines q hd roots hfactor
  have hpowers : P * S ^ n * P⁻¹ = T ^ n := by
    rw [(hinter.pow_right n).eq, Matrix.mul_assoc, Matrix.mul_nonsing_inv P hdet, mul_one]
  have htrace : Matrix.trace (S ^ n) = ∑ j, roots j ^ n := by
    rw [← Matrix.trace_conj hunit (S ^ n), hpowers]
    exact Finset.sum_congr rfl (fun j _ => root_bidiagonal_power_diagonal roots n j)
  have hreal : Matrix.trace (coefficientMultiplicationMatrix q ^ n) =
      (∑ j, roots j ^ n).re := by
    have h := congrArg Complex.re htrace
    change (Matrix.trace (((coefficientMultiplicationMatrix q).map
      Complex.ofRealHom) ^ n)).re = _ at h
    rw [← Matrix.map_pow, ← AddMonoidHom.map_trace] at h
    exact h
  rw [hreal, rootPowerMoment]

#print axioms coefficient_multiplication_trace_pow_eq_rootPowerMoment

end D5.S3.Constants.Moments.CoefficientMultiplicationTraceMoments
