/- GID: D5/S0/Observation/MatrixFirstMomentCoefficientBridge
   generality: G
   mirror-B: D5/B/S0/Observation/MatrixFirstMomentCoefficientBridge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities]
   utility: none
   digest: The first unequal Hermitian power trace determines the first unequal characteristic coefficient. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic

/-!
proof_shape: matrix_first_moment_coefficient_bridge: content.
admission_basis: escape-witness.
escape_witness: actual unitary diagonalization supplies the matrix power sums;
Vieta and the elementary-symmetric Newton identity supply the recurrence.
Subtracting the recurrences isolates the first coefficient defect. The live
consumer is BajnokBeattyFirstCharacteristicDefect.first_characteristic_defect.

The neighboring NewtonPowerSumCharacteristicPolynomial module recovers an entire
split polynomial from all dimension-many power sums. RegularCHS.Newton proves a
spectral walk identity and a complete-homogeneous recurrence. Neither supplies
this first unequal descending characteristic coefficient. The spectral proof
below follows RegularCHS.Newton.sum_eigenvalues_pow_eq_closedWalks, and the
induction uses the same exact Mathlib Newton primitive as the S0 theorem.
No recurrence or spectral factorization is taken as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S0.Observation.MatrixFirstMomentCoefficientBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_pow_eq_eval_psum
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (k : ℕ) :
    Matrix.trace (A ^ k) =
      MvPolynomial.eval (fun i => (hA.eigenvalues i : ℂ))
        (MvPolynomial.psum ι ℂ k) := by
  calc
    Matrix.trace (A ^ k) = ∑ i, (hA.eigenvalues i : ℂ) ^ k := by
      conv_lhs => rw [hA.spectral_theorem, ← map_pow]
      simpa only [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
        Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.diagonal_pow,
        Matrix.trace_diagonal, Function.comp_apply, Pi.pow_apply,
        RCLike.ofReal_eq_complex_ofReal]
    _ = _ := by simp [MvPolynomial.psum]

private theorem descending_coeff_eq_eval_esymm
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    A.charpoly.coeff (Fintype.card ι - k) =
      (-1 : ℂ) ^ k *
        MvPolynomial.eval (fun i => (hA.eigenvalues i : ℂ))
          (MvPolynomial.esymm ι ℂ k) := by
  have hVieta := Polynomial.coeff_eq_esymm_roots_of_splits hA.splits_charpoly
    (k := Fintype.card ι - k)
    (by simpa only [Matrix.charpoly_natDegree_eq_dim] using Nat.sub_le (Fintype.card ι) k)
  have hsub : Fintype.card ι - (Fintype.card ι - k) = k := by omega
  rw [Matrix.charpoly_natDegree_eq_dim, A.charpoly_monic.leadingCoeff,
    one_mul, hsub, hA.roots_charpoly_eq_eigenvalues,
    ← MvPolynomial.aeval_esymm_eq_multiset_esymm ι ℂ k
      (RCLike.ofReal ∘ hA.eigenvalues)] at hVieta
  simpa only [MvPolynomial.aeval_eq_eval, Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal] using hVieta

-- Derive the recurrence for actual matrix characteristic coefficients.
-- It is private and used by the coefficient comparison below.
private theorem matrix_newton_identity
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    (k : ℂ) * A.charpoly.coeff (Fintype.card ι - k) +
      (∑ a ∈ Finset.antidiagonal k with a.1 < k,
        A.charpoly.coeff (Fintype.card ι - a.1) * Matrix.trace (A ^ a.2)) = 0 := by
  let x : ι → ℂ := fun i => (hA.eigenvalues i : ℂ)
  let E : ℕ → ℂ := fun j => MvPolynomial.eval x (MvPolynomial.esymm ι ℂ j)
  let P : ℕ → ℂ := fun j => MvPolynomial.eval x (MvPolynomial.psum ι ℂ j)
  let S : ℂ := ∑ a ∈ Finset.antidiagonal k with a.1 < k,
    (-1 : ℂ) ^ a.1 * E a.1 * P a.2
  have hNewton : (k : ℂ) * E k = (-1 : ℂ) ^ (k + 1) * S := by
    simpa [E, P, S] using congrArg (MvPolynomial.eval x)
      (MvPolynomial.mul_esymm_eq_sum ι ℂ k)
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ (k + 1) = -1 := by
    rw [pow_succ, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]
  have hscaled : (k : ℂ) * ((-1 : ℂ) ^ k * E k) = -S := by
    calc
      (k : ℂ) * ((-1 : ℂ) ^ k * E k) =
          (-1 : ℂ) ^ k * ((k : ℂ) * E k) := by ring
      _ = (-1 : ℂ) ^ k * ((-1 : ℂ) ^ (k + 1) * S) := by rw [hNewton]
      _ = -S := by rw [← mul_assoc, hsign, neg_one_mul]
  have hsum :
      (∑ a ∈ Finset.antidiagonal k with a.1 < k,
        A.charpoly.coeff (Fintype.card ι - a.1) * Matrix.trace (A ^ a.2)) = S := by
    apply Finset.sum_congr rfl
    intro a ha
    have haFirst : a.1 < k := (Finset.mem_filter.mp ha).2
    simpa only [E, P, x] using congrArg₂ (fun u v : ℂ => u * v)
      (descending_coeff_eq_eval_esymm A hA (k := a.1) (by omega))
      (trace_pow_eq_eval_psum A hA a.2)
  rw [descending_coeff_eq_eval_esymm A hA hk, hsum]
  exact add_eq_zero_iff_eq_neg.mpr hscaled

/-- Prefix equality of actual matrix power traces determines the descending
characteristic coefficients up to the same prefix. The next difference has the
Newton factor `n` and the negative of the next power-trace difference.

Here descending index zero means the leading coefficient. -/
theorem matrix_first_moment_coefficient_bridge
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ Fintype.card ι)
    (hTrace : ∀ k : ℕ, 0 < k → k < n →
      Matrix.trace (A ^ k) = Matrix.trace (B ^ k)) :
    (∀ k : ℕ, k < n →
      A.charpoly.coeff (Fintype.card ι - k) =
        B.charpoly.coeff (Fintype.card ι - k)) ∧
    (n : ℂ) * (B.charpoly.coeff (Fintype.card ι - n) -
      A.charpoly.coeff (Fintype.card ι - n)) =
        -(Matrix.trace (B ^ n) - Matrix.trace (A ^ n)) := by
  classical
  have hcoeff : ∀ k : ℕ, k < n →
      A.charpoly.coeff (Fintype.card ι - k) =
        B.charpoly.coeff (Fintype.card ι - k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hkn
        by_cases hk0 : k = 0
        · subst k
          rw [descending_coeff_eq_eval_esymm A hA (k := 0) (Nat.zero_le _),
            descending_coeff_eq_eval_esymm B hB (k := 0) (Nat.zero_le _)]
          simp
        have hkN : k ≤ Fintype.card ι := by omega
        have hsum :
            (∑ a ∈ Finset.antidiagonal k with a.1 < k,
              A.charpoly.coeff (Fintype.card ι - a.1) * Matrix.trace (A ^ a.2)) =
            (∑ a ∈ Finset.antidiagonal k with a.1 < k,
              B.charpoly.coeff (Fintype.card ι - a.1) * Matrix.trace (B ^ a.2)) := by
          apply Finset.sum_congr rfl
          intro a ha
          have haData := Finset.mem_filter.mp ha
          have haSum := Finset.mem_antidiagonal.mp haData.1
          have haFirst : a.1 < k := haData.2
          rw [ih a.1 haFirst (by omega), hTrace a.2 (by omega) (by omega)]
        have hNA := matrix_newton_identity A hA hkN
        have hNB := matrix_newton_identity B hB hkN
        rw [hsum] at hNA
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hk0)
          (add_right_cancel (hNA.trans hNB.symm))
  refine ⟨hcoeff, ?_⟩
  have hsumDiff :
      (∑ a ∈ Finset.antidiagonal n with a.1 < n,
        B.charpoly.coeff (Fintype.card ι - a.1) * Matrix.trace (B ^ a.2)) -
      (∑ a ∈ Finset.antidiagonal n with a.1 < n,
        A.charpoly.coeff (Fintype.card ι - a.1) * Matrix.trace (A ^ a.2)) =
      Matrix.trace (B ^ n) - Matrix.trace (A ^ n) := by
    calc
      _ = ∑ a ∈ Finset.antidiagonal n with a.1 < n,
          (B.charpoly.coeff (Fintype.card ι - a.1) * Matrix.trace (B ^ a.2) -
            A.charpoly.coeff (Fintype.card ι - a.1) * Matrix.trace (A ^ a.2)) := by
        rw [Finset.sum_sub_distrib]
      _ = B.charpoly.coeff (Fintype.card ι - 0) * Matrix.trace (B ^ n) -
          A.charpoly.coeff (Fintype.card ι - 0) * Matrix.trace (A ^ n) := by
        apply Finset.sum_eq_single (0, n)
        · intro a ha hane
          have haData := Finset.mem_filter.mp ha
          have haSum := Finset.mem_antidiagonal.mp haData.1
          have haFirst : a.1 < n := haData.2
          have haFirstPos : 0 < a.1 := by
            by_contra h
            have hai : a.1 = 0 := by omega
            have haj : a.2 = n := by omega
            exact hane (Prod.ext hai haj)
          rw [hcoeff a.1 haFirst, hTrace a.2 (by omega) (by omega), sub_self]
        · intro hnot
          exact (hnot (by simp [hn])).elim
      _ = Matrix.trace (B ^ n) - Matrix.trace (A ^ n) := by
        rw [descending_coeff_eq_eval_esymm B hB (k := 0) (Nat.zero_le _),
          descending_coeff_eq_eval_esymm A hA (k := 0) (Nat.zero_le _)]
        simp
  have hNA := matrix_newton_identity A hA hnN
  have hNB := matrix_newton_identity B hB hnN
  linear_combination hNB - hNA - hsumDiff

#print axioms matrix_first_moment_coefficient_bridge

end D5.S0.Observation.MatrixFirstMomentCoefficientBridge
