/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnTransfer
   mirror-E: none(waiver:integral-column-moment-functional)
   anchors: []
   utility: none
   digest: The orthogonal moment functional recovers every Motzkin column. -/

import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDefs
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelOrthogonal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnTransfer

open Polynomial Finset CiglerMotzkinHankelDefs CiglerMotzkinHankelTransfer
open CiglerMotzkinHankelOrthogonal

/-- Moving the three-term recurrence across the moment pairing recovers all columns. -/
theorem column_moments : ∃ ℓ : Base[X] →ₗ[Base] Base,
    (∀ n k : ℕ, ℓ (X ^ n * orthogonal k) = motzkin n k) ∧
      (∀ i j : ℕ, ℓ (orthogonal i * orthogonal j) = if i = j then 1 else 0) := by
  classical
  let ℓ : Base[X] →ₗ[Base] Base :=
    Polynomial.lsum (fun n => LinearMap.mulRight Base (motzkin n 0))
  have monomial (n : ℕ) : ℓ (X ^ n) = motzkin n 0 := by
    simp [ℓ, Polynomial.lsum, X_pow_eq_monomial]
  have scalar (c : Base) (f : Base[X]) : ℓ (C c * f) = c * ℓ f := by
    simpa only [smul_eq_C_mul, smul_eq_mul] using ℓ.map_smul c f
  have columns : ∀ k n : ℕ, ℓ (X ^ n * orthogonal k) = motzkin n k := by
    apply Nat.twoStepInduction
    · intro n
      simpa [orthogonal] using monomial n
    · intro n
      have recurrence : motzkin (n + 1) 0 =
          sVar * motzkin n 0 + motzkin n 1 := by simp [motzkin]
      have polynomial_identity : X ^ n * orthogonal 1 =
          X ^ (n + 1) - C sVar * X ^ n := by
        rw [orthogonal, pow_succ]
        ring
      rw [polynomial_identity, map_sub, scalar, monomial, monomial]
      rw [recurrence]
      ring
    · intro k previous current n
      have polynomial_identity : X ^ n * orthogonal (k + 2) =
          X ^ (n + 1) * orthogonal (k + 1) -
            C tVar * (X ^ n * orthogonal (k + 1)) - X ^ n * orthogonal k := by
        rw [orthogonal, pow_succ]
        ring
      rw [polynomial_identity, map_sub, map_sub, scalar, current, current, previous,
        motzkin, if_neg (by omega : k + 1 ≠ 0), if_neg (by omega : k + 1 ≠ 0),
        Nat.add_sub_cancel]
      ring
  have triangular (i j : ℕ) (order : i ≤ j) :
      ℓ (orthogonal i * orthogonal j) = if i = j then 1 else 0 := by
    have expansion := (orthogonal i).as_sum_range' (n := i + 1)
      (by rw [(orthogonal_basis i).1.natDegree_eq]; omega)
    rw [expansion, sum_mul, map_sum]
    simp_rw [← C_mul_X_pow_eq_monomial, mul_assoc, scalar, columns]
    by_cases equal : i = j
    · subst j
      rw [if_pos rfl, sum_eq_single i]
      · rw [(motzkin_triangle i).2, mul_one]
        simpa [(orthogonal_basis i).1.natDegree_eq] using
          (orthogonal_basis i).1.monic.coeff_natDegree
      · intro a member different
        have smaller : a < i := by simp only [mem_range] at member; omega
        rw [(motzkin_triangle a).1 i smaller, mul_zero]
      · simp
    · rw [if_neg equal]
      apply sum_eq_zero
      intro a member
      have smaller : a < j := by simp only [mem_range] at member; omega
      rw [(motzkin_triangle a).1 j smaller, mul_zero]
  refine ⟨ℓ, (fun n k => columns k n), ?_⟩
  intro i j
  rcases le_total i j with order | order
  · exact triangular i j order
  · rw [mul_comm, triangular j i order]
    simp [eq_comm]

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnTransfer
