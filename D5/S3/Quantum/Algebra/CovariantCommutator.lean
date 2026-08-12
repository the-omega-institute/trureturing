/- GID: D5/S3/Quantum/Algebra/CovariantCommutator
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive covariant commutator factorizations independently of a representation. -/

/- Library-search audit trail (2026-08-12):
   * Searches of the pinned mathlib tree for covariant representations, crossed products,
     skew group rings, and covariance-to-commutator lemmas found no theorem to wrap.
   * `SemiconjBy` is reused for its exact equation `U * f = translated * U`.
     The generic proof is the distributive law `sub_mul` after rewriting that equation.
   * `Matrix.smul_mul`, `Matrix.mul_diagonal`, `IsPrimitiveRoot.ne_one`, and
     `IsPrimitiveRoot.ne_zero` support the concrete finite-window witness.
-/

import D5.S3.Observer.WindowRegister

/-!
# Covariant commutator factorization

The algebraic declarations in this module require only a ring and a semiconjugacy equation.
The group-action wrapper therefore applies to any covariant pair with values in an arbitrary
ring, independently of any particular representation or universal construction.
-/

namespace D5.S3.Quantum.Algebra.CovariantCommutator

open D5.S3.Observer.WindowRegister

/-- A semiconjugacy equation factors the commutator with the conjugating element on the right. -/
theorem covariant_commutator_formula {B : Type*} [Ring B] {U f translated : B}
    (hcov : SemiconjBy U f translated) :
    U * f - f * U = (translated - f) * U := by
  rw [hcov.eq, sub_mul]

/-- The same factorization in the opposite commutator orientation. -/
theorem covariant_opposite_commutator_formula {B : Type*} [Ring B]
    {U f translated : B} (hcov : SemiconjBy U f translated) :
    f * U - U * f = (f - translated) * U := by
  rw [hcov.eq, sub_mul]

/-- The abstract factorization specialized to a group action and an arbitrary covariant pair. -/
theorem covariant_pair_commutator_formula {Gamma A B : Type*}
    [Group Gamma] [Semiring A] [Ring B]
    (action : Gamma →* (A ≃+* A)) (embed : A →+* B) (U : Gamma →* Bˣ)
    (hcov : ∀ g a, SemiconjBy (U g : B) (embed a) (embed (action g a)))
    (g : Gamma) (a : A) :
    (U g : B) * embed a - embed a * (U g : B) =
      (embed (action g a) - embed a) * (U g : B) :=
  covariant_commutator_formula (hcov g a)

/-- The covariant-pair formula in the opposite commutator orientation. -/
theorem covariant_pair_opposite_commutator_formula {Gamma A B : Type*}
    [Group Gamma] [Semiring A] [Ring B]
    (action : Gamma →* (A ≃+* A)) (embed : A →+* B) (U : Gamma →* Bˣ)
    (hcov : ∀ g a, SemiconjBy (U g : B) (embed a) (embed (action g a)))
    (g : Gamma) (a : A) :
    embed a * (U g : B) - (U g : B) * embed a =
      (embed a - embed (action g a)) * (U g : B) :=
  covariant_opposite_commutator_formula (hcov g a)

/-- The frozen finite-window Weyl relation is a concrete semiconjugacy instance. -/
theorem window_covariance (M : ℕ) [NeZero M] :
    SemiconjBy (clockMatrix M) (shiftMatrix M) (windowRoot M • shiftMatrix M) := by
  change clockMatrix M * shiftMatrix M =
    (windowRoot M • shiftMatrix M) * clockMatrix M
  simpa only [Matrix.smul_mul] using window_weyl M

/-- The two-address window clock and shift have a genuinely nonzero commutator. -/
theorem window_two_commutator_ne_zero :
    clockMatrix 2 * shiftMatrix 2 - shiftMatrix 2 * clockMatrix 2 ≠ 0 := by
  intro hzero
  have hcomm : clockMatrix 2 * shiftMatrix 2 = shiftMatrix 2 * clockMatrix 2 :=
    sub_eq_zero.mp hzero
  have hscalar :
      windowRoot 2 • (shiftMatrix 2 * clockMatrix 2) =
        shiftMatrix 2 * clockMatrix 2 :=
    (window_weyl 2).symm.trans hcomm
  have hentry :
      (shiftMatrix 2 * clockMatrix 2) (0 : ZMod 2) (1 : ZMod 2) = windowRoot 2 := by
    rw [clockMatrix, Matrix.mul_diagonal, shiftMatrix, Matrix.circulant_apply,
      if_pos (by decide), one_mul,
      ZMod.val_one'' (by norm_num : (2 : ℕ) ≠ 1), pow_one]
  have hroot_mul : windowRoot 2 * windowRoot 2 = windowRoot 2 := by
    simpa [Matrix.smul_apply, smul_eq_mul, hentry] using
      congrFun (congrFun hscalar (0 : ZMod 2)) (1 : ZMod 2)
  have hroot_ne_zero : windowRoot 2 ≠ 0 :=
    (windowRoot_isPrimitiveRoot 2).ne_zero (by norm_num)
  have hroot_eq_one : windowRoot 2 = 1 := by
    apply mul_left_cancel₀ hroot_ne_zero
    simpa using hroot_mul
  exact (windowRoot_isPrimitiveRoot 2).ne_one (by norm_num) hroot_eq_one

/-- An explicit inhabited covariance relation whose resulting commutator does not vanish. -/
theorem window_two_covariant_commutator_witness :
    SemiconjBy (clockMatrix 2) (shiftMatrix 2) (windowRoot 2 • shiftMatrix 2) ∧
      clockMatrix 2 * shiftMatrix 2 - shiftMatrix 2 * clockMatrix 2 ≠ 0 :=
  ⟨window_covariance 2, window_two_commutator_ne_zero⟩

end D5.S3.Quantum.Algebra.CovariantCommutator
