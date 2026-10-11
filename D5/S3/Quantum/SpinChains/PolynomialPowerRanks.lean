/- GID: D5/S3/Quantum/SpinChains/PolynomialPowerRanks
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/PolynomialPowerRanks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A normalized polynomial certifies simultaneous maximal ranks of all matrix powers. -/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators

namespace D5.S3.Quantum.SpinChains.PolynomialPowerRanks

/-- If all power ranks are bounded by those at a nilpotent specialization, a polynomial
normalized to one at that specialization certifies equality of every power rank. -/
theorem exists_polynomial_power_rank_certificate
    {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ K)) (x0 : σ → K) (H : ℕ)
    (hnil : A.map (MvPolynomial.eval x0) ^ H = 0)
    (hbound : ∀ (x : σ → K) (r : ℕ),
      (A.map (MvPolynomial.eval x) ^ r).rank ≤
        (A.map (MvPolynomial.eval x0) ^ r).rank) :
    ∃ P : MvPolynomial σ K, MvPolynomial.eval x0 P = 1 ∧
      ∀ (x : σ → K), MvPolynomial.eval x P ≠ 0 → ∀ r : ℕ,
        (A.map (MvPolynomial.eval x) ^ r).rank =
          (A.map (MvPolynomial.eval x0) ^ r).rank := by
  classical
  have certificate (r : ℕ) : ∃ p : MvPolynomial σ K,
      MvPolynomial.eval x0 p = 1 ∧ ∀ x : σ → K,
        MvPolynomial.eval x p ≠ 0 →
          (A.map (MvPolynomial.eval x0) ^ r).rank ≤
            (A.map (MvPolynomial.eval x) ^ r).rank := by
    let M := A.map (MvPolynomial.eval x0) ^ r
    obtain ⟨V, U, e, _hV, _hU, hform⟩ := Matrix.exists_rank_normal_form M
    let j : Fin M.rank → ι := fun i => e.symm (Sum.inl i)
    let B : Matrix ι ι (MvPolynomial σ K) :=
      V.map MvPolynomial.C * A ^ r * U.map MvPolynomial.C
    have evaluate (x : σ → K) : B.map (MvPolynomial.eval x) =
        V * (A.map (MvPolynomial.eval x) ^ r) * U := by
      dsimp [B]
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_pow]
      have constant (T : Matrix ι ι K) :
          (T.map (MvPolynomial.C : K →+* MvPolynomial σ K)).map
            (MvPolynomial.eval x) = T := by
        ext i k
        simp
      rw [constant, constant]
    have determinant (x : σ → K) :
        MvPolynomial.eval x (B.submatrix j j).det =
          ((V * (A.map (MvPolynomial.eval x) ^ r) * U).submatrix j j).det := by
      rw [RingHom.map_det]
      change ((B.map (MvPolynomial.eval x)).submatrix j j).det = _
      rw [evaluate]
    refine ⟨(B.submatrix j j).det, ?_, ?_⟩
    · rw [determinant]
      change ((V * M * U).submatrix j j).det = 1
      rw [hform]
      have block : ((Matrix.fromBlocks 1 0 0 0).submatrix e e).submatrix j j =
          (1 : Matrix (Fin M.rank) (Fin M.rank) K) := by
        ext i k
        simp [Matrix.submatrix, j]
      rw [block, Matrix.det_one]
    · intro x hx
      rw [determinant] at hx
      have full := Matrix.rank_of_det_ne_zero hx
      have lower := Matrix.rank_submatrix_le
        (V * (A.map (MvPolynomial.eval x) ^ r) * U) j j
      rw [full, Fintype.card_fin] at lower
      exact lower.trans ((Matrix.rank_mul_le_left _ _).trans
        (Matrix.rank_mul_le_right _ _))
  choose p hp0 hp using certificate
  refine ⟨∏ r ∈ Finset.range H, p r, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun r _ => hp0 r
  · intro x hx r
    apply le_antisymm (hbound x r)
    by_cases hr : r < H
    · apply hp r x
      rw [map_prod] at hx
      exact (Finset.prod_ne_zero_iff.mp hx) r (Finset.mem_range.mpr hr)
    · have hz : A.map (MvPolynomial.eval x0) ^ r = 0 :=
        pow_eq_zero_of_le (Nat.le_of_not_gt hr) hnil
      rw [hz, Matrix.rank_zero]
      exact Nat.zero_le _

#print axioms exists_polynomial_power_rank_certificate

end D5.S3.Quantum.SpinChains.PolynomialPowerRanks
