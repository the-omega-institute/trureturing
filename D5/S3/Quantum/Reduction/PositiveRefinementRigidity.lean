/- GID: D5/S3/Quantum/Reduction/PositiveRefinementRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/PositiveRefinementRigidity
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Positive maps dominated by identity have scalar action on every projection. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basis

/-!
# Positive domination and projection rigidity

The map is only complex linear and positive; no Kraus representation or
complete positivity is assumed. The Loewner upper bound is imposed on all
positive semidefinite inputs. The support argument includes zero projections.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Reduction.PositiveRefinementRigidity
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem projection_action
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (hdom : ∀ X, X.PosSemidef → Φ X ≤ X)
    (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) :
    Φ 1 * P = Φ P ∧ P * Φ 1 = Φ P := by
  have hp : P.PosSemidef := by
    have h := posSemidef_conjTranspose_mul_self P
    simpa only [hP, hPP] using h
  have hproj : IsStarProjection P := ⟨hPP, hP⟩
  have hq : (1 - P).PosSemidef := hproj.one_sub.nonneg.posSemidef
  obtain ⟨hright, hleft⟩ := hproj.mul_right_and_mul_left_of_nonneg_of_le
    (hpos P hp).nonneg (hdom P hp)
  obtain ⟨hqr, hql⟩ := hproj.one_sub.mul_right_and_mul_left_of_nonneg_of_le
    (hpos (1 - P) hq).nonneg (hdom (1 - P) hq)
  have hzeroR : Φ (1 - P) * P = 0 := by
    have := hqr
    rw [mul_sub, mul_one] at this
    exact sub_eq_self.mp this
  have hzeroL : P * Φ (1 - P) = 0 := by
    have := hql
    rw [sub_mul, one_mul] at this
    exact sub_eq_self.mp this
  have hsum : Φ 1 = Φ P + Φ (1 - P) := by rw [← map_add]; congr 1; abel
  rw [hsum, add_mul, mul_add, hright, hleft, hzeroR, hzeroL]
  simp

/-- Positivity-only domination forces the image of the identity to be scalar,
and gives that same scalar on every Hermitian projection. -/
theorem identity_dominated_projection_scalar
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (hdom : ∀ X, X.PosSemidef → Φ X ≤ X) (i₀ : n) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ Φ 1 = (c : ℂ) • (1 : Matrix n n ℂ) ∧
      ∀ P : Matrix n n ℂ, Pᴴ = P → P * P = P → Φ P = (c : ℂ) • P := by
  have hc (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) :
      Φ 1 * P = P * Φ 1 := by
    obtain ⟨hr, hl⟩ := projection_action Φ hpos hdom P hP hPP
    exact hr.trans hl.symm
  have hoff (i j : n) (hij : i ≠ j) : Φ 1 i j = 0 := by
    have h := congrArg (fun M : Matrix n n ℂ => M i j)
      (hc (single j j 1) (by simp) (by simp))
    simpa [Matrix.mul_apply, Matrix.single, hij, eq_comm] using h
  have hd : Φ 1 = diagonal (fun i => Φ 1 i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, hoff i j hij]
  have heq (i j : n) : Φ 1 i i = Φ 1 j j := by
    by_cases hij : i = j
    · subst j; rfl
    let v : n → ℂ := Pi.single i 1 + Pi.single j 1
    let Q : Matrix n n ℂ := (1 / 2 : ℂ) • vecMulVec v (star v)
    have hv : star v ⬝ᵥ v = 2 := by
      norm_num [v, dotProduct_add, add_dotProduct, hij, Ne.symm hij]
    have hQ : Qᴴ = Q := by simp [Q]
    have hQQ : Q * Q = Q := by
      simp only [Q, smul_mul_assoc, mul_smul_comm, vecMulVec_mul_vecMulVec, hv,
        smul_smul]
      norm_num [smul_smul]
    have h := congrArg (fun M : Matrix n n ℂ => M i j) (hc Q hQ hQQ)
    rw [hd] at h
    simp [Q, v, hij, Ne.symm hij, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.vecMulVec_apply] at h
    linear_combination 2 * h
  have hOne := hpos 1 PosSemidef.one
  have hnonneg := hOne.diag_nonneg (i := i₀)
  have hupper := (Matrix.le_iff.mp (hdom 1 PosSemidef.one)).diag_nonneg (i := i₀)
  let c : ℝ := (Φ 1 i₀ i₀).re
  have hreal : Φ 1 i₀ i₀ = (c : ℂ) := by
    apply Complex.ext <;> simp [c, hnonneg.2.symm]
  have hscalar : Φ 1 = (c : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa using (heq i i₀).trans hreal
    · simp [hij, hoff i j hij]
  refine ⟨c, hnonneg.1, ?_, hscalar, ?_⟩
  · simpa [c] using hupper.1
  · intro P hP hPP
    have h := (projection_action Φ hpos hdom P hP hPP).1.symm
    simpa [hscalar] using h

#print axioms identity_dominated_projection_scalar
end D5.S3.Quantum.Reduction.PositiveRefinementRigidity
