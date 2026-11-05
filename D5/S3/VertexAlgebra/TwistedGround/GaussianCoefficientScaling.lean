/- GID: D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact diagonal congruence scaling of native Gaussian coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Diagonal coordinate substitution gives the exact scaling of ordinary Gaussian coefficients. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientScaling
open MvPolynomial FactorialFockQuadraticEstimate InfiniteGaussianFock
open FactorialFockMetric (Occupation weight)
universe u v

private def diagonalSubstitution {J : Type u} (w : J → ℂ) :
    MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial J ℂ :=
  eval₂AlgHom ℂ (fun i => w i • X i)

private theorem diagonalSubstitution_monomial {J : Type u} (w : J → ℂ)
    (d : Occupation J) (c : ℂ) :
    diagonalSubstitution w (monomial d c) =
      d.prod (fun i n => w i ^ n) • monomial d c := by
  classical
  simp only [diagonalSubstitution, coe_eval₂AlgHom, algebraMap_eq,
    eval₂_monomial, smul_pow, Finsupp.prod, Finset.prod_smul,
    prod_X_pow_eq_monomial]
  rw [mul_smul_comm, C_mul_monomial, mul_one]

private theorem coeff_diagonalSubstitution {J : Type u} (w : J → ℂ)
    (p : MvPolynomial J ℂ) (d : Occupation J) :
    (diagonalSubstitution w p).coeff d =
      d.prod (fun i n => w i ^ n) * p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [diagonalSubstitution_monomial, coeff_smul]
    by_cases h : a = d
    · subst a; simp
    · simp [coeff_monomial, h, Ne.symm h]
  | add p q hp hq => simp [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]

private theorem diagonalSubstitution_quadratic {J : Type u} [Fintype J]
    (w : J → ℂ) (K : Matrix J J ℂ) :
    diagonalSubstitution w (quadratic K) =
      quadratic (fun i j => w i * K i j * w j) := by
  simp only [quadratic, map_smul, map_sum, map_mul,
    diagonalSubstitution, eval₂AlgHom_X]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_mul_smul_comm, smul_smul]
  congr 1
  ring

/-- Ordinary native coefficients under arbitrary complex diagonal congruence.
Zero weights and odd occupations are included. -/
theorem finite_diagonal_congruence {J : Type u} [Fintype J] [DecidableEq J]
    (K : Matrix J J ℂ) (w : J → ℂ) (d : Occupation J) :
    gaussianCoefficient (fun i j => w i * K i j * w j) d =
      d.prod (fun i n => w i ^ n) * gaussianCoefficient K d := by
  unfold gaussianCoefficient
  rw [← coeff_diagonalSubstitution w]
  congr 1
  simp only [gaussianPiece, map_smul, map_pow, diagonalSubstitution_quadratic]

/-- The principal-support definition preserves diagonal scaling for arbitrary
mode types, with no summability or enumeration premise. -/
theorem diagonal_congruence {J : Type u} [DecidableEq J]
    (K : J → J → ℂ) (w : J → ℂ) (d : Occupation J) :
    coefficient (fun i j => w i * K i j * w j) d =
      d.prod (fun i n => w i ^ n) * coefficient K d := by
  rw [coefficient, finite_diagonal_congruence, coefficient]
  congr 1
  have h := Finsupp.prod_mapDomain_index_inj (M := ℕ) (N := ℂ)
    Subtype.val_injective (s := restrictOccupation d.support d)
    (h := fun i n => w i ^ n)
  rw [extend_restrict _ _ (fun _ h => h)] at h
  exact h.symm

/-- One factor per external occurrence, regardless of the internal occupation. -/
theorem external_scaling {X : Type u} {I : Type v}
    [DecidableEq X] [DecidableEq I] (K : (X ⊕ I) → (X ⊕ I) → ℂ)
    (t : ℂ) (d : Occupation X) (n : Occupation I) :
    coefficient (fun i j => (Sum.elim (fun _ : X => t) (fun _ : I => 1) i) *
      K i j * (Sum.elim (fun _ : X => t) (fun _ : I => 1) j)) (d.sumElim n) =
        t ^ d.degree * coefficient K (d.sumElim n) := by
  have hp : d.prod (fun _ k => t ^ k) = t ^ d.degree := by
    change (∏ i ∈ d.support, t ^ d i) = t ^ d.degree
    rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [diagonal_congruence, Finsupp.prod_sumElim]
  change (d.prod (fun _ k => t ^ k) * n.prod (fun _ k => (1 : ℂ) ^ k)) *
    coefficient K (d.sumElim n) = _
  rw [show n.prod (fun _ k => (1 : ℂ) ^ k) = 1 by simp, mul_one, hp]

end D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientScaling
