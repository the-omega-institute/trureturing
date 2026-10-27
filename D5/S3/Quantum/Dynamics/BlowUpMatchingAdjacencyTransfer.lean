/- GID: D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Perfect matchings in every clone set induce adjacency transfer at pi/2. -/

import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer

open Matrix Complex Finset
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
open scoped BigOperators Matrix.Norms.Operator

/-- The adjacency eigenvalue support at `v` is integral: every complex eigenvector for a real
 eigenvalue with a nonzero `v` coordinate has an integer eigenvalue. -/
def IntegralSupport {m : ℕ} (g : SimpleGraph (Fin m)) [DecidableRel g.Adj] (v : Fin m) :
    Prop :=
  ∀ (λ : ℝ) (x : Fin m → ℂ), g.adjMatrix ℂ *ᵥ x = (λ : ℂ) • x →
    x v ≠ 0 → ∃ z : ℤ, λ = z

/-- A perfect matching of clone indices is a fixed-point-free involutive permutation. -/
def IsPerfectMatching {n : ℕ} (ρ : Equiv.Perm (Fin n)) : Prop :=
  ρ * ρ = 1 ∧ ∀ j, ρ j ≠ j

/-- Adjacency of the blow-up with a matching in every clone set. Indices are `(vertex, clone)`;
`permMatrix` sends a basis vector to its inverse image, equal to its image for an involution. -/
def blowUpMatching {m : ℕ} (g : SimpleGraph (Fin m)) [DecidableRel g.Adj]
    (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.kroneckerMap (· * ·) (g.adjMatrix ℂ) (Matrix.of fun _ _ => 1) +
    Matrix.kroneckerMap (· * ·) 1 (ρ.permMatrix ℂ)

private theorem integral_phase (n : ℕ) (hn : 4 ∣ n) (z : ℤ) :
    Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I * n * z) = 1 := by
  sorry

private theorem base_periodic {m n : ℕ} (g : SimpleGraph (Fin m))
    [DecidableRel g.Adj] (v : Fin m) (hv : IntegralSupport g v) (hn : 4 ∣ n) :
    NormedSpace.exp (((((Real.pi / 2 : ℝ) : ℂ) * I) * n) • g.adjMatrix ℂ) *ᵥ
      Pi.single v 1 = Pi.single v 1 := by
  sorry

private theorem blowup_commute {m n : ℕ} (g : SimpleGraph (Fin m))
    [DecidableRel g.Adj] (ρ : Equiv.Perm (Fin n)) :
    Commute (Matrix.kroneckerMap (· * ·) (g.adjMatrix ℂ)
      (Matrix.of fun _ _ : Fin n => (1 : ℂ)))
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin m) (Fin m) ℂ) (ρ.permMatrix ℂ)) := by
  sorry

private theorem matching_exp {m n : ℕ} (ρ : Equiv.Perm (Fin n))
    (hρ : IsPerfectMatching ρ) :
    NormedSpace.exp ((((Real.pi / 2 : ℝ) : ℂ) * I) •
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin m) (Fin m) ℂ) (ρ.permMatrix ℂ)) =
      I • Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin m) (Fin m) ℂ)
        (ρ.permMatrix ℂ) := by
  sorry

private theorem blowup_exp_column {m n : ℕ} (a : Matrix (Fin m) (Fin m) ℂ)
    (c : ℂ) (hn : n ≠ 0) (v : Fin m) (k : Fin n) :
    NormedSpace.exp (c • Matrix.kroneckerMap (· * ·) a
      (Matrix.of fun _ _ : Fin n => (1 : ℂ))) *ᵥ Pi.single (v, k) 1 =
      Pi.single (v, k) 1 + fun p => (n : ℂ)⁻¹ *
        ((NormedSpace.exp ((c * n) • a) *ᵥ Pi.single v 1) p.1 -
          (Pi.single v (1 : ℂ)) p.1) := by
  sorry

private theorem matching_column {m n : ℕ} (ρ : Equiv.Perm (Fin n))
    (hρ : IsPerfectMatching ρ) (v : Fin m) (j : Fin n) :
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin m) (Fin m) ℂ)
      (ρ.permMatrix ℂ) *ᵥ Pi.single (v, j) 1 = Pi.single (v, ρ j) 1 := by
  sorry

private theorem transfer_column {m n : ℕ} (g : SimpleGraph (Fin m))
    [DecidableRel g.Adj] (v : Fin m) (ρ : Equiv.Perm (Fin n))
    (hv : IntegralSupport g v) (hn : 4 ∣ n) (hρ : IsPerfectMatching ρ) (j : Fin n) :
    NormedSpace.exp ((((Real.pi / 2 : ℝ) : ℂ) * I) • blowUpMatching g n ρ) *ᵥ
      Pi.single (v, j) 1 = I • Pi.single (v, ρ j) 1 := by
  have hn0 : n ≠ 0 := by have := j.isLt; omega
  have hfix : NormedSpace.exp ((((Real.pi / 2 : ℝ) : ℂ) * I) •
      Matrix.kroneckerMap (· * ·) (g.adjMatrix ℂ)
        (Matrix.of fun _ _ : Fin n => (1 : ℂ))) *ᵥ Pi.single (v, ρ j) 1 =
      Pi.single (v, ρ j) 1 := by
    rw [blowup_exp_column _ _ hn0, base_periodic g v hv hn]
    ext p
    simp
  unfold blowUpMatching
  rw [smul_add, Matrix.exp_add_of_commute _ _
    ((blowup_commute g ρ).smul_left _ |>.smul_right _), matching_exp ρ hρ,
    Matrix.mulVec_mulVec, Matrix.smul_mulVec, matching_column ρ hρ,
    Matrix.mulVec_smul, hfix]

/-- Integral adjacency support and a clone multiplicity divisible by four give adjacency
perfect state transfer across every inserted matching edge in the clone set of `v`. -/
theorem result (m n : ℕ) (g : SimpleGraph (Fin m)) [DecidableRel g.Adj]
    (v : Fin m) (ρ : Equiv.Perm (Fin n)) (hv : IntegralSupport g v)
    (hn : 4 ∣ n) (hρ : IsPerfectMatching ρ) (j : Fin n) :
    HasPST (blowUpMatching g n ρ) (Real.pi / 2) (v, j) (v, ρ j) := by
  have h := congrFun (transfer_column g v ρ hv hn hρ (ρ j)) (v, j)
  have hinv : ρ (ρ j) = j := congrArg (fun p : Equiv.Perm (Fin n) => p j) hρ.1
  rw [hinv] at h
  simp only [Matrix.mulVec_single_one, Pi.smul_apply, Pi.single_eq_same, mul_one] at h
  unfold HasPST
  rw [hamiltonianPropagator_neg, h]
  exact Complex.normSq_I

end D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer
