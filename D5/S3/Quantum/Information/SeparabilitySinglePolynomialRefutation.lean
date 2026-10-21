/- GID: D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.claim; result=D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.result; claim=D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.claim
   digest: No single polynomial inequality characterizes all bipartite separable states. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped ComplexOrder Kronecker
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (partialTranspose)

namespace D5.S3.Quantum.Information.SeparabilitySinglePolynomialRefutation

noncomputable section

/-- A density operator is positive semidefinite with trace one. -/
def IsDensity {m n : ℕ} (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Real and imaginary coordinates of the matrix entries. -/
def coords {m n : ℕ} (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (Fin m × Fin n) × (Fin m × Fin n) × Bool → ℝ :=
  fun (p, q, b) => if b then (ρ p q).im else (ρ p q).re

/-- Polynomial invariance under arbitrary local unitary conjugations. -/
def IsInvariant {m n : ℕ}
    (f : MvPolynomial ((Fin m × Fin n) × (Fin m × Fin n) × Bool) ℝ) : Prop :=
  ∀ (UA : unitaryGroup (Fin m) ℂ) (UB : unitaryGroup (Fin n) ℂ)
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    MvPolynomial.eval (coords
      (((UA : Matrix _ _ ℂ) ⊗ₖ (UB : Matrix _ _ ℂ)) * ρ *
        ((UA : Matrix _ _ ℂ) ⊗ₖ (UB : Matrix _ _ ℂ))ᴴ)) f =
      MvPolynomial.eval (coords ρ) f

/-- The dimension-dependent single-inequality separability question of Krüger and Werner. -/
def claim : Prop :=
  ∀ m n : ℕ, 2 ≤ m → 2 ≤ n →
    ∃ f : MvPolynomial ((Fin m × Fin n) × (Fin m × Fin n) × Bool) ℝ,
      IsInvariant f ∧ ∀ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
        IsDensity ρ → (0 ≤ MvPolynomial.eval (coords ρ) f ↔ separableCone ρ)

private def rho (x y : ℝ) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  fun p q =>
    if p = q then
      if p = (0, 0) ∨ p = (1, 1) then ((1 / 8 + 3 * x / 40 - y / 40 : ℝ) : ℂ)
      else if p = (0, 1) ∨ p = (1, 2) then ((1 / 8 - x / 40 + 3 * y / 40 : ℝ) : ℂ)
      else ((1 / 4 - x / 20 - y / 20 : ℝ) : ℂ)
    else if (p = (0, 1) ∧ q = (1, 0)) ∨ (p = (1, 0) ∧ q = (0, 1)) then
      ((-1 / 8 + x / 8 + y / 40 : ℝ) : ℂ)
    else if (p = (0, 2) ∧ q = (1, 1)) ∨ (p = (1, 1) ∧ q = (0, 2)) then
      ((-1 / 8 + x / 40 + y / 8 : ℝ) : ℂ)
    else 0

private def positiveCoefficients (x y : ℝ) : Fin 8 → ℝ :=
  ![(5 + 3 * x - y) / 40, (5 - x + 3 * y) / 40,
    (5 - 5 * x - y) / 240, (5 - x - 5 * y) / 240,
    (5 + 7 * x + 11 * y) / 120, (5 + 11 * x + 7 * y) / 120,
    (5 + 11 * x - y) / 80, (5 - x + 11 * y) / 80]

private def positiveVectors : Fin 8 → (Fin 2 × Fin 3 → ℂ) :=
  ![Pi.single (0, 0) 1, Pi.single (1, 2) 1,
    2 • Pi.single (0, 1) 1 - 3 • Pi.single (1, 0) 1,
    2 • Pi.single (1, 1) 1 - 3 • Pi.single (0, 2) 1,
    Pi.single (0, 1) 1, Pi.single (1, 1) 1,
    Pi.single (1, 0) 1, Pi.single (0, 2) 1]

private lemma rho_trace (x y : ℝ) : (rho x y).trace = 1 := by
  sorry

private lemma rho_positive_decomposition (x y : ℝ) :
    rho x y = ∑ i : Fin 8, positiveCoefficients x y i •
      vecMulVec (positiveVectors i) (star (positiveVectors i)) := by
  sorry

private lemma rho_posSemidef {x y : ℝ} (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    (rho x y).PosSemidef := by
  sorry

private lemma rho_density {x y : ℝ} (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    IsDensity (rho x y) := by
  sorry

private lemma rho_affine (x y : ℝ) :
    rho x y = (1 - x - y) • rho 0 0 + x • rho 1 0 + y • rho 0 1 := by
  sorry

private lemma base_zero_separable : separableCone (rho 0 0) := by
  sorry

private lemma base_one_separable : separableCone (rho 1 0) := by
  sorry

private lemma base_two_separable : separableCone (rho 0 1) := by
  sorry

private lemma rho_separable {x y : ℝ} (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) : separableCone (rho x y) := by
  sorry

private lemma partialTranspose_quadratic_x (x y : ℝ) :
    (star (Pi.single (0, 0) 1 + Pi.single (1, 1) 1) ⬝ᵥ
      (partialTranspose (rho x y)) *ᵥ (Pi.single (0, 0) 1 + Pi.single (1, 1) 1)).re =
      2 * x / 5 := by
  sorry

private lemma partialTranspose_quadratic_y (x y : ℝ) :
    (star (Pi.single (0, 1) 1 + Pi.single (1, 2) 1) ⬝ᵥ
      (partialTranspose (rho x y)) *ᵥ (Pi.single (0, 1) 1 + Pi.single (1, 2) 1)).re =
      2 * y / 5 := by
  sorry

private lemma rho_entangled {x y : ℝ} (h : x < 0 ∨ y < 0) :
    ¬ separableCone (rho x y) := by
  sorry

private def restriction
    (f : MvPolynomial ((Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Bool) ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (coords (rho 0 0) i) +
      Polynomial.X * Polynomial.C (coords (rho 0 1) i - coords (rho 0 0) i)) f

private lemma restriction_eval
    (f : MvPolynomial ((Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Bool) ℝ) (y : ℝ) :
    Polynomial.eval y (restriction f) = MvPolynomial.eval (coords (rho 0 y)) f := by
  sorry

private lemma evaluation_continuous
    (f : MvPolynomial ((Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Bool) ℝ) (y : ℝ) :
    Continuous (fun x : ℝ => MvPolynomial.eval (coords (rho x y)) f) := by
  sorry

private lemma boundary_zero
    (f : MvPolynomial ((Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Bool) ℝ)
    (hf : ∀ ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ,
      IsDensity ρ → (0 ≤ MvPolynomial.eval (coords ρ) f ↔ separableCone ρ))
    {y : ℝ} (hy : 0 < y) (hy' : y < 1 / 4) :
    Polynomial.eval y (restriction f) = 0 := by
  sorry

/-- Qubit–qutrit states refute the dimension-dependent single-polynomial criterion. -/
theorem result : ¬ claim := by
  sorry

end D5.S3.Quantum.Information.SeparabilitySinglePolynomialRefutation
