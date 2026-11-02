/- GID: D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.claim; result=D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.result; claim=D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.claim
   digest: Three orthogonal pure states exclude every labelling of the product ansatz. -/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Korzekwa, Czachórski, Puchała and Życzkowski, arXiv:1812.09083v3,
Equation (30). Classical versions are the real diagonals in the preferred basis;
perfect distinguishability is pairwise orthogonality of density-matrix supports. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation

/-- The centre of the face missing the coordinate `k`. -/
def faceCentre (k : Fin 4) : Fin 4 → ℝ := fun j => if j = k then 0 else 1 / 3

/-- The source's three-distinguishability region, with classical version `diag ρ`. -/
def InRegion (p : Fin 4 → ℝ) : Prop :=
  p ∈ stdSimplex ℝ (Fin 4) ∧
    ∃ ρ : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ i, (ρ i).PosSemidef ∧ Matrix.trace (ρ i) = 1) ∧
      (∀ i j, i ≠ j → ρ i * ρ j = 0) ∧
      ∀ i k, (Matrix.diag (ρ i) k).re = p k

/-- The product ansatz with two independent parameters in the unit interval. -/
def ProductForm (f : Fin 4 → Fin 4 → ℝ) (p : Fin 4 → ℝ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧
    p = (a * b) • f 0 + (a * (1 - b)) • f 1 +
      ((1 - a) * b) • f 2 + ((1 - a) * (1 - b)) • f 3

/-- Equation (30), allowing any labelling of the four face centres. -/
def claim : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), ∀ p, InRegion p →
    ProductForm (fun i => faceCentre (σ i)) p

private def point : Fin 4 → ℝ :=
  ![(5 - Real.sqrt 5) / 10, (5 - Real.sqrt 5) / 20,
    (5 - Real.sqrt 5) / 10, (Real.sqrt 5 - 1) / 4]

private def ζ : ℂ := Complex.exp ((Real.pi / 5 : ℝ) * Complex.I)

private def phases : Fin 3 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, ζ ^ 2, ζ ^ 4, ζ ^ 7], ![-1, ζ ^ 9, ζ ^ 3, ζ ^ 9]]

private def state (i : Fin 3) (k : Fin 4) : ℂ :=
  (Real.sqrt (point k) : ℂ) * phases i k

private def density (i : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.vecMulVec (state i) (star (state i))

private lemma radical_bounds : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 9 / 4 := by
  sorry

private lemma point_simplex : point ∈ stdSimplex ℝ (Fin 4) := by
  sorry

private lemma phase_unit : conj ζ * ζ = 1 := by
  sorry

private lemma phase_fifth : ζ ^ 5 = -1 := by
  sorry

private lemma phase_quadratic : ζ ^ 2 = ((1 + Real.sqrt 5 : ℝ) / 2 : ℂ) * ζ - 1 := by
  sorry

private lemma phases_unit (i : Fin 3) (k : Fin 4) :
    conj (phases i k) * phases i k = 1 := by
  sorry

private lemma weighted_orthogonality (i j : Fin 3) (h : i ≠ j) :
    ∑ k, (point k : ℂ) * (conj (phases i k) * phases j k) = 0 := by
  sorry

private lemma state_diagonal (i : Fin 3) (k : Fin 4) :
    state i k * conj (state i k) = (point k : ℂ) := by
  sorry

private lemma state_orthogonality (i j : Fin 3) (h : i ≠ j) :
    star (state i) ⬝ᵥ state j = 0 := by
  sorry

private lemma density_region : InRegion point := by
  sorry

private lemma product_pairing (σ : Equiv.Perm (Fin 4)) (p : Fin 4 → ℝ)
    (h : ProductForm (fun i => faceCentre (σ i)) p) :
    (1 - 3 * p (σ 0)) * (1 - 3 * p (σ 3)) =
      (1 - 3 * p (σ 1)) * (1 - 3 * p (σ 2)) := by
  sorry

private lemma permutation_pairing (σ : Equiv.Perm (Fin 4)) (q : Fin 4 → ℝ)
    (h : q (σ 0) * q (σ 3) = q (σ 1) * q (σ 2)) :
    q 0 * q 1 = q 2 * q 3 ∨ q 0 * q 2 = q 1 * q 3 ∨
      q 0 * q 3 = q 1 * q 2 := by
  sorry

private lemma point_pairings :
    let q := fun k => 1 - 3 * point k
    q 0 * q 1 ≠ q 2 * q 3 ∧ q 0 * q 2 ≠ q 1 * q 3 ∧
      q 0 * q 3 ≠ q 1 * q 2 := by
  sorry

private lemma point_not_product (σ : Equiv.Perm (Fin 4)) :
    ¬ ProductForm (fun i => faceCentre (σ i)) point := by
  intro h
  rcases permutation_pairing σ (fun k => 1 - 3 * point k) (product_pairing σ point h)
    with h | h | h
  · exact point_pairings.1 h
  · exact point_pairings.2.1 h
  · exact point_pairings.2.2 h

/-- No labelling makes the product ansatz contain the three-distinguishability region. -/
theorem result : ¬ claim := by
  rintro ⟨σ, h⟩
  exact point_not_product σ (h point density_region)

end D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation
