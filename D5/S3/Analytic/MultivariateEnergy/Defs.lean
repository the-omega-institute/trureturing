/- GID: D5/S3/Analytic/MultivariateEnergy/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/MultivariateEnergy/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Constructions.HaarToSphere, mathlib/module/Mathlib.MeasureTheory.Integral.Pi, mathlib/module/Mathlib.LinearAlgebra.Matrix.Trace, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace, mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Normalized spherical measure, multivariate energy and centered matrix kernels. -/

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Matrix.Normed

/-! Spherical energy and the centered rank-one feature family. -/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Elementwise

namespace D5.S3.Analytic.MultivariateEnergy.Defs

/-- The unit sphere with its induced Borel measurable structure. -/
abbrev S (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

/-- Normalized surface measure, defined by radial disintegration of volume. -/
def sigma (d : ℕ) : Measure (S d) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere

instance sigma_isProbabilityMeasure (d : ℕ) [NeZero d] : IsProbabilityMeasure (sigma d) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  have hne : (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume)
  exact ⟨by rw [sigma, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel hne (measure_ne_top _ _)]⟩

/-- Orthogonal transformations acting on the sphere. -/
def sphereAction {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (x : S d) : S d :=
  ⟨V x, by simpa only [Metric.mem_sphere, dist_zero_right, V.norm_map] using x.property⟩

/-- Continuity, symmetry, and invariance under every orthogonal transformation. -/
def IsAdmissible {d n : ℕ} (K : (Fin n → S d) → ℝ) : Prop :=
  Continuous K ∧
  (∀ π : Equiv.Perm (Fin n), ∀ x, K (x ∘ π) = K x) ∧
  (∀ V : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
    ∀ x, K (fun i => sphereAction V (x i)) = K x)

/-- Product-measure energy of a multivariate kernel. -/
def energy {d n : ℕ} (K : (Fin n → S d) → ℝ) (μ : Measure (S d)) : ℝ :=
  ∫ x, K x ∂Measure.pi (fun _ : Fin n => μ)

/-- Minimization among all Borel probability measures. -/
def IsMinimizer {d n : ℕ} (K : (Fin n → S d) → ℝ) (μ₀ : Measure (S d)) : Prop :=
  ∀ μ : Measure (S d), IsProbabilityMeasure μ → energy K μ₀ ≤ energy K μ

/-- Integrate the first inputs, leaving the last two free. -/
def avgKernel {d m : ℕ} (K : (Fin (m + 2) → S d) → ℝ) (x y : S d) : ℝ :=
  ∫ z : Fin m → S d, K (Fin.append (m := m) (n := 2) z ![x, y])
    ∂Measure.pi (fun _ : Fin m => sigma d)

/-- The Jordan decomposition formulation of conditional positive definiteness:
any finite signed measure of mass zero is the difference of two finite positive
measures of equal mass. -/
def IsCondPosDef {d : ℕ} (U : S d → S d → ℝ) : Prop :=
  ∀ μ₁ μ₂ : Measure (S d), IsFiniteMeasure μ₁ → IsFiniteMeasure μ₂ →
    μ₁ Set.univ = μ₂ Set.univ →
    0 ≤ (∫ x, ∫ y, U x y ∂μ₁ ∂μ₁) -
      2 * (∫ x, ∫ y, U x y ∂μ₂ ∂μ₁) + (∫ x, ∫ y, U x y ∂μ₂ ∂μ₂)

/-- The averaged-kernel characterization on all dimensions and arities. -/
def claim : Prop :=
  ∀ d ≥ 2, ∀ m, ∀ K : (Fin (m + 3) → S d) → ℝ, IsAdmissible K →
    (IsMinimizer K (sigma d) ↔ IsCondPosDef (avgKernel (m := m + 1) K))

/-- Centered rank-one matrix feature. -/
def A {d : ℕ} (x : S d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (x : EuclideanSpace ℝ (Fin d)) i * (x : EuclideanSpace ℝ (Fin d)) j -
    if i = j then 1 / (d : ℝ) else 0

/-- Quadratic matrix feature pairing. -/
def L {d : ℕ} (x y : S d) : ℝ := Matrix.trace (A x * A y)

/-- Cubic matrix feature pairing. -/
def T {d : ℕ} (x y z : S d) : ℝ := Matrix.trace (A x * A y * A z)

/-- The averaged centered feature of a measure. -/
def Q {d : ℕ} (μ : Measure (S d)) : Matrix (Fin d) (Fin d) ℝ := ∫ x, A x ∂μ

/-- The symmetric pair and triple family, indexed by unordered subsets.
The increasing enumeration chooses one ordering for each subset. -/
def familyKernel (d m : ℕ) (β : ℝ) (x : Fin (m + 3) → S d) : ℝ :=
  β / ((m + 3).choose 2 : ℝ) *
    (∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
      L (x ((s.sort (· ≤ ·)).getD 0 0)) (x ((s.sort (· ≤ ·)).getD 1 0))) -
  1 / ((m + 3).choose 3 : ℝ) *
    (∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 3,
      T (x ((s.sort (· ≤ ·)).getD 0 0)) (x ((s.sort (· ≤ ·)).getD 1 0))
        (x ((s.sort (· ≤ ·)).getD 2 0)))

end D5.S3.Analytic.MultivariateEnergy.Defs
