/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean.
Changes: module imports relocated; comment formatting, placement and blank lines adapted for the canonical weighted-graph consumer.
Matteo Cipollina. Changes: unused declarations and branches removed; retained live proof steps preserved; unused local proof terms removed. -/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
open Quiver.Path
namespace Matrix
open CollatzWielandt
open Quiver
open Matrix Complex
open scoped ENNReal
variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
omit [Fintype n] [DecidableEq n] in
lemma normFun_complex_ne_zero_of_ne_zero {x : n → ℂ} (hx : x ≠ 0) : (fun i ↦ ‖x i‖) ≠ 0 := by
  contrapose! hx
  ext i
  exact norm_eq_zero.mp (congr_fun hx i)
variable [Nonempty n]
omit [DecidableEq n] [Nonempty n] in
theorem eigenvalue_abs_subinvariant
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x) :
    (‖μ‖ : ℝ) • (fun i => ‖x i‖) ≤ A *ᵥ (fun i => ‖x i‖) := by
  intro i
  calc
    (‖μ‖ : ℝ) * ‖x i‖ = ‖μ * x i‖ := by rw [← norm_mul]
    _ = ‖(μ • x) i‖ := by simp [Pi.smul_apply]
    _ = ‖((A.map (algebraMap ℝ ℂ)) *ᵥ x) i‖ := by rw [← hx_eig]
    _ = ‖∑ j, (A i j : ℂ) * x j‖ := by simp; rfl
    _ ≤ ∑ j, ‖(A i j : ℂ) * x j‖ := by apply norm_sum_le
    _ = ∑ j, A i j * ‖x j‖ := by
      simp only [Complex.norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hA_nonneg _ _)]
    _ = (A *ᵥ fun i => ‖x i‖) i := by simp [mulVec_apply_eq_sum]
lemma collatzWielandtFn_le_perronRoot
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    collatzWielandtFn A x ≤ perronRoot A := by
  apply le_csSup (CollatzWielandt.bddAbove A hA_nonneg)
  rw [Set.mem_image]
  exact ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
theorem eigenvalue_abs_le_perron_root
    {A : Matrix n n ℝ} (_ : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) :
    ‖μ‖ ≤ perronRoot A := by
  let B := A.map (algebraMap ℝ ℂ)
  have h_spec : μ ∈ spectrum ℂ (toLin' B) := by rwa [spectrum.Matrix_toLin'_eq_spectrum]
  rcases Module.End.exists_eigenvector_of_mem_spectrum h_spec with ⟨x, hx_ne_zero, hx_eig_lin⟩
  have hx_eig : B *ᵥ x = μ • x := by rwa [toLin'_apply] at hx_eig_lin
  let x_abs := fun i => ‖x i‖
  have hx_abs_nonneg : ∀ i, 0 ≤ x_abs i := fun i => norm_nonneg _
  have hx_abs_ne_zero : x_abs ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  have h_subinv : (‖μ‖ : ℝ) • x_abs ≤ A *ᵥ x_abs :=
    eigenvalue_abs_subinvariant hA_nonneg hx_eig
  have h_le_collatz : (‖μ‖ : ℝ) ≤ collatzWielandtFn A x_abs :=
    le_of_subinvariant hA_nonneg hx_abs_nonneg hx_abs_ne_zero h_subinv
  have h_le_perron : collatzWielandtFn A x_abs ≤ perronRoot A :=
    collatzWielandtFn_le_perronRoot hA_nonneg hx_abs_nonneg hx_abs_ne_zero
  exact le_trans h_le_collatz h_le_perron
lemma perron_root_eq_positive_eigenvalue (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃ r v, 0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v ∧ perronRoot A = r := by
  obtain ⟨r, v, hr_pos, hv_pos, h_eig⟩ := exists_positive_eigenvector_of_irreducible hA_irred
  have h_le : perronRoot A ≤ r :=
    eigenvalue_is_ub_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig
  have h_ge : r ≤ perronRoot A :=
    eigenvalue_le_perron_root_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig
  have h_eq : perronRoot A = r := le_antisymm h_le h_ge
  exact ⟨r, v, hr_pos, hv_pos, h_eig, h_eq⟩
lemma mem_spectrum_of_hasEigenvector {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : V →ₗ[K] V} {μ : K} {v : V} (h : Module.End.HasEigenvector f μ v) :
    μ ∈ spectrum K f := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector h
lemma mem_spectrum_of_eigenvalue
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n K} {μ : K} {v : n → K}
    (hv_ne_zero : v ≠ 0) (h_eig : A *ᵥ v = μ • v) :
    μ ∈ spectrum K A := by
  let f := toLin' A
  have h_eig_f : f v = μ • v := by
    simpa [toLin'_apply, f] using h_eig
  have h_has_eigvec : Module.End.HasEigenvector f μ v :=
    ⟨by
      rwa [← Module.End.mem_eigenspace_iff] at h_eig_f,
      hv_ne_zero⟩
  have h_mem_f : μ ∈ spectrum K f :=
    mem_spectrum_of_hasEigenvector h_has_eigvec
  simpa [f, spectrum.Matrix_toLin'_eq_spectrum] using h_mem_f
