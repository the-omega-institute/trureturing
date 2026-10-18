/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/Spectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/Spectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean.
Changes: module imports relocated; comment formatting, placement and blank lines adapted for the canonical weighted-graph consumer.
Matteo Cipollina. Changes: unused declarations and branches removed; retained live proof steps preserved; unused local proof terms removed. -/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.SimpleRing.Principal
namespace Matrix
open LinearMap Polynomial Module
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n] in
lemma stdSimplex_nonempty [Nonempty n] : (stdSimplex ℝ n).Nonempty :=
  ⟨(Fintype.card n : ℝ)⁻¹ • 1, by simp [stdSimplex, Finset.sum_const, nsmul_eq_mul]⟩
open Module
open LinearMap
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
lemma Module.End.exists_eigenvector_of_mem_spectrum {K V : Type*}
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {f : V →ₗ[K] V} {μ : K} (h_is_eigenvalue : μ ∈ spectrum K f) :
  ∃ v, v ≠ 0 ∧ f v = μ • v := by
  rw [spectrum.mem_iff, LinearMap.isUnit_iff_ker_eq_bot] at h_is_eigenvalue
  obtain ⟨v, hv_mem, hv_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_is_eigenvalue
  use v, hv_ne_zero
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply] at hv_mem
  exact (sub_eq_zero.mp hv_mem).symm
theorem spectrum.Matrix_toLin'_eq_spectrum {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    spectrum R (Matrix.toLin' A) = spectrum R A := by
  exact AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (Pi.basisFun R n)) A
end Matrix
