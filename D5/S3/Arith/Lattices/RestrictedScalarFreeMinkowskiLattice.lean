/- GID: D5/S3/Arith/Lattices/RestrictedScalarFreeMinkowskiLattice
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/RestrictedScalarFreeMinkowskiLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Free restriction of scalars has product rank and a conjugate Minkowski lattice. -/

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
Library-search and duplicate audit trail (2026-09-04):
* Literal and notation-variant D5 searches covered restriction/restrict scalars,
  projective and free modules, number-field degree, Minkowski embeddings,
  conjugate coordinates, and discrete/cocompact lattices. They found only the
  quadratic golden model-set lattice and unrelated scalar restrictions.
* The digestion index leaves the source atom residual-open with no coverage
  GID. Generalized body-shape searches for rank multiplication and full-rank
  lattice images found no D5 owner. The retired formalization-receipt directory
  was neither consulted nor recreated.
* The in-flight module and atom indexes contain no restricted-scalar,
  number-field-module, or general Minkowski-lattice owner. The proposed module
  path is absent from `origin/dev`, and its theorem names have no repository hit.
* Pinned Mathlib supplies `RingOfIntegers.rank`,
  `Module.finrank_pi_fintype`, `LinearMap.range_compLeft`,
  `NumberField.mixedEmbedding.span_latticeBasis`,
  `ZSpan.isAddFundamentalDomain`, and the existing `DiscreteTopology` and
  `IsZLattice` instances for the integer Minkowski lattice. These are reused.

The source states the result for every finite-rank projective `O_K`-module.
Pinned Mathlib packages the Minkowski lattice of `O_K` and fractional ideals,
but has no Steinitz decomposition identifying an arbitrary finite projective
module with a direct sum of ideals. Accordingly, this module proves the full
rank-and-lattice conclusion for the finite-free case `O_K^r`; it does not claim
the unavailable arbitrary-projective generalization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Module Set
open scoped Classical

namespace D5.S3.Arith.Lattices.RestrictedScalarFreeMinkowskiLattice

/-- The ring of integers embedded in the real/complex Minkowski space, viewed
as an integer-linear map. -/
def integerMinkowskiEmbedding (K : Type*) [Field K] [NumberField K] :
    NumberField.RingOfIntegers K →ₗ[ℤ]
      NumberField.mixedEmbedding.mixedSpace K :=
  ((NumberField.mixedEmbedding K).comp
    (algebraMap (NumberField.RingOfIntegers K) K)).toIntAlgHom.toLinearMap

/-- Apply every archimedean embedding to every coordinate of the free module
`O_K^r`. -/
def restrictedMinkowskiEmbedding (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    (Fin r → NumberField.RingOfIntegers K) →ₗ[ℤ]
      (Fin r → NumberField.mixedEmbedding.mixedSpace K) :=
  (integerMinkowskiEmbedding K).compLeft (Fin r)

/-- The product of Mathlib's integral Minkowski bases, one copy for each free
module coordinate. -/
def restrictedMinkowskiBasis (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    Basis (Σ _ : Fin r,
      Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) ℝ
      (Fin r → NumberField.mixedEmbedding.mixedSpace K) :=
  Pi.basis fun _ => NumberField.mixedEmbedding.latticeBasis K

/-- The image of `O_K^r` under all real and complex embeddings. -/
def restrictedMinkowskiLattice (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    Submodule ℤ (Fin r → NumberField.mixedEmbedding.mixedSpace K) :=
  LinearMap.range (restrictedMinkowskiEmbedding K r)

/-- The coordinatewise Minkowski image is exactly the integer span of the
product Minkowski basis. -/
theorem restrictedMinkowskiLattice_eq_span
    (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    restrictedMinkowskiLattice K r =
      Submodule.span ℤ (Set.range (restrictedMinkowskiBasis K r)) := by
  rw [restrictedMinkowskiLattice, restrictedMinkowskiEmbedding,
    LinearMap.range_compLeft]
  change
    Submodule.pi Set.univ
        (fun _ : Fin r => NumberField.mixedEmbedding.integerLattice K) =
      Submodule.span ℤ (Set.range (restrictedMinkowskiBasis K r))
  rw [← NumberField.mixedEmbedding.span_latticeBasis K]
  ext x
  constructor
  · intro hx
    apply ((restrictedMinkowskiBasis K r).mem_span_iff_repr_mem ℤ x).mpr
    rintro ⟨i, j⟩
    rw [restrictedMinkowskiBasis, Pi.basis_repr]
    exact ((NumberField.mixedEmbedding.latticeBasis K).mem_span_iff_repr_mem
      ℤ (x i)).mp (hx i (Set.mem_univ i)) j
  · intro hx i _
    apply ((NumberField.mixedEmbedding.latticeBasis K).mem_span_iff_repr_mem
      ℤ (x i)).mpr
    intro j
    have hCoordinate :=
      ((restrictedMinkowskiBasis K r).mem_span_iff_repr_mem ℤ x).mp hx ⟨i, j⟩
    simpa only [restrictedMinkowskiBasis, Pi.basis_repr] using hCoordinate

instance restrictedMinkowskiLattice_discrete
    (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    DiscreteTopology (restrictedMinkowskiLattice K r) := by
  rw [restrictedMinkowskiLattice_eq_span]
  infer_instance

instance restrictedMinkowskiLattice_isZLattice
    (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    IsZLattice ℝ (restrictedMinkowskiLattice K r) := by
  constructor
  rw [restrictedMinkowskiLattice_eq_span]
  exact ZSpan.span_top (restrictedMinkowskiBasis K r)

/-- A fundamental domain for the coordinatewise Minkowski lattice. -/
theorem restrictedMinkowskiLattice_fundamentalDomain
    (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    MeasureTheory.IsAddFundamentalDomain (restrictedMinkowskiLattice K r)
      (ZSpan.fundamentalDomain (restrictedMinkowskiBasis K r)) := by
  rw [restrictedMinkowskiLattice_eq_span]
  exact ZSpan.isAddFundamentalDomain (restrictedMinkowskiBasis K r) _

/-- Restriction of scalars from `O_K` to `Z` multiplies the free rank by the
degree of the number field. -/
theorem restrictedScalarFree_finrank
    (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    Module.finrank ℤ (Fin r → NumberField.RingOfIntegers K) =
      r * Module.finrank ℚ K := by
  rw [Module.finrank_pi_fintype]
  simp [NumberField.RingOfIntegers.rank]

/-- Finite-free restriction of scalars: a rank-`r` module over the integers of
a degree-`d` number field has integer rank `r*d`, and its full conjugate image
is a discrete full-rank lattice with the displayed fundamental domain. -/
theorem restricted_scalar_free_minkowski_completion
    (K : Type*) [Field K] [NumberField K] (r d : ℕ)
    (degree : Module.finrank ℚ K = d) :
    Module.finrank ℤ (Fin r → NumberField.RingOfIntegers K) = r * d ∧
      IsZLattice ℝ (restrictedMinkowskiLattice K r) ∧
      MeasureTheory.IsAddFundamentalDomain (restrictedMinkowskiLattice K r)
        (ZSpan.fundamentalDomain (restrictedMinkowskiBasis K r)) := by
  refine ⟨?_, inferInstance, restrictedMinkowskiLattice_fundamentalDomain K r⟩
  rw [restrictedScalarFree_finrank, degree]

#print axioms restrictedMinkowskiLattice_eq_span
#print axioms restrictedMinkowskiLattice_fundamentalDomain
#print axioms restrictedScalarFree_finrank
#print axioms restricted_scalar_free_minkowski_completion

end D5.S3.Arith.Lattices.RestrictedScalarFreeMinkowskiLattice
