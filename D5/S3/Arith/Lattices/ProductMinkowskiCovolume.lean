/- GID: D5/S3/Arith/Lattices/ProductMinkowskiCovolume
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/ProductMinkowskiCovolume
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite product fundamental domains give the Minkowski discriminant covolume. -/

import D5.S3.Arith.Lattices.RestrictedScalarFreeMinkowskiLattice
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
Finite products of arbitrary real bases have Cartesian-product fundamental
domains and product volumes. Specializing to the existing coordinatewise
Minkowski lattice gives its discriminant covolume for every finite power,
including the zero-dimensional power. This supplies the paper's quantitative
arithmetic client of the range-to-span and fundamental-domain declarations.

The pinned library provides the one-copy discriminant formula and the product
measure formula. Its `fundamentalDomain_pi_basisFun` concerns only standard
real-coordinate bases; the dependent-family factorization below is new here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Module MeasureTheory

namespace D5.S3.Arith.Lattices.ProductMinkowskiCovolume

/-- The fundamental domain of a finite dependent Pi basis factors coordinatewise.
No finiteness assumption on the component basis indices is needed. -/
theorem fundamentalDomain_pi
    {I : Type*} {ι E : I → Type*} [Fintype I]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (b : ∀ i, Basis (ι i) ℝ (E i)) :
    ZSpan.fundamentalDomain (Pi.basis b) =
      Set.univ.pi (fun i => ZSpan.fundamentalDomain (b i)) := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, Pi.basis_repr, Set.mem_pi,
    Set.mem_univ, forall_const, Sigma.forall]

/-- With the canonical Pi measure, the volume is the product of the component
volumes, for arbitrary sigma-finite component measures. -/
theorem volume_fundamentalDomain_pi
    {I : Type*} {ι E : I → Type*} [Fintype I]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))]
    (b : ∀ i, Basis (ι i) ℝ (E i)) :
    volume (ZSpan.fundamentalDomain (Pi.basis b)) =
      ∏ i, volume (ZSpan.fundamentalDomain (b i)) := by
  rw [fundamentalDomain_pi, volume_pi_pi]

open RestrictedScalarFreeMinkowskiLattice

open scoped Classical in
/-- The covolume of the existing finite-power integral Minkowski lattice is the
power of the discriminant covolume, with the standard product volume. -/
theorem restrictedMinkowskiLattice_covolume
    (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    ZLattice.covolume (restrictedMinkowskiLattice K r) volume =
      ((2 : ℝ)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K : ℝ)|) ^ r := by
  let : BorelSpace (Fin r → NumberField.mixedEmbedding.mixedSpace K) := inferInstance
  let : MeasurableAdd (NumberField.mixedEmbedding.mixedSpace K) := inferInstance
  let : (volume : Measure (Fin r → NumberField.mixedEmbedding.mixedSpace K)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (restrictedMinkowskiLattice K r)
    (volume : Measure (Fin r → NumberField.mixedEmbedding.mixedSpace K))
    (restrictedMinkowskiLattice_fundamentalDomain K r), measureReal_def,
    restrictedMinkowskiBasis, volume_fundamentalDomain_pi]
  simp only [NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]

end D5.S3.Arith.Lattices.ProductMinkowskiCovolume
