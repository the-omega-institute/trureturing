/- GID: D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge
   generality: G
   mirror-B: D5/B/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge
   mirror-E: none(waiver:finite-weighted-homology)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none
   digest: Weighted harmonic chains represent the actual persistent real simplicial homology image. -/

import D5.S3.Geometry.PersistentLaplacianHeatStability
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Real ordered face chains, their weighted metrics and persistent harmonic representatives. -/

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped TensorProduct InnerProductSpace

namespace D5.S3.Geometry.SimplicialPersistence.WeightedPersistentHodge

open FiniteSimplicialSingularHomology

variable {V : Type} [Fintype V] [LinearOrder V]

/-- Strictly positive weights on every actual face, independently in every degree. -/
structure Weights (K : PreAbstractSimplicialComplex V) where
  value : ∀ q, Face K q → ℝ
  positive : ∀ q s, 0 < value q s

private def integerCoordinates (K : PreAbstractSimplicialComplex V) (q : ℕ) :
    orderedGroup K q ≃ₗ[ℤ] (Face K q → ℤ) :=
  LinearEquiv.ofBijective (PersistentLaplacianHeatStability.coordinates K q) (by
    classical
    exact (DirectSum.linearEquivFunOnFintype ℤ (Face K q) (fun _ => ℤ)).bijective.comp
      (ModuleCat.coprodIsoDirectSum (fun _ : Face K q => Z)).toLinearEquiv.bijective)

private def integerBasis (K : PreAbstractSimplicialComplex V) (q : ℕ) :
    Module.Basis (Face K q) ℤ (orderedGroup K q) :=
  Module.Basis.ofEquivFun (integerCoordinates K q)

/-- Scalar extension of the actual ordered integer face module, before taking homology. -/
def Chain (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :=
  ℝ ⊗[ℤ] orderedGroup K q

instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    AddCommGroup (Chain K w q) := inferInstanceAs (AddCommGroup (ℝ ⊗[ℤ] orderedGroup K q))
instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    Module ℝ (Chain K w q) := inferInstanceAs (Module ℝ (ℝ ⊗[ℤ] orderedGroup K q))

/-- Coefficients in the increasing-face basis after scalar extension. -/
def coefficients (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    Chain K w q ≃ₗ[ℝ] (Face K q → ℝ) :=
  ((integerBasis K q).baseChange ℝ).equivFun

private def orthonormalCoordinates (K : PreAbstractSimplicialComplex V) (w : Weights K)
    (q : ℕ) : Chain K w q ≃ₗ[ℝ] EuclideanSpace ℝ (Face K q) := by
  classical
  let scale : (Face K q → ℝ) ≃ₗ[ℝ] (Face K q → ℝ) :=
    LinearEquiv.piCongrRight fun s => LinearEquiv.smulOfNeZero ℝ ℝ
      (Real.sqrt (w.value q s))⁻¹ (inv_ne_zero (Real.sqrt_pos.2 (w.positive q s)).ne')
  exact ((coefficients K w q).trans scale).trans (WithLp.linearEquiv 2 ℝ _).symm

instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    NormedAddCommGroup (Chain K w q) :=
  NormedAddCommGroup.induced _ _ (orthonormalCoordinates K w q)
    (orthonormalCoordinates K w q).injective

instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    InnerProductSpace ℝ (Chain K w q) :=
  InnerProductSpace.induced (orthonormalCoordinates K w q)

instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    FiniteDimensional ℝ (Chain K w q) :=
  (coefficients K w q).finiteDimensional

/-- The ordinary signed boundary, extended on chains from integers to reals. -/
def boundary (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    Chain K w (q + 1) →ₗ[ℝ] Chain K w q :=
  (orderedBoundary K q).hom.baseChange ℝ

private theorem boundary_squared (K : PreAbstractSimplicialComplex V) (w : Weights K)
    (q : ℕ) : (boundary K w q).comp (boundary K w (q + 1)) = 0 := by
  rw [boundary, boundary, ← LinearMap.baseChange_comp]
  have h := congrArg ModuleCat.Hom.hom (orderedBoundary_squared K q)
  simpa using congrArg (LinearMap.baseChange ℝ) h

/-- The real ordered simplicial chain complex, with zero outgoing differential at zero. -/
def chainComplex (K : PreAbstractSimplicialComplex V) (w : Weights K) :
    ChainComplex (ModuleCat ℝ) ℕ :=
  ChainComplex.of (fun q => ModuleCat.of ℝ (Chain K w q))
    (fun q => ModuleCat.ofHom (boundary K w q))
    (fun q => ModuleCat.hom_ext (boundary_squared K w q))

end D5.S3.Geometry.SimplicialPersistence.WeightedPersistentHodge
