/- GID: D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge
   generality: G
   mirror-B: D5/B/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge
   mirror-E: none(waiver:finite-weighted-homology)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none
   digest: Weighted harmonic simplicial chains represent the actual persistent homology image. -/

module

public import D5.S3.Geometry.PersistentLaplacianHeatStability
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Analysis.InnerProductSpace.ProdL2
public import D5.S3.Geometry.SimplicialPersistence.HomologyImage

/-! Real ordered face chains, their weighted metrics and persistent harmonic representatives. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

public noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped TensorProduct InnerProductSpace

namespace D5.S3.Geometry.SimplicialPersistence.WeightedPersistentHodge

open FiniteSimplicialSingularHomology

variable {V : Type} [Fintype V] [LinearOrder V]

/-- Strictly positive weights on every actual face, independently in every degree. -/
structure Weights (K : PreAbstractSimplicialComplex V) where
  value : ∀ q, Face K q → ℝ
  positive : ∀ q s, 0 < value q s

/-- The same increasing face regarded as a face of the larger complex. -/
def faceInclusion {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (q : ℕ)
    (s : Face K q) : Face L q := ⟨s.val, h s.property.1, s.property.2⟩

/-- The metric on the smaller complex is the restriction of the larger weights. -/
def Weights.restrict {K L : PreAbstractSimplicialComplex V} (w : Weights L) (h : K ≤ L) :
    Weights K where
  value q s := w.value q (faceInclusion h q s)
  positive q s := w.positive q (faceInclusion h q s)

private def integerInclusion {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (q : ℕ) :
    orderedGroup K q ⟶ orderedGroup L q :=
  Sigma.desc fun s => faceι L (faceInclusion h q s)

private def integerRetraction {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (q : ℕ) :
    orderedGroup L q ⟶ orderedGroup K q := by
  classical
  exact Sigma.desc fun s => if hs : s.val ∈ K then
    faceι K ⟨s.val, hs, s.property.2⟩ else 0

private theorem integerInclusion_retraction {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (q : ℕ) : integerInclusion h q ≫ integerRetraction h q = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro s
  simp [integerInclusion, integerRetraction, faceι, faceInclusion]

private theorem integerInclusion_boundary {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (q : ℕ) :
    integerInclusion h (q + 1) ≫ orderedBoundary L q =
      orderedBoundary K q ≫ integerInclusion h q := by
  apply Sigma.hom_ext
  intro s
  simp only [integerInclusion, faceι, Sigma.ι_comp_desc_assoc, orderedBoundary,
    Sigma.ι_comp_desc, Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro v hv
  rfl

@[expose] def integerCoordinates (K : PreAbstractSimplicialComplex V) (q : ℕ) :
    orderedGroup K q ≃ₗ[ℤ] (Face K q → ℤ) :=
  LinearEquiv.ofBijective (PersistentLaplacianHeatStability.coordinates K q) (by
    classical
    exact (DirectSum.linearEquivFunOnFintype ℤ (Face K q) (fun _ => ℤ)).bijective.comp
      (ModuleCat.coprodIsoDirectSum (fun _ : Face K q => Z)).toLinearEquiv.bijective)

@[expose] def integerBasis (K : PreAbstractSimplicialComplex V) (q : ℕ) :
    Module.Basis (Face K q) ℤ (orderedGroup K q) :=
  Module.Basis.ofEquivFun (integerCoordinates K q)

/-- Scalar extension on chains, with the exact positive-weight metric. -/
@[expose] def Chain (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :=
  HomologyImage.WeightedModule (integerBasis K q) (w.value q) (w.positive q)

instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    AddCommGroup (Chain K w q) := inferInstanceAs (AddCommGroup
      (HomologyImage.WeightedModule (integerBasis K q) (w.value q) (w.positive q)))
instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    Module ℝ (Chain K w q) := inferInstanceAs (Module ℝ
      (HomologyImage.WeightedModule (integerBasis K q) (w.value q) (w.positive q)))
instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    NormedAddCommGroup (Chain K w q) := inferInstanceAs (NormedAddCommGroup
      (HomologyImage.WeightedModule (integerBasis K q) (w.value q) (w.positive q)))
instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    InnerProductSpace ℝ (Chain K w q) := inferInstanceAs (InnerProductSpace ℝ
      (HomologyImage.WeightedModule (integerBasis K q) (w.value q) (w.positive q)))
instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    FiniteDimensional ℝ (Chain K w q) := inferInstanceAs (FiniteDimensional ℝ
      (HomologyImage.WeightedModule (integerBasis K q) (w.value q) (w.positive q)))

/-- The coefficients identify chains with all real functions on actual faces. -/
@[expose] def coefficients (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    Chain K w q ≃ₗ[ℝ] (Face K q → ℝ) :=
  HomologyImage.weightedCoefficients (integerBasis K q) (w.value q) (w.positive q)

/-- The ordinary signed boundary, extended on chains from integers to reals. -/
def boundary (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    Chain K w (q + 1) →ₗ[ℝ] Chain K w q :=
  (orderedBoundary K q).hom.baseChange ℝ

private theorem boundary_squared (K : PreAbstractSimplicialComplex V) (w : Weights K)
    (q : ℕ) : (boundary K w q).comp (boundary K w (q + 1)) = 0 := by
  rw [boundary, boundary, ← LinearMap.baseChange_comp]
  have h := congrArg ModuleCat.Hom.hom (orderedBoundary_squared K q)
  simpa using congrArg (LinearMap.baseChange ℝ) h

/-- The real ordered simplicial chain complex, before taking its actual homology. -/
def chainComplex (K : PreAbstractSimplicialComplex V) (w : Weights K) :
    ChainComplex (ModuleCat ℝ) ℕ :=
  HomologyImage.realComplex (boundary K w) (boundary_squared K w)

/-- Zero extension of actual chains; this is scalar extension of face inclusion. -/
def inclusion {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (w : Weights L) (q : ℕ) :
    Chain K (w.restrict h) q →ₗ[ℝ] Chain L w q :=
  (integerInclusion h q).hom.baseChange ℝ

private theorem inclusion_injective {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) : Function.Injective (inclusion h w q) := by
  have hsplit := congrArg (fun f => f.hom.baseChange ℝ) (integerInclusion_retraction h q)
  have hleft : ((integerRetraction h q).hom.baseChange ℝ).comp (inclusion h w q) =
      LinearMap.id := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.baseChange_comp,
      LinearMap.baseChange_id] using hsplit
  exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun hleft x)

private theorem inclusion_boundary {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) :
    (boundary L w q).comp (inclusion h w (q + 1)) =
      (inclusion h w q).comp (boundary K (w.restrict h) q) := by
  simpa only [boundary, inclusion, ModuleCat.hom_comp, LinearMap.baseChange_comp] using
    congrArg (fun f => f.hom.baseChange ℝ) (integerInclusion_boundary h q)

/-- A genuine map of full real ordered simplicial chain complexes. -/
def chainInclusion {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (w : Weights L) :
    chainComplex K (w.restrict h) ⟶ chainComplex L w :=
  HomologyImage.realChainMap (boundary K (w.restrict h)) (boundary_squared K (w.restrict h))
    (boundary L w) (boundary_squared L w) (inclusion h w) (inclusion_boundary h w)

/-- The persistent operator uses the full inverse image of the included chain space. -/
def persistentLaplacian {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) :
    Chain K (w.restrict h) q →ₗ[ℝ] Chain K (w.restrict h) q :=
  HomologyImage.naturalLaplacian (boundary K (w.restrict h))
    (boundary_squared K (w.restrict h)) (boundary L w) (boundary_squared L w)
    (inclusion h w) (inclusion_boundary h w) (inclusion_injective h w) q

/-- The canonical harmonic representative equivalence for an actual finite simplicial pair. -/
def persistentHodgeEquiv {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) :
    (persistentLaplacian h w q).ker ≃ₗ[ℝ]
      (HomologicalComplex.homologyMap (chainInclusion h w) q).hom.range :=
  HomologyImage.naturalHodgeEquiv (boundary K (w.restrict h))
    (boundary_squared K (w.restrict h)) (boundary L w) (boundary_squared L w)
    (inclusion h w) (inclusion_boundary h w) (inclusion_injective h w) q

/-- The full weighted theorem, including the coefficient metric, representative and dimension. -/
theorem weighted_persistent_hodge {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) :
    (∀ r (x y : Chain L w r), ⟪x, y⟫_ℝ =
      ∑ s, coefficients L w r x s * coefficients L w r y s / w.value r s) ∧
    (∀ r (x y : Chain K (w.restrict h) r), ⟪x, y⟫_ℝ =
      ∑ s, coefficients K (w.restrict h) r x s * coefficients K (w.restrict h) r y s /
        (w.restrict h).value r s) ∧
    (∀ x : (persistentLaplacian h w q).ker,
      (persistentHodgeEquiv h w q x).val =
        HomologyImage.includedClass (boundary K (w.restrict h))
          (by exact boundary_squared K (w.restrict h)) (boundary L w) (by exact boundary_squared L w)
          (inclusion h w) (by exact inclusion_boundary h w) q
          ⟨x.val, HomologyImage.naturalHodge_cycle (boundary K (w.restrict h))
            (by exact boundary_squared K (w.restrict h)) (boundary L w) (by exact boundary_squared L w)
            (inclusion h w) (by exact inclusion_boundary h w) (by exact inclusion_injective h w) q x⟩) ∧
    Module.finrank ℝ (persistentLaplacian h w q).ker =
      Module.finrank ℝ (HomologicalComplex.homologyMap (chainInclusion h w) q).hom.range := by
  refine ⟨?_, ?_, ?_, (persistentHodgeEquiv h w q).finrank_eq⟩
  · intro r x y
    exact HomologyImage.weighted_inner (integerBasis L r) (w.value r) (w.positive r) x y
  · intro r x y
    exact HomologyImage.weighted_inner (integerBasis K r) ((w.restrict h).value r)
      ((w.restrict h).positive r) x y
  · intro x
    exact HomologyImage.naturalHodgeEquiv_apply (boundary K (w.restrict h))
      (by exact boundary_squared K (w.restrict h)) (boundary L w) (by exact boundary_squared L w)
      (inclusion h w) (by exact inclusion_boundary h w) (by exact inclusion_injective h w) q x

end D5.S3.Geometry.SimplicialPersistence.WeightedPersistentHodge
