/- GID: D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge
   generality: G
   mirror-B: D5/B/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge
   mirror-E: none(waiver:finite-weighted-homology)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none
   digest: Weighted harmonic simplicial chains represent the actual persistent homology image. -/



import D5.S3.Geometry.PersistentLaplacianHeatStability
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Weighted simplicial chains and canonical representatives in the actual homology image. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory
open scoped InnerProductSpace TensorProduct

namespace D5.S3.Geometry.SimplicialPersistence.WeightedPersistentHodge

section WeightedMetric

variable {ι M : Type} [Fintype ι] [AddCommGroup M] [Module ℤ M]
  (basis : Module.Basis ι ℤ M) (weight : ι → ℝ) (positive : ∀ i, 0 < weight i)

/-- Real chains in a specified integer basis, with the reciprocal-weight metric. -/
def WeightedModule (_basis : Module.Basis ι ℤ M)
    (_weight : ι → ℝ) (_positive : ∀ i, 0 < _weight i) := ℝ ⊗[ℤ] M

instance : AddCommGroup (WeightedModule basis weight positive) :=
  inferInstanceAs (AddCommGroup (ℝ ⊗[ℤ] M))
instance : Module ℝ (WeightedModule basis weight positive) :=
  inferInstanceAs (Module ℝ (ℝ ⊗[ℤ] M))

/-- Ordinary face coefficients, before normalization by square roots of weights. -/
def weightedCoefficients :
    WeightedModule basis weight positive ≃ₗ[ℝ] (ι → ℝ) :=
  (basis.baseChange ℝ).equivFun

def weightedOrthonormalCoordinates :
    WeightedModule basis weight positive ≃ₗ[ℝ] EuclideanSpace ℝ ι := by
  classical
  let scale : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
    LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero ℝ ℝ
      (Real.sqrt (weight i))⁻¹ (inv_ne_zero (Real.sqrt_pos.2 (positive i)).ne')
  exact ((weightedCoefficients basis weight positive).trans scale).trans
    (WithLp.linearEquiv 2 ℝ _).symm

instance : NormedAddCommGroup (WeightedModule basis weight positive) :=
  NormedAddCommGroup.induced _ _ (weightedOrthonormalCoordinates basis weight positive)
    (weightedOrthonormalCoordinates basis weight positive).injective

instance : InnerProductSpace ℝ (WeightedModule basis weight positive) :=
  InnerProductSpace.induced (weightedOrthonormalCoordinates basis weight positive)

omit [Fintype ι] in
instance [Finite ι] : FiniteDimensional ℝ (WeightedModule basis weight positive) := by
  letI := Fintype.ofFinite ι
  exact (weightedCoefficients basis weight positive).symm.finiteDimensional

/-- Every strictly positive weight gives exactly the reciprocal-weight inner product. -/
theorem weighted_inner (x y : WeightedModule basis weight positive) :
    ⟪x, y⟫_ℝ = ∑ i, weightedCoefficients basis weight positive x i *
      weightedCoefficients basis weight positive y i / weight i := by
  classical
  change ⟪weightedOrthonormalCoordinates basis weight positive x,
    weightedOrthonormalCoordinates basis weight positive y⟫_ℝ = _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change ((Real.sqrt (weight i))⁻¹ * weightedCoefficients basis weight positive y i) *
    ((Real.sqrt (weight i))⁻¹ * weightedCoefficients basis weight positive x i) = _
  calc
    _ = (weightedCoefficients basis weight positive x i *
        weightedCoefficients basis weight positive y i) *
        (Real.sqrt (weight i) * Real.sqrt (weight i))⁻¹ := by rw [mul_inv]; ring
    _ = _ := by rw [← pow_two, Real.sq_sqrt (positive i).le]; rfl

end WeightedMetric

section Algebraic

variable (S : ShortComplex (ModuleCat ℝ))

/-- The ordinary homology class of a genuine cycle, in categorical homology. -/
def cycleClass : S.g.hom.ker →ₗ[ℝ] S.homology :=
  (S.moduleCatCyclesIso.inv ≫ S.homologyπ).hom

private theorem cycleClass_surjective : Function.Surjective (cycleClass S) := by
  apply (ModuleCat.epi_iff_surjective _).1
  infer_instance

private theorem cycleClass_eq_zero (x : S.g.hom.ker) :
    cycleClass S x = 0 ↔ x ∈ S.moduleCatToCycles.range := by
  have hi := S.moduleCatHomologyIso.toLinearEquiv.injective
  rw [← (map_eq_zero_iff _ hi)]
  change (S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ S.moduleCatHomologyIso.hom) x = 0 ↔ _
  simp only [ShortComplex.moduleCatCyclesIso_inv_π_assoc, Iso.inv_hom_id,
    Category.comp_id]
  exact Submodule.Quotient.mk_eq_zero _

variable {S} {R : ShortComplex (ModuleCat ℝ)} (φ : S ⟶ R)

/-- The chain map on the actual cycle kernels. -/
def cycleMap : S.g.hom.ker →ₗ[ℝ] R.g.hom.ker :=
  (φ.τ₂.hom.comp S.g.hom.ker.subtype).codRestrict _ (by
    intro x
    change R.g (φ.τ₂ x.val) = 0
    have h := congrArg (fun f => f x.val) φ.comm₂₃
    simpa using h)

private theorem cycleClass_naturality :
    (cycleClass R).comp (cycleMap φ) =
      (ShortComplex.homologyMap φ).hom.comp (cycleClass S) := by
  have h : ModuleCat.ofHom (cycleMap φ) ≫ R.moduleCatCyclesIso.inv =
      S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ := by
    apply (cancel_mono R.iCycles).1
    simp only [Category.assoc, ShortComplex.moduleCatCyclesIso_inv_iCycles,
      ShortComplex.cyclesMap_i, ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
    rfl
  exact congrArg ModuleCat.Hom.hom (show
      ModuleCat.ofHom (cycleMap φ) ≫ R.moduleCatCyclesIso.inv ≫ R.homologyπ =
        S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ ShortComplex.homologyMap φ by
    rw [← Category.assoc, h, Category.assoc, ShortComplex.homologyπ_naturality])

/-- The map taking a cycle to the homology class of its included chain. -/
def imageClass : S.g.hom.ker →ₗ[ℝ] R.homology :=
  (cycleClass R).comp (cycleMap φ)

private theorem range_imageClass :
    (imageClass φ).range = (ShortComplex.homologyMap φ).hom.range := by
  rw [imageClass, cycleClass_naturality, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (cycleClass_surjective S), Submodule.map_top]

/-- All incoming chains whose boundary lies in the chain inclusion's range. -/
abbrev FillingDomain : Submodule ℝ R.X₁ :=
  φ.τ₂.hom.range.comap R.f.hom

/-- The uniquely restricted incoming boundary. -/
def restrictedBoundary (hi : Function.Injective φ.τ₂) : FillingDomain φ →ₗ[ℝ] S.X₂ :=
  (LinearEquiv.ofInjective φ.τ₂.hom hi).symm.toLinearMap.comp
    ((R.f.hom.comp (FillingDomain φ).subtype).codRestrict _ (fun x => x.property))

private theorem inclusion_restrictedBoundary (hi : Function.Injective φ.τ₂)
    (x : FillingDomain φ) : φ.τ₂ (restrictedBoundary φ hi x) = R.f x := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective φ.τ₂.hom hi).apply_symm_apply
    ⟨R.f x, x.property⟩)

private theorem restrictedBoundary_cycle (hi : Function.Injective φ.τ₂)
    (h₃ : Function.Injective φ.τ₃)
    (x : FillingDomain φ) : S.g (restrictedBoundary φ hi x) = 0 := by
  have h := congrArg (fun z => R.g z) (inclusion_restrictedBoundary φ hi x)
  rw [R.moduleCat_zero_apply] at h
  have hc := congrArg (fun f => f (restrictedBoundary φ hi x)) φ.comm₂₃
  apply h₃
  simpa using hc.symm.trans h

private def boundaryToCycles (hi : Function.Injective φ.τ₂)
    (h₃ : Function.Injective φ.τ₃) : FillingDomain φ →ₗ[ℝ] S.g.hom.ker :=
  (restrictedBoundary φ hi).codRestrict _ (restrictedBoundary_cycle φ hi h₃)

private theorem range_boundaryToCycles (hi : Function.Injective φ.τ₂)
    (h₃ : Function.Injective φ.τ₃) :
    (boundaryToCycles φ hi h₃).range = (imageClass φ).ker := by
  ext x
  rw [LinearMap.mem_ker, imageClass, LinearMap.comp_apply, cycleClass_eq_zero]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u.val, Subtype.ext ?_⟩
    exact (inclusion_restrictedBoundary φ hi u).symm
  · rintro ⟨u, hu⟩
    have hv : R.f u = φ.τ₂ x.val := congrArg Subtype.val hu
    let v : FillingDomain φ := ⟨u, ⟨x.val, hv.symm⟩⟩
    refine ⟨v, Subtype.ext (hi ?_)⟩
    exact (inclusion_restrictedBoundary φ hi v).trans hv

end Algebraic

section Inner

set_option allowUnsafeReducibility true in
attribute [local reducible] ShortComplex.moduleCatMk

variable {A B C X Y Z : Type}
  [AddCommGroup A] [Module ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  {f : A →ₗ[ℝ] B} {d : B →ₗ[ℝ] C} {hfd : d.comp f = 0}
  {b : X →ₗ[ℝ] Y} {e : Y →ₗ[ℝ] Z} {hbe : e.comp b = 0}

variable (φ : ShortComplex.moduleCatMk f d hfd ⟶ ShortComplex.moduleCatMk b e hbe)

/-- The incoming term uses the inherited metric on the entire filling domain. -/
def laplacian (hi : Function.Injective φ.τ₂) : B →ₗ[ℝ] B :=
  (restrictedBoundary φ hi).comp (restrictedBoundary φ hi).adjoint + d.adjoint.comp d


theorem laplacian_eq_zero (hi : Function.Injective φ.τ₂) (x : B) :
    laplacian φ hi x = 0 ↔
      (restrictedBoundary φ hi).adjoint x = 0 ∧ d x = 0 := by
  let T : FillingDomain φ →ₗ[ℝ] B := restrictedBoundary φ hi
  constructor
  · intro h
    have he : ⟪T.adjoint x, T.adjoint x⟫_ℝ + ⟪d x, d x⟫_ℝ = 0 := by
      calc
        _ = ⟪laplacian φ hi x, x⟫_ℝ := by
          change _ = ⟪T (T.adjoint x) + d.adjoint (d x), x⟫_ℝ
          rw [inner_add_left]
          exact congrArg₂ (· + ·) (LinearMap.adjoint_inner_right T (T.adjoint x) x)
            (LinearMap.adjoint_inner_left d x (d x)).symm
        _ = 0 := by rw [h, inner_zero_left]
    have hT : T.adjoint x = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp
      (le_antisymm (by linarith [real_inner_self_nonneg (x := d x)])
        real_inner_self_nonneg)
    have hD : d x = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp
      (le_antisymm (by linarith [real_inner_self_nonneg (x := T.adjoint x)])
        real_inner_self_nonneg)
    exact ⟨hT, hD⟩
  · rintro ⟨hT, hD⟩
    simp [laplacian, hT, hD]

omit [FiniteDimensional ℝ C] in
private theorem cycle_orthogonal_iff (hi : Function.Injective φ.τ₂)
    (h₃ : Function.Injective φ.τ₃) (x : d.ker) :
    x ∈ (imageClass φ).kerᗮ ↔ (restrictedBoundary φ hi).adjoint x.val = 0 := by
  rw [← range_boundaryToCycles φ hi h₃, Submodule.mem_orthogonal]
  constructor
  · intro h
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hh := h (boundaryToCycles φ hi h₃ ((restrictedBoundary φ hi).adjoint x.val))
      ⟨_, rfl⟩
    change ⟪restrictedBoundary φ hi ((restrictedBoundary φ hi).adjoint x.val),
      x.val⟫_ℝ = 0 at hh
    rwa [← LinearMap.adjoint_inner_right] at hh
  · intro h y hy
    obtain ⟨u, rfl⟩ := hy
    change ⟪restrictedBoundary φ hi u, x.val⟫_ℝ = 0
    rw [← LinearMap.adjoint_inner_right, h, inner_zero_right]

def harmonicCycles (hi : Function.Injective φ.τ₂)
    (h₃ : Function.Injective φ.τ₃) :
    (laplacian φ hi).ker ≃ₗ[ℝ] ↥(imageClass φ).kerᗮ := by
  exact LinearEquiv.ofLinearMap
    { toFun := fun x =>
        ⟨⟨x.val, ((laplacian_eq_zero φ hi x.val).mp x.property).2⟩,
          (cycle_orthogonal_iff φ hi h₃ _).mpr
            ((laplacian_eq_zero φ hi x.val).mp x.property).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    { toFun := fun x => ⟨x.val.val,
        (laplacian_eq_zero φ hi _).mpr
          ⟨(cycle_orthogonal_iff φ hi h₃ x.val).mp x.property, x.val.property⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (by ext; rfl) (by ext; rfl)

/-- Harmonic vectors map to the image of the actual induced homology map. -/
def harmonicEquivImage (hi : Function.Injective φ.τ₂)
    (h₃ : Function.Injective φ.τ₃) :
    (laplacian φ hi).ker ≃ₗ[ℝ] (ShortComplex.homologyMap φ).hom.range := by
  exact (harmonicCycles φ hi h₃).trans
    (((imageClass φ).ker.quotientEquivOrthogonal.toLinearEquiv.symm.trans
      (imageClass φ).quotKerEquivRange).trans
        (LinearEquiv.ofEq _ _ (range_imageClass φ)))

/-- The equivalence sends a harmonic vector to the class of its included chain. -/
theorem harmonicEquivImage_apply (hi : Function.Injective φ.τ₂)
    (h₃ : Function.Injective φ.τ₃) (x : (laplacian φ hi).ker) :
    (harmonicEquivImage φ hi h₃ x).val =
      cycleClass (ShortComplex.moduleCatMk b e hbe) (cycleMap φ
        ⟨x.val, ((laplacian_eq_zero φ hi x.val).mp x.property).2⟩) := by
  change ((imageClass φ).quotKerEquivRange
    ((imageClass φ).ker.quotientEquivOrthogonal.symm (harmonicCycles φ hi h₃ x))).val = _
  rw [Submodule.quotientEquivOrthogonal_symm_eq_mk]
  exact (imageClass φ).quotKerEquivRange_apply_mk _

end Inner
section NaturalChains

variable {P Q : ℕ → Type}
  [∀ n, NormedAddCommGroup (P n)] [∀ n, InnerProductSpace ℝ (P n)]
  [∀ n, FiniteDimensional ℝ (P n)]
  [∀ n, NormedAddCommGroup (Q n)] [∀ n, InnerProductSpace ℝ (Q n)]
  [∀ n, FiniteDimensional ℝ (Q n)]

/-- The unaugmented outgoing differential has a zero map in degree zero. -/
def outgoing (d : ∀ n, P (n + 1) →ₗ[ℝ] P n) :
    ∀ q, P q →ₗ[ℝ] P (q - 1)
  | 0 => 0
  | q + 1 => d q

omit [∀ n, FiniteDimensional ℝ (P n)] in
private theorem outgoing_squared (d : ∀ n, P (n + 1) →ₗ[ℝ] P n)
    (sq : ∀ n, (d n).comp (d (n + 1)) = 0) (q : ℕ) :
    (outgoing d q).comp (d q) = 0 := by
  cases q with
  | zero => simp [outgoing]
  | succ q => exact sq q

/-- The standard short complex computing homology in degree q. -/
def window (d : ∀ n, P (n + 1) →ₗ[ℝ] P n)
    (sq : ∀ n, (d n).comp (d (n + 1)) = 0) (q : ℕ) : ShortComplex (ModuleCat ℝ) :=
  ShortComplex.moduleCatMk (d q) (outgoing d q) (by exact outgoing_squared d sq q)

/-- The actual real chain complex with the given successive differentials. -/
def realComplex (d : ∀ n, P (n + 1) →ₗ[ℝ] P n)
    (sq : ∀ n, (d n).comp (d (n + 1)) = 0) : ChainComplex (ModuleCat ℝ) ℕ :=
  ChainComplex.of (fun q => ModuleCat.of ℝ (P q))
    (fun q => ModuleCat.ofHom (d q)) (fun q => ModuleCat.hom_ext (sq q))

/-- The comparison uses the actual chain-complex homology, including degree zero. -/
def windowIso (d : ∀ n, P (n + 1) →ₗ[ℝ] P n)
    (sq : ∀ n, (d n).comp (d (n + 1)) = 0) (q : ℕ) :
    (realComplex d sq).sc q ≅ window d sq q := by
  cases q with
  | zero =>
    refine (realComplex d sq).isoSc' 1 0 0 (by simp) (by simp) ≪≫ ?_
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · change ModuleCat.ofHom (d 0) = _
      exact (ChainComplex.of_d (fun n => ModuleCat.of ℝ (P n))
        (fun n => ModuleCat.ofHom (d n)) 0).symm
    · simp [realComplex, window, outgoing, ChainComplex.of_d_ne]
  | succ q =>
    refine (realComplex d sq).isoSc' (q + 1 + 1) (q + 1) q (by simp) (by simp) ≪≫ ?_
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simp [realComplex, window, ChainComplex.of_d]
    · simp [realComplex, window, outgoing, ChainComplex.of_d]

variable (d : ∀ n, P (n + 1) →ₗ[ℝ] P n)
  (sq : ∀ n, (d n).comp (d (n + 1)) = 0)
  (b : ∀ n, Q (n + 1) →ₗ[ℝ] Q n)
  (bsq : ∀ n, (b n).comp (b (n + 1)) = 0)
  (i : ∀ n, P n →ₗ[ℝ] Q n)
  (comm : ∀ n, (b n).comp (i (n + 1)) = (i n).comp (d n))

/-- The short-complex map is induced by the actual degreewise chain map. -/
def windowMap (q : ℕ) : window d sq q ⟶ window b bsq q where
  τ₁ := ModuleCat.ofHom (i (q + 1))
  τ₂ := ModuleCat.ofHom (i q)
  τ₃ := ModuleCat.ofHom (i (q - 1))
  comm₁₂ := ModuleCat.hom_ext (comm q)
  comm₂₃ := by
    cases q with
    | zero => simp [window, outgoing]
    | succ q => exact ModuleCat.hom_ext (comm q)

/-- The chain map on the full, untruncated natural-number complex. -/
def realChainMap : realComplex d sq ⟶ realComplex b bsq :=
  ChainComplex.ofHom (fun q => ModuleCat.ofHom (i q)) (by
    intro q
    simpa only [realComplex, ChainComplex.of_d] using ModuleCat.hom_ext (comm q))

private theorem windowMap_naturality (q : ℕ) :
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) q).map
        (realChainMap d sq b bsq i comm) ≫ (windowIso b bsq q).hom =
      (windowIso d sq q).hom ≫ windowMap d sq b bsq i comm q := by
  cases q <;> ext <;> simp [windowIso, windowMap, realChainMap, realComplex]

private def homologyComparison (q : ℕ) :
    (realComplex d sq).homology q ≅ (window d sq q).homology :=
  ShortComplex.homologyMapIso (windowIso d sq q)

private theorem homologyComparison_naturality (q : ℕ) :
    HomologicalComplex.homologyMap (realChainMap d sq b bsq i comm) q ≫
        (homologyComparison b bsq q).hom =
      (homologyComparison d sq q).hom ≫
        ShortComplex.homologyMap (windowMap d sq b bsq i comm q) := by
  change ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ =
    ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
    windowMap_naturality]

private theorem homology_range_transport (q : ℕ) :
    (HomologicalComplex.homologyMap (realChainMap d sq b bsq i comm) q).hom.range.map
        (homologyComparison b bsq q).hom.hom =
      (ShortComplex.homologyMap (windowMap d sq b bsq i comm q)).hom.range := by
  rw [← LinearMap.range_comp]
  have h := congrArg ModuleCat.Hom.hom
    (homologyComparison_naturality d sq b bsq i comm q)
  rw [show (homologyComparison b bsq q).hom.hom.comp
      (HomologicalComplex.homologyMap (realChainMap d sq b bsq i comm) q).hom =
      (ShortComplex.homologyMap (windowMap d sq b bsq i comm q)).hom.comp
        (homologyComparison d sq q).hom.hom from h]
  have hs : (homologyComparison d sq q).hom.hom.range = ⊤ :=
    LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  rw [LinearMap.range_comp, hs, Submodule.map_top]

private def homologyRangeEquiv (q : ℕ) :
    (HomologicalComplex.homologyMap (realChainMap d sq b bsq i comm) q).hom.range ≃ₗ[ℝ]
      (ShortComplex.homologyMap (windowMap d sq b bsq i comm q)).hom.range :=
  (Submodule.equivMapOfInjective (homologyComparison b bsq q).hom.hom
    (homologyComparison b bsq q).toLinearEquiv.injective _).trans
    (LinearEquiv.ofEq _ _ (homology_range_transport d sq b bsq i comm q))

set_option allowUnsafeReducibility true in
attribute [local reducible] window ShortComplex.moduleCatMk

/-- The persistent operator on an arbitrary finite real chain inclusion. -/
def naturalLaplacian (hi : ∀ q, Function.Injective (i q)) (q : ℕ) :
    P q →ₗ[ℝ] P q :=
  laplacian (windowMap d sq b bsq i comm q) (hi q)

/-- Harmonic chains represent the range of the actual full-complex homology map. -/
def naturalHodgeEquiv (hi : ∀ q, Function.Injective (i q)) (q : ℕ) :
    (naturalLaplacian d sq b bsq i comm hi q).ker ≃ₗ[ℝ]
      (HomologicalComplex.homologyMap (realChainMap d sq b bsq i comm) q).hom.range :=
  (harmonicEquivImage (windowMap d sq b bsq i comm q) (hi q) (hi (q - 1))).trans
    (homologyRangeEquiv d sq b bsq i comm q).symm

/-- A harmonic chain is a cycle for the unaugmented outgoing boundary. -/
theorem naturalHodge_cycle (hi : ∀ q, Function.Injective (i q)) (q : ℕ)
    (x : (naturalLaplacian d sq b bsq i comm hi q).ker) : outgoing d q x.val = 0 :=
  ((laplacian_eq_zero (windowMap d sq b bsq i comm q) (hi q) x.val).mp x.property).2

/-- The actual homology class of an included cycle, transported from the standard short complex. -/
def includedClass (q : ℕ) (x : (outgoing d q).ker) : (realComplex b bsq).homology q :=
  (homologyComparison b bsq q).inv
    (cycleClass (window b bsq q) (cycleMap (windowMap d sq b bsq i comm q) x))

/-- The representative formula uses the actual chain-induced homology class. -/
theorem naturalHodgeEquiv_apply (hi : ∀ q, Function.Injective (i q)) (q : ℕ)
    (x : (naturalLaplacian d sq b bsq i comm hi q).ker) :
    (naturalHodgeEquiv d sq b bsq i comm hi q x).val =
      includedClass d sq b bsq i comm q
        ⟨x.val, naturalHodge_cycle d sq b bsq i comm hi q x⟩ := by
  apply (homologyComparison b bsq q).toLinearEquiv.injective
  have h := congrArg Subtype.val
    ((homologyRangeEquiv d sq b bsq i comm q).apply_symm_apply
      (harmonicEquivImage (windowMap d sq b bsq i comm q) (hi q) (hi (q - 1)) x))
  change (homologyComparison b bsq q).hom
    (naturalHodgeEquiv d sq b bsq i comm hi q x).val = _ at h
  rw [harmonicEquivImage_apply] at h
  simpa [includedClass] using h

end NaturalChains

end D5.S3.Geometry.SimplicialPersistence.WeightedPersistentHodge

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

private def integerRetraction (K L : PreAbstractSimplicialComplex V) (q : ℕ) :
    orderedGroup L q ⟶ orderedGroup K q := by
  classical
  exact Sigma.desc fun s => if hs : s.val ∈ K then
    faceι K ⟨s.val, hs, s.property.2⟩ else 0

omit [Fintype V] in
private theorem integerInclusion_retraction {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (q : ℕ) : integerInclusion h q ≫ integerRetraction K L q = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro s
  simp [integerInclusion, integerRetraction, faceι, faceInclusion, s.property.1]

omit [Fintype V] in
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

def integerCoordinates (K : PreAbstractSimplicialComplex V) (q : ℕ) :
    orderedGroup K q ≃ₗ[ℤ] (Face K q → ℤ) :=
  LinearEquiv.ofBijective (PersistentLaplacianHeatStability.coordinates K q) (by
    classical
    exact (DirectSum.linearEquivFunOnFintype ℤ (Face K q) (fun _ => ℤ)).bijective.comp
      (ModuleCat.coprodIsoDirectSum (fun _ : Face K q => Z)).toLinearEquiv.bijective)

def integerBasis (K : PreAbstractSimplicialComplex V) (q : ℕ) :
    Module.Basis (Face K q) ℤ (orderedGroup K q) :=
  Module.Basis.ofEquivFun (integerCoordinates K q)


private theorem integerCoordinates_face (K : PreAbstractSimplicialComplex V) (q : ℕ)
    (s : Face K q) : integerCoordinates K q (faceι K s (1 : ℤ)) = Pi.single s 1 := by
  classical
  change (DirectSum.linearEquivFunOnFintype ℤ (Face K q) (fun _ => ℤ))
    ((ModuleCat.coprodIsoDirectSum (fun _ : Face K q => Z)).hom (faceι K s (1 : ℤ))) = _
  have hc := congrArg (fun f => f (1 : ℤ))
    (ModuleCat.ι_coprodIsoDirectSum_hom (fun _ : Face K q => Z) s)
  rw [show (ModuleCat.coprodIsoDirectSum (fun _ : Face K q => Z)).hom (faceι K s (1 : ℤ)) =
      DirectSum.lof ℤ (Face K q) (fun _ => ℤ) s 1 from hc]
  rfl

private theorem integerBasis_face (K : PreAbstractSimplicialComplex V) (q : ℕ)
    (s : Face K q) : integerBasis K q s = faceι K s (1 : ℤ) := by
  classical
  rw [integerBasis, Module.Basis.coe_ofEquivFun]
  apply (integerCoordinates K q).injective
  rw [LinearEquiv.apply_symm_apply, integerCoordinates_face]

/-- Scalar extension on chains, with the exact positive-weight metric. -/
def Chain (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :=
  WeightedModule (integerBasis K q) (w.value q) (w.positive q)

instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    AddCommGroup (Chain K w q) := inferInstanceAs (AddCommGroup
      (WeightedModule (integerBasis K q) (w.value q) (w.positive q)))
instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    Module ℝ (Chain K w q) := inferInstanceAs (Module ℝ
      (WeightedModule (integerBasis K q) (w.value q) (w.positive q)))
instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    NormedAddCommGroup (Chain K w q) := inferInstanceAs (NormedAddCommGroup
      (WeightedModule (integerBasis K q) (w.value q) (w.positive q)))
instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    InnerProductSpace ℝ (Chain K w q) := inferInstanceAs (InnerProductSpace ℝ
      (WeightedModule (integerBasis K q) (w.value q) (w.positive q)))
instance (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    FiniteDimensional ℝ (Chain K w q) := inferInstanceAs (FiniteDimensional ℝ
      (WeightedModule (integerBasis K q) (w.value q) (w.positive q)))

/-- The coefficients identify chains with all real functions on actual faces. -/
def coefficients (K : PreAbstractSimplicialComplex V) (w : Weights K) (q : ℕ) :
    Chain K w q ≃ₗ[ℝ] (Face K q → ℝ) :=
  weightedCoefficients (integerBasis K q) (w.value q) (w.positive q)

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
  realComplex (boundary K w) (by exact boundary_squared K w)

/-- Zero extension of actual chains; this is scalar extension of face inclusion. -/
def inclusion {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (w : Weights L) (q : ℕ) :
    Chain K (w.restrict h) q →ₗ[ℝ] Chain L w q :=
  (integerInclusion h q).hom.baseChange ℝ


section CoefficientCompatibility

set_option allowUnsafeReducibility true in
attribute [local reducible] Chain WeightedModule

private theorem inclusion_basis {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) (s : Face K q) :
    inclusion h w q ((integerBasis K q).baseChange ℝ s) =
      (integerBasis L q).baseChange ℝ (faceInclusion h q s) := by
  have hc := congrArg (fun f => f (1 : ℤ)) (show
    faceι K s ≫ integerInclusion h q = faceι L (faceInclusion h q s) by
    simp [faceι, integerInclusion])
  simp only [inclusion, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    integerBasis_face]
  exact congrArg (fun z => (1 : ℝ) ⊗ₜ[ℤ] z) hc

private def coefficientExtension (K L : PreAbstractSimplicialComplex V) (q : ℕ) :
    (Face K q → ℝ) →ₗ[ℝ] (Face L q → ℝ) := by
  classical
  exact {
    toFun := fun x t => if ht : t.val ∈ K then x ⟨t.val, ht, t.property.2⟩ else 0
    map_add' := fun x y => by ext t; dsimp; split_ifs <;> simp
    map_smul' := fun a x => by ext t; dsimp; split_ifs <;> simp }

private theorem inclusion_coefficients {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) :
    (coefficients L w q).toLinearMap.comp (inclusion h w q) =
      (coefficientExtension K L q).comp (coefficients K (w.restrict h) q).toLinearMap := by
  classical
  apply ((integerBasis K q).baseChange ℝ).ext
  intro s
  rw [LinearMap.comp_apply, inclusion_basis]
  ext t
  by_cases ht : t.val ∈ K
  · let u : Face K q := ⟨t.val, ht, t.property.2⟩
    by_cases hs : s.val = t.val
    · have hL : faceInclusion h q s = t := Subtype.ext hs
      have hK : s = u := Subtype.ext hs
      simp [coefficients, weightedCoefficients, coefficientExtension,
        Module.Basis.equivFun_self, ht, hL, hK, u, faceInclusion, Subtype.ext_iff, hs]
    · have hL : faceInclusion h q s ≠ t := fun he => hs (congrArg Subtype.val he)
      have hK : s ≠ u := fun he => hs (congrArg Subtype.val he)
      simp [coefficients, weightedCoefficients, coefficientExtension,
        Module.Basis.equivFun_self, ht, hL, hK, u, faceInclusion, Subtype.ext_iff, hs]
  · have hL : faceInclusion h q s ≠ t := by
      intro he
      apply ht
      rw [← congrArg Subtype.val he]
      exact s.property.1
    simp [coefficients, weightedCoefficients, coefficientExtension,
      Module.Basis.equivFun_self, ht, hL]

end CoefficientCompatibility

private theorem inclusion_injective {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) : Function.Injective (inclusion h w q) := by
  have hsplit := congrArg (fun f => f.hom.baseChange ℝ) (integerInclusion_retraction h q)
  have hleft : ((integerRetraction K L q).hom.baseChange ℝ).comp (inclusion h w q) =
      LinearMap.id := by
    simpa only [inclusion, Chain, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.baseChange_comp,
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
  realChainMap (boundary K (w.restrict h)) (by exact boundary_squared K (w.restrict h))
    (boundary L w) (by exact boundary_squared L w) (inclusion h w) (by exact inclusion_boundary h w)

/-- The persistent operator uses the full inverse image of the included chain space. -/
def persistentLaplacian {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) :
    Chain K (w.restrict h) q →ₗ[ℝ] Chain K (w.restrict h) q :=
  naturalLaplacian (boundary K (w.restrict h))
    (by exact boundary_squared K (w.restrict h)) (boundary L w) (by exact boundary_squared L w)
    (inclusion h w) (by exact inclusion_boundary h w) (by exact inclusion_injective h w) q

/-- The canonical harmonic representative equivalence for an actual finite simplicial pair. -/
def persistentHodgeEquiv {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) :
    (persistentLaplacian h w q).ker ≃ₗ[ℝ]
      (HomologicalComplex.homologyMap (chainInclusion h w) q).hom.range :=
  naturalHodgeEquiv (boundary K (w.restrict h))
    (by exact boundary_squared K (w.restrict h)) (boundary L w) (by exact boundary_squared L w)
    (inclusion h w) (by exact inclusion_boundary h w) (by exact inclusion_injective h w) q

/-- The homology class of the actual included harmonic chain. -/
def harmonicClass {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) (x : (persistentLaplacian h w q).ker) :
    (chainComplex L w).homology q :=
  includedClass (boundary K (w.restrict h))
    (by exact boundary_squared K (w.restrict h)) (boundary L w)
    (by exact boundary_squared L w) (inclusion h w) (by exact inclusion_boundary h w) q
    ⟨x.val, naturalHodge_cycle (boundary K (w.restrict h))
      (by exact boundary_squared K (w.restrict h)) (boundary L w)
      (by exact boundary_squared L w) (inclusion h w) (by exact inclusion_boundary h w)
      (by exact inclusion_injective h w) q x⟩

open Classical in
/-- The full weighted theorem, including the coefficient metric, representative and dimension. -/
theorem weighted_persistent_hodge {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) (w : Weights L) (q : ℕ) :
    (∀ r (x y : Chain L w r), ⟪x, y⟫_ℝ =
      ∑ s, coefficients L w r x s * coefficients L w r y s / w.value r s) ∧
    (∀ r (x y : Chain K (w.restrict h) r), ⟪x, y⟫_ℝ =
      ∑ s, coefficients K (w.restrict h) r x s * coefficients K (w.restrict h) r y s /
        (w.restrict h).value r s) ∧
    (∀ r (x : Chain K (w.restrict h) r) (t : Face L r),
      coefficients L w r (inclusion h w r x) t =
        if ht : t.val ∈ K then
          coefficients K (w.restrict h) r x ⟨t.val, ht, t.property.2⟩ else 0) ∧
    (∀ x : (persistentLaplacian h w q).ker,
      (persistentHodgeEquiv h w q x).val = harmonicClass h w q x) ∧
    Module.finrank ℝ (persistentLaplacian h w q).ker =
      Module.finrank ℝ (HomologicalComplex.homologyMap (chainInclusion h w) q).hom.range := by
  classical
  refine ⟨?_, ?_, ?_, ?_, (persistentHodgeEquiv h w q).finrank_eq⟩
  · intro r x y
    exact weighted_inner (integerBasis L r) (w.value r) (w.positive r) x y
  · intro r x y
    exact weighted_inner (integerBasis K r) ((w.restrict h).value r)
      ((w.restrict h).positive r) x y
  · intro r x t
    simpa [coefficientExtension] using
      congrFun (LinearMap.congr_fun (inclusion_coefficients h w r) x) t
  · intro x
    exact naturalHodgeEquiv_apply (boundary K (w.restrict h))
      (by exact boundary_squared K (w.restrict h)) (boundary L w) (by exact boundary_squared L w)
      (inclusion h w) (by exact inclusion_boundary h w) (by exact inclusion_injective h w) q x

end D5.S3.Geometry.SimplicialPersistence.WeightedPersistentHodge
