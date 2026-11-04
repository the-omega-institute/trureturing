/- GID: D5/S3/Geometry/FiniteSimplicialSingularHomology
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteSimplicialSingularHomology
   mirror-E: none(waiver:coordinate-topology)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Ordered integer H1 of a finite coordinate complex compares with its actual singular H1. -/

import D5.S3.Geometry.FiniteSimplicialOpenCover
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.Contractible
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.OrderedCech
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
The carrier throughout this file is `FiniteConeCollapse.realization K`, with
its coordinate subspace topology. An intersection is defined by strict
positivity of every coordinate indexed by the finite set. In particular these
are open vertex stars, and are not closed stars of faces.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Limits AlgebraicTopology Finset Topology
open scoped BigOperators ContinuousMap Simplicial

namespace D5.S3.Geometry.FiniteSimplicialSingularHomology

open FiniteConeCollapse FiniteSimplicialOpenCover

variable {V : Type} [Fintype V] [LinearOrder V]
variable (K : PreAbstractSimplicialComplex V)

/-- The small-chain supplier is used on the actual coordinate cover. -/
def coordinateSmallHomologyIso (n : ℕ) :
    ((TopCat.of (Space K)).smallSingularSubcomplex (vertexOpen K) : SSet).homology
        (ModuleCat.of ℤ ℤ) n ≅
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (Space K)) := by
  change (((TopCat.of (Space K)).smallSingularSubcomplex (vertexOpen K) : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)).homology n ≅
      ((TopCat.toSSet.obj (TopCat.of (Space K))).chainComplex (ModuleCat.of ℤ ℤ)).homology n
  exact TauCeti.smallSingularHomologyIso (X := TopCat.of (Space K))
    (ModuleCat.of ℤ ℤ) (vertexOpen K) (isOpen_vertexOpen K) (vertexOpen_cover K) n

section OrderedChains

open TauCeti.OrderedCechSingular


abbrev Z : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- Actual increasing faces: no truncation or dimension bound is imposed on `K`. -/
abbrev Face (p : ℕ) := {s : Finset V // s ∈ K ∧ s.card = p + 1}

instance (p : ℕ) : Fintype (Face K p) := by
  classical
  unfold Face
  infer_instance

/-- The free integer module on the actual ordered `p`-faces. -/
abbrev orderedGroup (p : ℕ) : ModuleCat ℤ := ∐ fun _ : Face K p => Z

def faceι {p : ℕ} (s : Face K p) : Z ⟶ orderedGroup K p :=
  Sigma.ι (fun _ : Face K p => Z) s

abbrev smallSet : SSet := small (TopCat.of (Space K)) (vertexOpen K)

abbrev memberSet (v : V) : (smallSet K).Subcomplex :=
  member (TopCat.of (Space K)) (vertexOpen K) v

/-- The actual integer Cech--singular double complex of the positive-coordinate cover. -/
abbrev cechSingular := integerBicomplex (TopCat.of (Space K)) (vertexOpen K)

/-- A basis map has one copy of Z per singular simplex, never a free-module coefficient. -/
def cechι {p q : ℕ} (s : Finset V) (hs : s.card = p + 1)
    (σ : (smallSet K) _⦋q⦌)
    (hσ : ∀ v ∈ s, σ ∈ (memberSet K v).obj (Opposite.op ⦋q⦌)) :
    Z ⟶ ((cechSingular K).X p).X q :=
  TauCeti.OrderedCover.basisι Z s hs σ hσ

omit [Fintype V] in
@[ext]
theorem cech_hom_ext {p q : ℕ} {M : ModuleCat ℤ}
    {f g : ((cechSingular K).X p).X q ⟶ M}
    (h : ∀ s hs σ hσ, cechι K (p := p) (q := q) s hs σ hσ ≫ f =
      cechι K s hs σ hσ ≫ g) : f = g :=
  TauCeti.OrderedCover.basis_hom_ext Z h

omit [Fintype V] in
@[reassoc]
theorem cechι_horizontal {p q : ℕ} (s : Finset V) (hs : s.card = p + 2)
    (σ : (smallSet K) _⦋q⦌)
    (hσ : ∀ v ∈ s, σ ∈ (memberSet K v).obj (Opposite.op ⦋q⦌)) :
    cechι K s hs σ hσ ≫ ((cechSingular K).d (p + 1) p).f q =
      ∑ v : s, ((-1 : ℤ) ^ (s.filter (fun w => w < v.1)).card) •
        cechι K (s.erase v.1) (by rw [card_erase_of_mem v.2, hs]; omega)
          σ (fun w hw => hσ w (mem_of_mem_erase hw)) :=
  TauCeti.OrderedCover.basisι_d Z s hs σ hσ

omit [Fintype V] in
@[reassoc]
theorem cechι_vertical {p q : ℕ} (s : Finset V) (hs : s.card = p + 1)
    (σ : (smallSet K) _⦋q + 1⦌)
    (hσ : ∀ v ∈ s, σ ∈ (memberSet K v).obj (Opposite.op ⦋q + 1⦌)) :
    cechι K s hs σ hσ ≫ ((cechSingular K).X p).d (q + 1) q =
      ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        cechι K s hs ((smallSet K).δ i σ)
          (fun v hv => (memberSet K v).map (SimplexCategory.δ i).op (hσ v hv)) := by
  change _ ≫ (((alternatingFaceMapComplex (ChainComplex (ModuleCat ℤ) ℕ)).obj
    (rows Z (smallSet K) (memberSet K))).d (q + 1) q).f p = _
  erw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [TauCeti.OrderedCechSingular.sum_chainMap_f, HomologicalComplex.zsmul_f_apply,
    Preadditive.comp_sum, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  simp [cechι, rows, SimplicialObject.δ]

/-- Any simplex carried by the intersection witnesses that its finite set is a face. -/
abbrev carriedFace {p q : ℕ} (s : Finset V) (hs : s.card = p + 1)
    (σ : (smallSet K) _⦋q⦌)
    (hσ : ∀ v ∈ s, σ ∈ (memberSet K v).obj (Opposite.op ⦋q⦌)) : Face K p := by
  refine ⟨s, ?_, hs⟩
  apply face_of_nonempty_intersection K (Finset.card_pos.mp (by omega))
  refine ⟨(TopCat.of (Space K)).toSSetObjEquiv _ σ.val
    (Convexity.StdSimplex.single (0 : Fin (q + 1))), ?_⟩
  intro v hv
  exact hσ v hv ⟨_, rfl⟩

/-- The actual coefficient-sum map in singular degree zero. -/
def coefficientSum (p : ℕ) : ((cechSingular K).X p).X 0 ⟶ orderedGroup K p :=
  Sigma.desc fun s => Sigma.desc fun σ =>
    faceι K (carriedFace K s.val s.property σ.val σ.property)

@[reassoc (attr := simp)]
theorem cechι_coefficientSum {p : ℕ} (s : Finset V) (hs : s.card = p + 1)
    (σ : (smallSet K) _⦋0⦌)
    (hσ : ∀ v ∈ s, σ ∈ (memberSet K v).obj (Opposite.op ⦋0⦌)) :
    cechι K s hs σ hσ ≫ coefficientSum K p =
      faceι K (carriedFace K s hs σ hσ) := by
  rw [cechι, TauCeti.OrderedCover.basisι_eq]
  simp only [coefficientSum, Category.assoc, Sigma.ι_comp_desc]

/-- The constant singular simplex at a face's genuine coordinate barycenter. -/
def barycenterSimplex {p : ℕ} (s : Face K p) (q : ℕ) : (smallSet K) _⦋q⦌ := by
  let σ := ((TopCat.of (Space K)).toSSetObjEquiv (Opposite.op ⦋q⦌)).symm
    (ContinuousMap.const _ (barycenter K s.property.1))
  refine ⟨σ, ?_⟩
  obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces s.property.1).1
  refine ⟨v, ?_⟩
  rintro _ ⟨z, rfl⟩
  simpa [σ, vertexOpen] using barycenter_mem_intersection K s.property.1 v hv

theorem barycenterSimplex_carried {p : ℕ} (s : Face K p) (q : ℕ) :
    ∀ v ∈ s.val, barycenterSimplex K s q ∈
      (memberSet K v).obj (Opposite.op ⦋q⦌) := by
  intro v hv
  rintro _ ⟨z, rfl⟩
  simpa [barycenterSimplex, vertexOpen] using barycenter_mem_intersection K s.property.1 v hv

private def coefficientSection (p : ℕ) : orderedGroup K p ⟶ ((cechSingular K).X p).X 0 :=
  Sigma.desc fun s => cechι K s.val s.property.2 (barycenterSimplex K s 0)
    (barycenterSimplex_carried K s 0)

private theorem coefficientSection_coefficientSum (p : ℕ) :
    coefficientSection K p ≫ coefficientSum K p = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  simp only [coefficientSection, Sigma.ι_comp_desc_assoc, cechι_coefficientSum,
    Category.comp_id]
  rfl

instance coefficientSum_epi (p : ℕ) : Epi (coefficientSum K p) :=
  epi_of_epi_fac (coefficientSection_coefficientSum K p)

def eraseFace {p : ℕ} (s : Face K (p + 1)) (v : s.val) : Face K p := by
  have hc : (s.val.erase v.val).card = p + 1 := by
    rw [card_erase_of_mem v.property, s.property.2]
    omega
  exact ⟨s.val.erase v.val,
    (K.isRelLowerSet_faces s.property.1).2 (s.val.erase_subset v.val)
      (Finset.card_pos.mp (by omega)), hc⟩

/-- Increasing-face deletion, with the ordinary rank sign. -/
def orderedBoundary (p : ℕ) : orderedGroup K (p + 1) ⟶ orderedGroup K p :=
  Sigma.desc fun s => ∑ v : s.val,
    ((-1 : ℤ) ^ (s.val.filter (fun w => w < v.val)).card) • faceι K (eraseFace K s v)

@[reassoc]
theorem coefficientSum_horizontal (p : ℕ) :
    coefficientSum K (p + 1) ≫ orderedBoundary K p =
      ((cechSingular K).d (p + 1) p).f 0 ≫ coefficientSum K p := by
  apply cech_hom_ext K
  intro s hs σ hσ
  rw [← Category.assoc, cechι_coefficientSum, faceι, orderedBoundary,
    Sigma.ι_comp_desc, ← Category.assoc, cechι_horizontal,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Preadditive.zsmul_comp, cechι_coefficientSum]
  rfl

/-- Boundary squared is inherited from the actual row differential through the surjection. -/
theorem orderedBoundary_squared (p : ℕ) :
    orderedBoundary K (p + 1) ≫ orderedBoundary K p = 0 := by
  apply (cancel_epi (coefficientSum K (p + 2))).1
  rw [← Category.assoc, coefficientSum_horizontal, Category.assoc,
    coefficientSum_horizontal, ← Category.assoc,
    HomologicalComplex₂.d_f_comp_d_f, zero_comp, comp_zero]

/-- The full ordered integer chain complex; faces in degrees above two are retained. -/
def orderedChainComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (orderedGroup K) (orderedBoundary K) (orderedBoundary_squared K)

theorem coefficientSum_vertical :
    ∀ p, ((cechSingular K).X p).d 1 0 ≫ coefficientSum K p = 0 := by
  intro p
  apply cech_hom_ext K
  intro s hs σ hσ
  rw [← Category.assoc, cechι_vertical, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, cechι_coefficientSum]
  rw [Fin.sum_univ_two]
  change (1 : ℤ) • faceι K (carriedFace K s hs _ _) +
    (-1 : ℤ) • faceι K (carriedFace K s hs _ _) = _
  simp only [carriedFace, one_smul, neg_smul, add_neg_cancel, comp_zero]

/-- Ordinary singular coefficient sum on each intersection, zero above singular degree zero. -/
def columnAugmentation (p : ℕ) :
    (cechSingular K).X p ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj (orderedGroup K p) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨coefficientSum K p, coefficientSum_vertical K p⟩

abbrev singleRow (L : ChainComplex (ModuleCat ℤ) ℕ) :
    HomologicalComplex₂ (ModuleCat ℤ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ((ChainComplex.single₀ (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj L

/-- The actual vertical augmentation as a morphism of commuting bicomplexes. -/
def verticalAugmentation : cechSingular K ⟶ singleRow (orderedChainComplex K) where
  f := columnAugmentation K
  comm' := by
    rintro _ p rfl
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f, columnAugmentation,
      ChainComplex.toSingle₀Equiv_symm_apply_f_zero, singleRow,
      Functor.mapHomologicalComplex_obj_d, ChainComplex.single₀_map_f_zero,
      orderedChainComplex, ChainComplex.of_d]
    change coefficientSum K (p + 1) ≫ orderedBoundary K p =
      ((cechSingular K).d (p + 1) p).f 0 ≫ coefficientSum K p
    exact coefficientSum_horizontal K p

/-! ### The columns are actual singular chains of intersections

The two inverse basis maps below use continuous maps into the subspace, not
formal labels for intersections. Empty intersections contribute no generator:
`carriedFace` supplies a real face for every generator that actually exists.
-/

abbrev intersectionChains {p : ℕ} (s : Face K p) : ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj (TopCat.of (intersection K s.val))).chainComplex Z

def intersectionSimplexEquiv {p : ℕ} (s : Face K p) (q : ℕ) :
    (TopCat.toSSet.obj (TopCat.of (intersection K s.val))) _⦋q⦌ ≃
      {σ : (smallSet K) _⦋q⦌ //
        ∀ v ∈ s.val, σ ∈ (memberSet K v).obj (Opposite.op ⦋q⦌)} where
  toFun σ := by
    let c := (TopCat.of (intersection K s.val)).toSSetObjEquiv (Opposite.op ⦋q⦌) σ
    let d : C(Convexity.StdSimplex ℝ (Fin (q + 1)), Space K) :=
      (ContinuousMap.subtypeVal _).comp c
    let τ := ((TopCat.of (Space K)).toSSetObjEquiv (Opposite.op ⦋q⦌)).symm d
    have ht : ∀ v ∈ s.val, Set.range
        ((TopCat.of (Space K)).toSSetObjEquiv (Opposite.op ⦋q⦌) τ) ⊆ vertexOpen K v := by
      intro v hv
      rintro _ ⟨z, rfl⟩
      simpa [τ, d, vertexOpen] using (c z).property v hv
    refine ⟨⟨τ, ?_⟩, ht⟩
    obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces s.property.1).1
    exact ⟨v, ht v hv⟩
  invFun σ :=
    ((TopCat.of (intersection K s.val)).toSSetObjEquiv (Opposite.op ⦋q⦌)).symm
      ⟨fun z => ⟨(TopCat.of (Space K)).toSSetObjEquiv (Opposite.op ⦋q⦌) σ.val.val z,
          fun v hv => σ.property v hv ⟨z, rfl⟩⟩,
        (((TopCat.of (Space K)).toSSetObjEquiv (Opposite.op ⦋q⦌) σ.val.val).continuous).subtype_mk _⟩
  left_inv σ := by
    apply ((TopCat.of (intersection K s.val)).toSSetObjEquiv (Opposite.op ⦋q⦌)).injective
    ext z
    simp
  right_inv σ := by
    apply Subtype.ext
    apply Subtype.ext
    apply ((TopCat.of (Space K)).toSSetObjEquiv (Opposite.op ⦋q⦌)).injective
    ext z
    simp

omit [Fintype V] in
theorem intersectionSimplexEquiv_face {p q : ℕ} (s : Face K p)
    (σ : (TopCat.toSSet.obj (TopCat.of (intersection K s.val))) _⦋q + 1⦌)
    (i : Fin (q + 2)) :
    (intersectionSimplexEquiv K s q
      ((TopCat.toSSet.obj (TopCat.of (intersection K s.val))).δ i σ)).val =
      (smallSet K).δ i (intersectionSimplexEquiv K s (q + 1) σ).val := by
  apply Subtype.ext
  apply ((TopCat.of (Space K)).toSSetObjEquiv _).injective
  ext z
  rfl

private def intersectionColumnMap {p : ℕ} (s : Face K p) (q : ℕ) :
    (intersectionChains K s).X q ⟶ ((cechSingular K).X p).X q :=
  Sigma.desc fun σ =>
    cechι K s.val s.property.2 (intersectionSimplexEquiv K s q σ).val
      (intersectionSimplexEquiv K s q σ).property

omit [Fintype V] in
@[reassoc]
private theorem ι_intersectionColumnMap {p q : ℕ} (s : Face K p)
    (σ : (TopCat.toSSet.obj (TopCat.of (intersection K s.val))) _⦋q⦌) :
    (TopCat.toSSet.obj (TopCat.of (intersection K s.val))).ιChainComplex σ ≫
        intersectionColumnMap K s q =
      cechι K s.val s.property.2 (intersectionSimplexEquiv K s q σ).val
        (intersectionSimplexEquiv K s q σ).property :=
  Sigma.ι_comp_desc _ _

private theorem intersectionColumnMap_comm {p : ℕ} (s : Face K p) (q : ℕ) :
    intersectionColumnMap K s (q + 1) ≫ ((cechSingular K).X p).d (q + 1) q =
      (intersectionChains K s).d (q + 1) q ≫ intersectionColumnMap K s q := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_intersectionColumnMap, cechι_vertical,
    ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, ι_intersectionColumnMap]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [intersectionSimplexEquiv_face]

private def intersectionColumnι {p : ℕ} (s : Face K p) :
    intersectionChains K s ⟶ (cechSingular K).X p where
  f := intersectionColumnMap K s
  comm' := by
    rintro _ q rfl
    exact intersectionColumnMap_comm K s q

@[reassoc (attr := simp)]
private theorem ι_intersectionColumnι {p q : ℕ} (s : Face K p)
    (σ : (TopCat.toSSet.obj (TopCat.of (intersection K s.val))) _⦋q⦌) :
    (TopCat.toSSet.obj (TopCat.of (intersection K s.val))).ιChainComplex σ ≫
        (intersectionColumnι K s).f q =
      cechι K s.val s.property.2 (intersectionSimplexEquiv K s q σ).val
        (intersectionSimplexEquiv K s q σ).property :=
  ι_intersectionColumnMap K s σ

abbrev columnCoproduct (p : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  ∐ fun s : Face K p => intersectionChains K s

private def columnToCoproduct (p : ℕ) : (cechSingular K).X p ⟶ columnCoproduct K p where
  f q := Sigma.desc fun s => Sigma.desc fun σ =>
    let F := carriedFace K s.val s.property σ.val σ.property
    (TopCat.toSSet.obj (TopCat.of (intersection K F.val))).ιChainComplex
        ((intersectionSimplexEquiv K F q).symm ⟨σ.val, σ.property⟩) ≫
      (Sigma.ι (fun t : Face K p => intersectionChains K t) F).f q
  comm' := by
    rintro _ q rfl
    apply cech_hom_ext K
    intro s hs σ hσ
    change (cechι K s hs σ hσ ≫ _) ≫ _ =
      (cechι K s hs σ hσ ≫ ((cechSingular K).X p).d (q + 1) q) ≫ _
    rw [cechι_vertical, Preadditive.sum_comp]
    simp only [cechι, TauCeti.OrderedCover.basisι_eq, Category.assoc, Sigma.ι_comp_desc,
      Preadditive.zsmul_comp]
    erw [HomologicalComplex.Hom.comm, ← Category.assoc, SSet.ιChainComplex_d,
      Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1

@[reassoc (attr := simp)]
private theorem cechι_columnToCoproduct {p q : ℕ}
    (s : Finset V) (hs : s.card = p + 1) (σ : (smallSet K) _⦋q⦌)
    (hσ : ∀ v ∈ s, σ ∈ (memberSet K v).obj (Opposite.op ⦋q⦌)) :
    cechι K s hs σ hσ ≫ (columnToCoproduct K p).f q =
      (TopCat.toSSet.obj (TopCat.of (intersection K s))).ιChainComplex
          ((intersectionSimplexEquiv K (carriedFace K s hs σ hσ) q).symm ⟨σ, hσ⟩) ≫
        (Sigma.ι (fun t : Face K p => intersectionChains K t)
          (carriedFace K s hs σ hσ)).f q := by
  rw [cechι, TauCeti.OrderedCover.basisι_eq]
  simp only [columnToCoproduct, Category.assoc, Sigma.ι_comp_desc]

private def coproductToColumn (p : ℕ) : columnCoproduct K p ⟶ (cechSingular K).X p :=
  Sigma.desc (intersectionColumnι K)

@[reassoc]
private theorem ι_coproductToColumn {p q : ℕ} (s : Face K p) :
    (Sigma.ι (fun t : Face K p => intersectionChains K t) s).f q ≫
        (coproductToColumn K p).f q = (intersectionColumnι K s).f q := by
  exact congrArg (fun f : intersectionChains K s ⟶ (cechSingular K).X p => f.f q)
    (Sigma.ι_comp_desc (intersectionColumnι K) s)

/-- Explicit basis identification with the coproduct of the actual intersection chain complexes. -/
def columnCoproductIso (p : ℕ) : (cechSingular K).X p ≅ columnCoproduct K p where
  hom := columnToCoproduct K p
  inv := coproductToColumn K p
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro q
    apply cech_hom_ext K
    intro s hs σ hσ
    change (cechι K s hs σ hσ ≫ (columnToCoproduct K p).f q) ≫
      (coproductToColumn K p).f q = cechι K s hs σ hσ
    rw [cechι_columnToCoproduct, Category.assoc, ι_coproductToColumn]
    simpa only [Equiv.apply_symm_apply] using
      ι_intersectionColumnι K (carriedFace K s hs σ hσ)
        ((intersectionSimplexEquiv K (carriedFace K s hs σ hσ) q).symm ⟨σ, hσ⟩)
  inv_hom_id := by
    apply Sigma.hom_ext
    intro s
    rw [coproductToColumn, Sigma.ι_comp_desc_assoc, Category.comp_id]
    apply HomologicalComplex.hom_ext
    intro q
    apply SSet.chainComplex_hom_ext
    intro σ
    change ((TopCat.toSSet.obj (TopCat.of (intersection K s.val))).ιChainComplex σ ≫
      (intersectionColumnι K s).f q) ≫ (columnToCoproduct K p).f q =
      (TopCat.toSSet.obj (TopCat.of (intersection K s.val))).ιChainComplex σ ≫
        (Sigma.ι (fun t : Face K p => intersectionChains K t) s).f q
    rw [ι_intersectionColumnι, cechι_columnToCoproduct]
    change (TopCat.toSSet.obj (TopCat.of (intersection K s.val))).ιChainComplex
        ((intersectionSimplexEquiv K s q).symm (intersectionSimplexEquiv K s q σ)) ≫
        (Sigma.ι (fun t : Face K p => intersectionChains K t) s).f q = _
    rw [Equiv.symm_apply_apply]

private theorem homologyMap_sigmaMap_isIso {J : Type} [Finite J]
    {A B : J → ChainComplex (ModuleCat ℤ) ℕ} (f : ∀ j, A j ⟶ B j)
    (q : ℕ) (hf : ∀ j, IsIso (HomologicalComplex.homologyMap (f j) q)) :
    IsIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.Sigma.map f) q) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) q
  have hnat : CategoryTheory.Limits.Sigma.map (fun j => H.map (f j)) ≫ sigmaComparison H B =
      sigmaComparison H A ≫ H.map (CategoryTheory.Limits.Sigma.map f) := by
    apply Sigma.hom_ext
    intro j
    simp only [Sigma.ι_map_assoc, ι_comp_sigmaComparison,
      ι_comp_sigmaComparison_assoc, ← H.map_comp, Sigma.ι_map]
  have hmap : H.map (CategoryTheory.Limits.Sigma.map f) = inv (sigmaComparison H A) ≫
      CategoryTheory.Limits.Sigma.map (fun j => H.map (f j)) ≫ sigmaComparison H B := by
    rw [hnat, IsIso.inv_hom_id_assoc]
  change IsIso (H.map (CategoryTheory.Limits.Sigma.map f))
  rw [hmap]
  haveI : ∀ j, IsIso (H.map (f j)) := hf
  infer_instance

private def coproductColumnAugmentation (p : ℕ) :
    columnCoproduct K p ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj (orderedGroup K p) :=
  CategoryTheory.Limits.Sigma.map (fun s : Face K p =>
      coefficientAugmentation Z (TopCat.toSSet.obj (TopCat.of (intersection K s.val)))) ≫
    sigmaComparison (ChainComplex.single₀ (ModuleCat ℤ)) (fun _ : Face K p => Z)

omit [Fintype V] in
private theorem summand_coproductColumnAugmentation (p : ℕ) (s : Face K p) :
    (Sigma.ι (fun t : Face K p => intersectionChains K t) s).f 0 ≫
        (coproductColumnAugmentation K p).f 0 =
      (coefficientAugmentation Z
        (TopCat.toSSet.obj (TopCat.of (intersection K s.val)))).f 0 ≫
          faceι K s := by
  change (Sigma.ι (fun t : Face K p => intersectionChains K t) s ≫
    coproductColumnAugmentation K p).f 0 = _
  rw [coproductColumnAugmentation, Sigma.ι_map_assoc, ι_comp_sigmaComparison]
  rfl

private theorem columnAugmentation_factorization (p : ℕ) :
    columnAugmentation K p = (columnCoproductIso K p).hom ≫
      coproductColumnAugmentation K p := by
  apply HomologicalComplex.to_single_hom_ext
  change (columnAugmentation K p).f 0 =
    (columnToCoproduct K p).f 0 ≫ (coproductColumnAugmentation K p).f 0
  apply cech_hom_ext K
  intro s hs σ hσ
  erw [columnAugmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
    cechι_coefficientSum, ← Category.assoc,
    cechι_columnToCoproduct]
  rw [Category.assoc, summand_coproductColumnAugmentation, ← Category.assoc]
  erw [ι_coefficientAugmentation]
  exact (Category.id_comp _).symm

/-- Every column comparison is induced by the actual coefficient sum. -/
theorem columnAugmentation_isIso (p q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (columnAugmentation K p) q) := by
  haveI h : ∀ s : Face K p, IsIso (HomologicalComplex.homologyMap
      (coefficientAugmentation Z
        (TopCat.toSSet.obj (TopCat.of (intersection K s.val)))) q) := by
    intro s
    letI := contractible_intersection K s.property.1
    exact isIso_coefficientAugmentation_of_contractible Z
      (TopCat.of (intersection K s.val)) q
  haveI := homologyMap_sigmaMap_isIso
    (fun s : Face K p => coefficientAugmentation Z
      (TopCat.toSSet.obj (TopCat.of (intersection K s.val)))) q h
  rw [columnAugmentation_factorization, coproductColumnAugmentation,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- Only degree-one isomorphisms and the required degree-two epimorphism are requested. -/
theorem vertical_total_comparison :
    (∀ n ≤ 1, IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (verticalAugmentation K) (ComplexShape.down ℕ)) n)) ∧
      Epi (HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (verticalAugmentation K) (ComplexShape.down ℕ)) 2) := by
  apply HomologicalComplex₂.finite_degree_comparison_total_map 1
  · intro p q hpq
    exact columnAugmentation_isIso K p q
  · intro p q hpq
    haveI : IsIso (HomologicalComplex.homologyMap ((verticalAugmentation K).f p) q) :=
      columnAugmentation_isIso K p q
    infer_instance

/-- Integral H1 of the ordered chain complex and of the actual coordinate realization.
There is no homology, good-cover, augmentation, or comparison premise. -/
def orderedChainH1IsoSingular :
    (orderedChainComplex K).homology 1 ≅
      ((singularHomologyFunctor (ModuleCat ℤ) 1).obj Z).obj (TopCat.of (Space K)) := by
  let D := cechSingular K
  let εv := HomologicalComplex₂.total.map (verticalAugmentation K) (ComplexShape.down ℕ)
  let εh := HomologicalComplex₂.total.map
    (integerHorizontalAugmentation (TopCat.of (Space K)) (vertexOpen K))
    (ComplexShape.down ℕ)
  haveI : IsIso (HomologicalComplex.homologyMap εv 1) :=
    (vertical_total_comparison K).1 1 (by omega)
  haveI : IsIso (HomologicalComplex.homologyMap εh 1) :=
    (horizontal_total_comparison Z (smallSet K) (memberSet K)
      (members_cover (TopCat.of (Space K)) (vertexOpen K))).1 1 (by omega)
  let ev : (D.total (ComplexShape.down ℕ)).homology 1 ≅
      (orderedChainComplex K).homology 1 :=
    asIso (HomologicalComplex.homologyMap εv 1) ≪≫
      HomologicalComplex.homologyMapIso
        (TauCeti.OrderedCechSingular.singleRowTotalIso (orderedChainComplex K)) 1
  let eh : (D.total (ComplexShape.down ℕ)).homology 1 ≅ (smallSet K).homology Z 1 :=
    asIso (HomologicalComplex.homologyMap εh 1) ≪≫
      HomologicalComplex.homologyMapIso
        (TauCeti.OrderedCechSingular.singleColumnTotalIso ((smallSet K).chainComplex Z)) 1
  exact ev.symm ≪≫ eh ≪≫ coordinateSmallHomologyIso K 1

/-- Exactly the integer triangle -> edge -> vertex boundary short complex. -/
abbrev orderedShortComplex : ShortComplex (ModuleCat ℤ) :=
  (orderedChainComplex K).sc' 2 1 0

/-- The finite ordered edge/triangle H1 comparison at the exact coordinate carrier. -/
def orderedH1IsoSingular :
    (orderedShortComplex K).homology ≅
      ((singularHomologyFunctor (ModuleCat ℤ) 1).obj Z).obj
        (TopCat.of ↥(FiniteConeCollapse.realization K)) :=
  ShortComplex.homologyMapIso
      ((orderedChainComplex K).isoSc' 2 1 0 (by simp) (by simp)).symm ≪≫
    orderedChainH1IsoSingular K

end OrderedChains

end D5.S3.Geometry.FiniteSimplicialSingularHomology
