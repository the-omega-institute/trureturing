/- GID: D5/S3/Geometry/FiniteSimplicialSingularHomology
   generality: G
   mirror-B: none(waiver:source-artifact-awaiting-canonical-validation)
   mirror-E: none(waiver:coordinate-topology)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: The positive-coordinate vertex cover of the actual finite realization. -/

import D5.S3.Geometry.FiniteConeCollapse
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

This source artifact has not been elaborated or compiled.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap Simplicial

namespace D5.S3.Geometry.FiniteSimplicialSingularHomology

open FiniteConeCollapse

variable {V : Type} [Fintype V] [LinearOrder V]
variable (K : PreAbstractSimplicialComplex V)

/-- The actual finite coordinate carrier, including the empty realization. -/
abbrev Space := ↥(FiniteConeCollapse.realization K)

/-- A useful public form of the existing coordinate-simplex identity. -/
theorem mem_realization_iff (x : V → ℝ) :
    x ∈ FiniteConeCollapse.realization K ↔
      ∃ s ∈ K, x ∈ FiniteConeCollapse.faceSimplex s := by
  simp only [FiniteConeCollapse.realization, Set.mem_setOf_eq,
    FiniteConeCollapse.faceSimplex_eq_convexHull]

theorem coordinate_data (x : Space K) :
    (∀ v, 0 ≤ x.val v) ∧ (∑ v, x.val v) = 1 := by
  obtain ⟨s, hs, hx⟩ := (mem_realization_iff K x.val).1 x.property
  exact ⟨hx.1, hx.2.1⟩

/-- The real open vertex star. Ghost vertices give empty stars. -/
def vertexOpen (v : V) : Set (Space K) := {x | 0 < x.val v}

theorem isOpen_vertexOpen (v : V) : IsOpen (vertexOpen K v) :=
  isOpen_lt continuous_const ((continuous_apply v).comp continuous_subtype_val)

theorem vertexOpen_cover : ⋃ v, vertexOpen K v = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hpos : ∃ v, 0 < x.val v := by
    by_contra h
    push_neg at h
    have hz : ∀ v, x.val v = 0 :=
      fun v => le_antisymm (h v) ((coordinate_data K x).1 v)
    have hsum := (coordinate_data K x).2
    simp only [hz, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨v, hv⟩ := hpos
  exact Set.mem_iUnion.mpr ⟨v, hv⟩

/-- Every finite intersection, with the empty intersection equal to the carrier. -/
def intersection (s : Finset V) : Set (Space K) :=
  {x | ∀ v ∈ s, 0 < x.val v}

theorem intersection_eq_iInter (s : Finset V) :
    intersection K s = ⋂ v ∈ s, vertexOpen K v := by
  ext x
  simp [intersection, vertexOpen]

theorem isOpen_intersection (s : Finset V) : IsOpen (intersection K s) := by
  rw [intersection_eq_iInter]
  exact isOpen_biInter_finset fun v hv => isOpen_vertexOpen K v

theorem intersection_antitone {s t : Finset V} (hst : s ⊆ t) :
    intersection K t ⊆ intersection K s :=
  fun _ hx v hv => hx v (hst hv)

/-- Positivity forces every chosen vertex to lie in the original support face. -/
theorem intersection_subset_support {s f : Finset V} {x : Space K}
    (hx : x ∈ intersection K s) (hf : x.val ∈ faceSimplex f) : s ⊆ f := by
  intro v hv
  by_contra hvf
  exact (ne_of_gt (hx v hv)) (hf.2.2 v hvf)

theorem face_of_nonempty_intersection {s : Finset V} (hs : s.Nonempty)
    (h : (intersection K s).Nonempty) : s ∈ K := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨f, hf, hxf⟩ := (mem_realization_iff K x.val).1 x.property
  exact (K.isRelLowerSet_faces hf).2 (intersection_subset_support K hx hxf) hs

/-- Equal weights on exactly the vertices of `s`. -/
def barycenterCoords (s : Finset V) (v : V) : ℝ :=
  if v ∈ s then 1 / (s.card : ℝ) else 0

theorem barycenterCoords_mem_faceSimplex {s : Finset V} (hs : s.Nonempty) :
    barycenterCoords s ∈ faceSimplex s := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  refine ⟨?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ s <;> simp [barycenterCoords, hv, hc.le]
  · have hsum : (∑ v, barycenterCoords s v) = ∑ v ∈ s, barycenterCoords s v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro v hv hvs
      simp [barycenterCoords, hvs]
    rw [hsum]
    calc
      (∑ v ∈ s, barycenterCoords s v) = ∑ _v ∈ s, 1 / (s.card : ℝ) := by
        exact Finset.sum_congr rfl fun v hv => by simp [barycenterCoords, hv]
      _ = 1 := by simp [hc.ne']
  · intro v hv
    simp [barycenterCoords, hv]

/-- A barycenter is constructed only from an actual nonempty face. -/
def barycenter {s : Finset V} (hs : s ∈ K) : Space K :=
  ⟨barycenterCoords s, (mem_realization_iff K _).2
    ⟨s, hs, barycenterCoords_mem_faceSimplex (K.isRelLowerSet_faces hs).1⟩⟩

theorem barycenter_mem_intersection {s : Finset V} (hs : s ∈ K) :
    barycenter K hs ∈ intersection K s := by
  intro v hv
  change 0 < barycenterCoords s v
  rw [barycenterCoords, if_pos hv]
  exact one_div_pos.mpr (by exact_mod_cast (K.isRelLowerSet_faces hs).1.card_pos)

theorem nonempty_intersection_iff {s : Finset V} (hs : s.Nonempty) :
    (intersection K s).Nonempty ↔ s ∈ K :=
  ⟨face_of_nonempty_intersection K hs,
    fun hf => ⟨barycenter K hf, barycenter_mem_intersection K hf⟩⟩

/-- No vertices outside the original support face appear during the contraction. -/
theorem segment_mem_original_face {s f : Finset V} (hs : s ∈ K)
    (x : Space K) (hx : x ∈ intersection K s)
    (hxf : x.val ∈ faceSimplex f) (t : I) :
    (fun v => (1 - (t : ℝ)) * x.val v + (t : ℝ) * barycenterCoords s v) ∈
      faceSimplex f := by
  have hsf : s ⊆ f := intersection_subset_support K hx hxf
  have hb : barycenterCoords s ∈ faceSimplex f := by
    refine ⟨(barycenterCoords_mem_faceSimplex (K.isRelLowerSet_faces hs).1).1,
      (barycenterCoords_mem_faceSimplex (K.isRelLowerSet_faces hs).1).2.1, ?_⟩
    intro v hv
    exact (barycenterCoords_mem_faceSimplex (K.isRelLowerSet_faces hs).1).2.2 v
      (fun hvs => hv (hsf hvs))
  have hc : Convex ℝ (faceSimplex f) := by
    rw [faceSimplex_eq_convexHull]
    exact convex_convexHull _ _
  exact hc hxf hb (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

/-- The actual straight-line contraction, valued in the actual intersection. -/
def contractIntersection {s : Finset V} (hs : s ∈ K)
    (t : I) (x : intersection K s) : intersection K s := by
  let y : V → ℝ :=
    fun v => (1 - (t : ℝ)) * x.val.val v + (t : ℝ) * barycenterCoords s v
  have hy : y ∈ FiniteConeCollapse.realization K := by
    obtain ⟨f, hf, hxf⟩ := (mem_realization_iff K x.val.val).1 x.val.property
    exact (mem_realization_iff K y).2
      ⟨f, hf, segment_mem_original_face K hs x.val x.property hxf t⟩
  refine ⟨⟨y, hy⟩, ?_⟩
  intro v hv
  have hxv : 0 < x.val.val v := x.property v hv
  have hbv : 0 < barycenterCoords s v := barycenter_mem_intersection K hs v hv
  change 0 < (1 - (t : ℝ)) * x.val.val v + (t : ℝ) * barycenterCoords s v
  rcases lt_or_eq_of_le t.property.2 with ht | ht
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht) hxv)
      (mul_nonneg t.property.1 hbv.le)
  · rw [ht]
    simpa using hbv

theorem continuous_contractIntersection {s : Finset V} (hs : s ∈ K) :
    Continuous (fun z : I × intersection K s => contractIntersection K hs z.1 z.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_apply v).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))).add
    ((continuous_subtype_val.comp continuous_fst).mul continuous_const)

/-- This is a homotopy in the intersection, not merely in the ambient vector space. -/
def intersectionContraction {s : Finset V} (hs : s ∈ K) :
    (ContinuousMap.id (intersection K s)).Homotopy
      (ContinuousMap.const _ ⟨barycenter K hs, barycenter_mem_intersection K hs⟩) where
  toFun z := contractIntersection K hs z.1 z.2
  continuous_toFun := continuous_contractIntersection K hs
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    simp [contractIntersection]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    simp [contractIntersection, barycenter]

theorem contractible_intersection {s : Finset V} (hs : s ∈ K) :
    ContractibleSpace (intersection K s) :=
  (contractible_iff_id_nullhomotopic _).2
    ⟨⟨barycenter K hs, barycenter_mem_intersection K hs⟩,
      ⟨intersectionContraction K hs⟩⟩

/-- The small-chain supplier is used on the actual coordinate cover. -/
def coordinateSmallHomologyIso (n : ℕ) :
    ((TopCat.of (Space K)).smallSingularSubcomplex (vertexOpen K) : SSet).homology
        (ModuleCat.of ℤ ℤ) n ≅
      ((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (Space K)) :=
  TauCeti.smallSingularHomologyIso (ModuleCat.of ℤ ℤ) (vertexOpen K)
    (isOpen_vertexOpen K) (vertexOpen_cover K) n

theorem positive_intersection_homology_isZero {s : Finset V} (hs : s ∈ K)
    (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (intersection K s))) := by
  letI := contractible_intersection K hs
  exact TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace
    (ModuleCat.of ℤ ℤ) (TopCat.of (intersection K s)) hn

section OrderedChains

open TauCeti.OrderedCechSingular


abbrev Z : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- Actual increasing faces: no truncation or dimension bound is imposed on `K`. -/
def Face (p : ℕ) := {s : Finset V // s ∈ K ∧ s.card = p + 1}

instance (p : ℕ) : Fintype (Face K p) := Fintype.ofFinite _

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

@[ext]
theorem cech_hom_ext {p q : ℕ} {M : ModuleCat ℤ}
    {f g : ((cechSingular K).X p).X q ⟶ M}
    (h : ∀ s hs σ hσ, cechι K (p := p) (q := q) s hs σ hσ ≫ f =
      cechι K s hs σ hσ ≫ g) : f = g :=
  TauCeti.OrderedCover.basis_hom_ext Z h

@[reassoc]
theorem cechι_horizontal {p q : ℕ} (s : Finset V) (hs : s.card = p + 2)
    (σ : (smallSet K) _⦋q⦌)
    (hσ : ∀ v ∈ s, σ ∈ (memberSet K v).obj (Opposite.op ⦋q⦌)) :
    cechι K s hs σ hσ ≫ ((cechSingular K).d (p + 1) p).f q =
      ∑ v : s, ((-1 : ℤ) ^ #{w ∈ s | w < v.1}) •
        cechι K (s.erase v.1) (by rw [card_erase_of_mem v.2, hs]; omega)
          σ (fun w hw => hσ w (mem_of_mem_erase hw)) :=
  TauCeti.OrderedCover.basisι_d Z s hs σ hσ

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
  rw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [TauCeti.OrderedCechSingular.sum_chainMap_f, HomologicalComplex.zsmul_f_apply,
    Preadditive.comp_sum, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cechι, TauCeti.OrderedCover.basisι_map]
  rfl

/-- Any simplex carried by the intersection witnesses that its finite set is a face. -/
def carriedFace {p q : ℕ} (s : Finset V) (hs : s.card = p + 1)
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
  simpa [σ] using barycenter_mem_intersection K s.property.1 v hv

theorem barycenterSimplex_carried {p : ℕ} (s : Face K p) (q : ℕ) :
    ∀ v ∈ s.val, barycenterSimplex K s q ∈
      (memberSet K v).obj (Opposite.op ⦋q⦌) := by
  intro v hv
  rintro _ ⟨z, rfl⟩
  simpa [barycenterSimplex] using barycenter_mem_intersection K s.property.1 v hv

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
    ((-1 : ℤ) ^ #{w ∈ s.val | w < v.val}) • faceι K (eraseFace K s v)

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
    let c := (TopCat.of (intersection K s.val)).toSSetObjEquiv _ σ
    let d : C(Convexity.StdSimplex ℝ (Fin (q + 1)), Space K) :=
      (ContinuousMap.subtypeVal _).comp c
    let τ := ((TopCat.of (Space K)).toSSetObjEquiv _).symm d
    have ht : ∀ v ∈ s.val, Set.range
        ((TopCat.of (Space K)).toSSetObjEquiv _ τ) ⊆ vertexOpen K v := by
      intro v hv
      rintro _ ⟨z, rfl⟩
      simpa [τ, d] using (c z).property v hv
    obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces s.property.1).1
    exact ⟨⟨τ, ⟨v, ht v hv⟩⟩, ht⟩
  invFun σ :=
    ((TopCat.of (intersection K s.val)).toSSetObjEquiv _).symm
      ⟨fun z => ⟨(TopCat.of (Space K)).toSSetObjEquiv _ σ.val.val z,
          fun v hv => σ.property v hv ⟨z, rfl⟩⟩,
        (((TopCat.of (Space K)).toSSetObjEquiv _ σ.val.val).continuous).subtype_mk _⟩
  left_inv σ := by
    apply ((TopCat.of (intersection K s.val)).toSSetObjEquiv _).injective
    ext z
    simp
  right_inv σ := by
    apply Subtype.ext
    apply Subtype.ext
    apply ((TopCat.of (Space K)).toSSetObjEquiv _).injective
    ext z
    simp

theorem intersectionSimplexEquiv_face {p q : ℕ} (s : Face K p)
    (σ : (TopCat.toSSet.obj (TopCat.of (intersection K s.val))) _⦋q + 1⦌)
    (i : Fin (q + 2)) :
    (intersectionSimplexEquiv K s q
      ((TopCat.toSSet.obj (TopCat.of (intersection K s.val))).δ i σ)).val =
      (smallSet K).δ i (intersectionSimplexEquiv K s (q + 1) σ).val := by
  apply Subtype.ext
  apply ((TopCat.of (Space K)).toSSetObjEquiv _).injective
  ext z
  simp [intersectionSimplexEquiv, TopCat.toSSetObjEquiv_naturality_apply]

private def intersectionColumnι {p : ℕ} (s : Face K p) :
    intersectionChains K s ⟶ (cechSingular K).X p where
  f q := Sigma.desc fun σ =>
    cechι K s.val s.property.2 (intersectionSimplexEquiv K s q σ).val
      (intersectionSimplexEquiv K s q σ).property
  comm' := by
    rintro _ q rfl
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, Sigma.ι_comp_desc, cechι_vertical,
      ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp, Sigma.ι_comp_desc]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [intersectionSimplexEquiv_face]

@[reassoc (attr := simp)]
private theorem ι_intersectionColumnι {p q : ℕ} (s : Face K p)
    (σ : (TopCat.toSSet.obj (TopCat.of (intersection K s.val))) _⦋q⦌) :
    (TopCat.toSSet.obj (TopCat.of (intersection K s.val))).ιChainComplex σ ≫
        (intersectionColumnι K s).f q =
      cechι K s.val s.property.2 (intersectionSimplexEquiv K s q σ).val
        (intersectionSimplexEquiv K s q σ).property :=
  Sigma.ι_comp_desc _ _

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
    let F := carriedFace K s hs σ hσ
    let τ := (intersectionSimplexEquiv K F (q + 1)).symm ⟨σ, hσ⟩
    have hτ : (intersectionSimplexEquiv K F (q + 1) τ).val = σ :=
      congrArg Subtype.val ((intersectionSimplexEquiv K F (q + 1)).apply_symm_apply _)
    change (cechι K s hs σ hσ ≫ _) ≫ _ =
      (cechι K s hs σ hσ ≫ ((cechSingular K).X p).d (q + 1) q) ≫ _
    rw [cechι_vertical, Preadditive.sum_comp]
    simp only [cechι, TauCeti.OrderedCover.basisι_eq, Category.assoc, Sigma.ι_comp_desc,
      Preadditive.zsmul_comp]
    rw [← HomologicalComplex.Hom.comm, ← Category.assoc, SSet.ιChainComplex_d,
      Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have hiτ := intersectionSimplexEquiv_face K F τ i
    rw [hτ] at hiτ
    have hface : (intersectionSimplexEquiv K F q).symm
        ⟨(smallSet K).δ i σ,
          fun v hv => (memberSet K v).map (SimplexCategory.δ i).op (hσ v hv)⟩ =
        (TopCat.toSSet.obj (TopCat.of (intersection K F.val))).δ i τ := by
      apply (intersectionSimplexEquiv K F q).injective
      apply Subtype.ext
      simpa using hiτ.symm
    simp only [hface, Category.assoc]

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

/-- Explicit basis identification with the coproduct of the actual intersection chain complexes. -/
def columnCoproductIso (p : ℕ) : (cechSingular K).X p ≅ columnCoproduct K p where
  hom := columnToCoproduct K p
  inv := Sigma.desc (intersectionColumnι K)
  hom_inv_id := by
    ext q : 1
    apply cech_hom_ext K
    intro s hs σ hσ
    rw [HomologicalComplex.comp_f, ← Category.assoc, cechι_columnToCoproduct,
      Category.assoc, ← HomologicalComplex.comp_f, Sigma.ι_comp_desc,
      ι_intersectionColumnι]
    simp only [Equiv.apply_symm_apply, HomologicalComplex.id_f, Category.comp_id]
    rfl
  inv_hom_id := by
    apply Sigma.hom_ext
    intro s
    rw [Sigma.ι_comp_desc_assoc]
    ext q : 1
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [HomologicalComplex.comp_f, ← Category.assoc, ι_intersectionColumnι,
      cechι_columnToCoproduct]
    simp only [Equiv.symm_apply_apply, Category.comp_id]
    rfl

private theorem homologyMap_sigmaMap_isIso {J : Type} [Finite J]
    {A B : J → ChainComplex (ModuleCat ℤ) ℕ} (f : ∀ j, A j ⟶ B j)
    (q : ℕ) (hf : ∀ j, IsIso (HomologicalComplex.homologyMap (f j) q)) :
    IsIso (HomologicalComplex.homologyMap (Sigma.map f) q) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) q
  have hnat : Sigma.map (fun j => H.map (f j)) ≫ sigmaComparison H B =
      sigmaComparison H A ≫ H.map (Sigma.map f) := by
    apply Sigma.hom_ext
    intro j
    simp only [Sigma.ι_map_assoc, ι_comp_sigmaComparison,
      ι_comp_sigmaComparison_assoc, ← H.map_comp, Sigma.ι_map]
  have hmap : H.map (Sigma.map f) = inv (sigmaComparison H A) ≫
      Sigma.map (fun j => H.map (f j)) ≫ sigmaComparison H B := by
    rw [hnat, IsIso.inv_hom_id_assoc]
  change IsIso (H.map (Sigma.map f))
  rw [hmap]
  haveI : ∀ j, IsIso (H.map (f j)) := hf
  infer_instance

private def coproductColumnAugmentation (p : ℕ) :
    columnCoproduct K p ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj (orderedGroup K p) :=
  Sigma.map (fun s : Face K p =>
      coefficientAugmentation Z (TopCat.toSSet.obj (TopCat.of (intersection K s.val)))) ≫
    sigmaComparison (ChainComplex.single₀ (ModuleCat ℤ)) (fun _ : Face K p => Z)

private theorem columnAugmentation_factorization (p : ℕ) :
    columnAugmentation K p = (columnCoproductIso K p).hom ≫
      coproductColumnAugmentation K p := by
  apply HomologicalComplex.to_single_hom_ext
  apply cech_hom_ext K
  intro s hs σ hσ
  rw [columnAugmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
    cechι_coefficientSum, HomologicalComplex.comp_f, ← Category.assoc,
    cechι_columnToCoproduct]
  simp only [coproductColumnAugmentation, HomologicalComplex.comp_f, Category.assoc,
    ← HomologicalComplex.comp_f, Sigma.ι_map_assoc, ι_comp_sigmaComparison,
    HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero,
    ι_coefficientAugmentation, Category.id_comp]
  rfl

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
    have := columnAugmentation_isIso K p q
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
