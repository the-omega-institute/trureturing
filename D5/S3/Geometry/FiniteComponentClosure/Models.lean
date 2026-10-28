/- GID: D5/S3/Geometry/FiniteComponentClosure/Models
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteComponentClosure/Models
   mirror-E: none(waiver:finite-component-closure)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: Coordinate sphere bouquets, component normal forms, and actual vertex-gluing realizations. -/
import D5.S3.Geometry.FiniteComponentClosure.Transport

noncomputable section
open Set Finset Topology ContinuousMap
open scoped BigOperators unitInterval

namespace D5.S3.Geometry.FiniteComponentClosure

open private
  pointJoinContraction
  singleton_coordinates
  sphereVertex_face
  spherePath
  nativeCylinder
  coordinateLinear
  coordinateLinear_at
  coordinateLinear_single
  coordinateHomeomorph
  coproductComplex
  mem_coproductComplex
  coproductHomeomorph
  from D5.S3.Geometry.FiniteComponentClosure.Transport

abbrev BouquetSpec := List {d : ℕ // 0 < d}

/-- One common vertex and the separately tagged nonbase vertices of every sphere. -/
abbrev BouquetVertices (ds : BouquetSpec) :=
  Option (Σ i : Fin ds.length,
    {v : SphereVertices (ds.get i).val // v ≠ sphereVertex (ds.get i).val})

private def bouquetInclusion (ds : BouquetSpec) (i : Fin ds.length) :
    SphereVertices (ds.get i).val ↪ BouquetVertices ds where
  toFun v := if h : v = sphereVertex (ds.get i).val then none else some ⟨i, ⟨v, h⟩⟩
  inj' := by
    intro v w h
    change (if h : v = sphereVertex (ds.get i).val then none else some ⟨i, ⟨v, h⟩⟩ : BouquetVertices ds) =
      (if h : w = sphereVertex (ds.get i).val then none else some ⟨i, ⟨w, h⟩⟩ : BouquetVertices ds) at h
    by_cases hv : v = sphereVertex (ds.get i).val
    · by_cases hw : w = sphereVertex (ds.get i).val
      · exact hv.trans hw.symm
      · rw [dif_pos hv, dif_neg hw] at h
        cases h
    · by_cases hw : w = sphereVertex (ds.get i).val
      · rw [dif_neg hv, dif_pos hw] at h
        cases h
      · rw [dif_neg hv, dif_neg hw] at h
        have hs : (⟨i, ⟨v, hv⟩⟩ : Σ k : Fin ds.length,
            {v : SphereVertices (ds.get k).val // v ≠ sphereVertex (ds.get k).val}) =
            ⟨i, ⟨w, hw⟩⟩ := Option.some.inj h
        have hs' : (⟨v, hv⟩ : {v : SphereVertices (ds.get i).val //
            v ≠ sphereVertex (ds.get i).val}) = ⟨w, hw⟩ :=
          (@sigma_mk_injective (Fin ds.length)
            (fun k => {v : SphereVertices (ds.get k).val //
              v ≠ sphereVertex (ds.get k).val}) i) hs
        exact congrArg Subtype.val hs'

private theorem bouquetInclusion_base (ds : BouquetSpec) (i : Fin ds.length) :
    bouquetInclusion ds i (sphereVertex (ds.get i).val) = none := by
  exact dif_pos rfl

private theorem bouquetInclusion_off (ds : BouquetSpec) (i : Fin ds.length)
    (v : SphereVertices (ds.get i).val) (hv : v ≠ sphereVertex (ds.get i).val) :
    bouquetInclusion ds i v = some ⟨i, ⟨v, hv⟩⟩ := by
  exact dif_neg hv

/-- The singleton complex retains a genuine point when a sphere list is empty. -/
private def vertexComplex {V : Type*} [DecidableEq V] (v : V) :
    PreAbstractSimplicialComplex V where
  faces := {{v}}
  isRelLowerSet_faces := by
    rintro s rfl
    refine ⟨by simp, ?_⟩
    intro t hts ht
    exact Set.mem_singleton_iff.mpr (Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨ht, fun w hw => Finset.mem_singleton.mp (hts hw)⟩)

/-- The literal finite coordinate bouquet; no zero-dimensional sphere is a summand. -/
def bouquetComplex (ds : BouquetSpec) : PreAbstractSimplicialComplex (BouquetVertices ds) :=
  vertexComplex none ⊔ ⨆ i, (sphereComplex (ds.get i).val).map (bouquetInclusion ds i)

private theorem bouquetVertex_face (ds : BouquetSpec) :
    ({none} : Finset (BouquetVertices ds)) ∈ bouquetComplex ds := Or.inl rfl

def bouquetPoint (ds : BouquetSpec) : FiniteSimplicialJoin.Space (bouquetComplex ds) :=
  FiniteVertexCylinder.vertexPoint _ _ (bouquetVertex_face ds)

private theorem mem_bouquetComplex (ds : BouquetSpec) (s : Finset (BouquetVertices ds)) :
    s ∈ bouquetComplex ds ↔ s = {none} ∨
      ∃ i, s ∈ (sphereComplex (ds.get i).val).map (bouquetInclusion ds i) := by
  change (s ∈ vertexComplex none ∨ s ∈ ⋃ K ∈ Set.range
    (fun i => (sphereComplex (ds.get i).val).map (bouquetInclusion ds i)), K.faces) ↔ _
  apply or_congr Iff.rfl
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨K, ⟨i, rfl⟩, hs⟩; exact ⟨i, hs⟩
  · rintro ⟨i, hs⟩; exact ⟨_, ⟨i, rfl⟩, hs⟩

private def bouquetPiece (ds : BouquetSpec) (i : Fin ds.length) :
    C(FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val),
      FiniteSimplicialJoin.Space (bouquetComplex ds)) where
  toFun x := ⟨coordinateLinear (bouquetInclusion ds i) x.val, by
    obtain ⟨s, hs, hx⟩ := (coordinateHomeomorph (sphereComplex (ds.get i).val)
      (bouquetInclusion ds i) x).property
    exact ⟨s, (mem_bouquetComplex ds s).mpr (Or.inr ⟨i, hs⟩), hx⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((coordinateLinear (bouquetInclusion ds i)).continuous_of_finiteDimensional.comp
      continuous_subtype_val) _

private theorem bouquetPiece_base (ds : BouquetSpec) (i : Fin ds.length) :
    bouquetPiece ds i (spherePoint (ds.get i).val) = bouquetPoint ds := by
  apply Subtype.ext
  change coordinateLinear (bouquetInclusion ds i)
    (Pi.single (sphereVertex (ds.get i).val) 1) = Pi.single none 1
  rw [coordinateLinear_single, bouquetInclusion_base]

private theorem bouquetPiece_injective (ds : BouquetSpec) (i : Fin ds.length) :
    Function.Injective (bouquetPiece ds i) := by
  intro x y h
  apply Subtype.ext
  funext v
  have := congrArg (fun z : FiniteSimplicialJoin.Space (bouquetComplex ds) =>
    z.val (bouquetInclusion ds i v)) h
  simpa only [bouquetPiece, ContinuousMap.coe_mk, coordinateLinear_at] using this

private theorem bouquetInclusion_intersection (ds : BouquetSpec)
    (i j : Fin ds.length) (hij : i ≠ j)
    (v : SphereVertices (ds.get i).val) (w : SphereVertices (ds.get j).val)
    (h : bouquetInclusion ds i v = bouquetInclusion ds j w) :
    bouquetInclusion ds i v = none := by
  by_cases hv : v = sphereVertex (ds.get i).val
  · subst v
    exact bouquetInclusion_base ds i
  · by_cases hw : w = sphereVertex (ds.get j).val
    · subst w
      exact h.trans (bouquetInclusion_base ds j)
    · rw [bouquetInclusion_off ds i v hv, bouquetInclusion_off ds j w hw] at h
      exact (hij (congrArg Sigma.fst (Option.some.inj h))).elim

private theorem coordinates_eq_vertex {V : Type*} [Fintype V] [DecidableEq V]
    {M : PreAbstractSimplicialComplex V} (x : FiniteSimplicialJoin.Space M)
    (a : V) (ha : ({a} : Finset V) ∈ M) (hz : ∀ v, v ≠ a → x.val v = 0) :
    x = FiniteVertexCylinder.vertexPoint M a ha := by
  apply Subtype.ext
  apply singleton_coordinates a
  obtain ⟨s, _, hx⟩ := x.property
  rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hx
  exact ⟨hx.1, hx.2.1, fun v hv => hz v (by simpa using hv)⟩

private theorem bouquetPiece_intersection (ds : BouquetSpec)
    (i j : Fin ds.length) (hij : i ≠ j)
    (x : FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val))
    (y : FiniteSimplicialJoin.Space (sphereComplex (ds.get j).val))
    (h : bouquetPiece ds i x = bouquetPiece ds j y) :
    x = spherePoint (ds.get i).val ∧ y = spherePoint (ds.get j).val := by
  have hx : x = spherePoint (ds.get i).val := by
    apply coordinates_eq_vertex x _ (sphereVertex_face _)
    intro v hv
    have he := congrArg (fun z : FiniteSimplicialJoin.Space (bouquetComplex ds) =>
      z.val (bouquetInclusion ds i v)) h
    have hz : coordinateLinear (bouquetInclusion ds j) y.val (bouquetInclusion ds i v) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      have hne : bouquetInclusion ds j w ≠ bouquetInclusion ds i v := by
        intro hh
        have := bouquetInclusion_intersection ds i j hij v w hh.symm
        rw [bouquetInclusion_off ds i v hv] at this
        cases this
      simp [hne]
    simpa only [bouquetPiece, ContinuousMap.coe_mk, coordinateLinear_at, hz] using he
  refine ⟨hx, bouquetPiece_injective ds j ?_⟩
  rw [← h, hx, bouquetPiece_base, bouquetPiece_base]

/-- The quotient source includes a separate common vertex, so the empty family is a point. -/
abbrev BouquetSource (ds : BouquetSpec) :=
  PUnit.{1} ⊕ (Σ i : Fin ds.length, FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val))

private def bouquetBases (ds : BouquetSpec) : Set (BouquetSource ds) :=
  {z | Sum.elim (fun _ => True) (fun x => x.2 = spherePoint (ds.get x.1).val) z}

abbrev CoordinateBouquetQuotient (ds : BouquetSpec) :=
  FiniteConeUnionWedge.Collapse (bouquetBases ds)

private def bouquetSourceMap (ds : BouquetSpec) :
    C(BouquetSource ds, FiniteSimplicialJoin.Space (bouquetComplex ds)) where
  toFun := Sum.elim (fun _ => bouquetPoint ds) (fun x => bouquetPiece ds x.1 x.2)
  continuous_toFun := continuous_const.sumElim
    (continuous_sigma fun i => (bouquetPiece ds i).continuous)

private theorem bouquetSourceMap_base (ds : BouquetSpec) (z : BouquetSource ds)
    (hz : z ∈ bouquetBases ds) : bouquetSourceMap ds z = bouquetPoint ds := by
  rcases z with _ | ⟨i, x⟩
  · rfl
  · change x = spherePoint (ds.get i).val at hz
    subst x
    exact bouquetPiece_base ds i

private theorem bouquetSourceMap_kernel (ds : BouquetSpec) (z w : BouquetSource ds) :
    bouquetSourceMap ds z = bouquetSourceMap ds w ↔
      (FiniteConeUnionWedge.subsetSetoid (bouquetBases ds)).r z w := by
  constructor
  · intro h
    rcases z with z | ⟨i, x⟩ <;> rcases w with w | ⟨j, y⟩
    · exact Or.inl (congrArg Sum.inl (Subsingleton.elim _ _))
    · apply Or.inr
      refine ⟨True.intro, bouquetPiece_injective ds j ?_⟩
      exact h.symm.trans (bouquetPiece_base ds j).symm
    · apply Or.inr
      refine ⟨bouquetPiece_injective ds i ?_, True.intro⟩
      exact h.trans (bouquetPiece_base ds i).symm
    · by_cases hij : i = j
      · subst j
        exact Or.inl (congrArg Sum.inr (congrArg (Sigma.mk i) (bouquetPiece_injective ds i h)))
      · exact Or.inr (bouquetPiece_intersection ds i j hij x y h)
  · rintro (rfl | ⟨hz, hw⟩)
    · rfl
    · exact (bouquetSourceMap_base ds z hz).trans (bouquetSourceMap_base ds w hw).symm

private theorem bouquetSourceMap_surjective (ds : BouquetSpec) :
    Function.Surjective (bouquetSourceMap ds) := by
  intro y
  obtain ⟨s, hs, hy⟩ := y.property
  rcases (mem_bouquetComplex ds s).mp hs with rfl | ⟨i, hs⟩
  · rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hy
    exact ⟨Sum.inl PUnit.unit, Subtype.ext (singleton_coordinates none hy).symm⟩
  · let z : FiniteSimplicialJoin.Space
        ((sphereComplex (ds.get i).val).map (bouquetInclusion ds i)) := ⟨y.val, s, hs, hy⟩
    let x := (coordinateHomeomorph (sphereComplex (ds.get i).val)
      (bouquetInclusion ds i)).symm z
    refine ⟨Sum.inr ⟨i, x⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun w : FiniteSimplicialJoin.Space
      ((sphereComplex (ds.get i).val).map (bouquetInclusion ds i)) => w.val)
      ((coordinateHomeomorph (sphereComplex (ds.get i).val)
        (bouquetInclusion ds i)).apply_symm_apply z)

private def bouquetQuotientMap (ds : BouquetSpec) :
    C(CoordinateBouquetQuotient ds, FiniteSimplicialJoin.Space (bouquetComplex ds)) where
  toFun := Quotient.lift (bouquetSourceMap ds) (fun z w h =>
    (bouquetSourceMap_kernel ds z w).mpr h)
  continuous_toFun := (bouquetSourceMap ds).continuous.quotient_lift _

/-- The full quotient kernel, including all repeated sphere bases and the empty bouquet. -/
def bouquetQuotientHomeomorph (ds : BouquetSpec) :
    CoordinateBouquetQuotient ds ≃ₜ FiniteSimplicialJoin.Space (bouquetComplex ds) := by
  letI (i : Fin ds.length) : CompactSpace
      (FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val)) :=
    FiniteSimplicialJoin.realizationCompactSpace _
  apply Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (bouquetQuotientMap ds) ?_)
    (bouquetQuotientMap ds).continuous
  constructor
  · intro z w
    induction z using Quotient.inductionOn with
    | h z =>
      induction w using Quotient.inductionOn with
      | h w => exact fun h => Quotient.sound ((bouquetSourceMap_kernel ds z w).mp h)
  · intro y
    obtain ⟨z, hz⟩ := bouquetSourceMap_surjective ds y
    exact ⟨Quotient.mk _ z, hz⟩

private def bouquetPath (ds : BouquetSpec)
    (x : FiniteSimplicialJoin.Space (bouquetComplex ds)) : Path x (bouquetPoint ds) := by
  let z := Classical.choose (bouquetSourceMap_surjective ds x)
  have hz := Classical.choose_spec (bouquetSourceMap_surjective ds x)
  change bouquetSourceMap ds z = x at hz
  rcases z with _ | ⟨i, y⟩
  · exact (Path.refl (bouquetPoint ds)).cast hz.symm rfl
  · exact ((spherePath (ds.get i).val (ds.get i).property y).map
      (bouquetPiece ds i).continuous).cast hz.symm (bouquetPiece_base ds i).symm

private theorem emptyBouquet_point (x : FiniteSimplicialJoin.Space (bouquetComplex [])) :
    x = bouquetPoint [] := by
  obtain ⟨z, hz⟩ := bouquetSourceMap_surjective [] x
  rcases z with _ | ⟨i, _⟩
  · exact hz.symm
  · exact Fin.elim0 i

private def emptyBouquetJoinEquiv {Z : Type*} [TopologicalSpace Z] (z₀ : Z) :
    FiniteSimplicialJoin.OrdinaryJoin
      (FiniteSimplicialJoin.Space (bouquetComplex [])) Z ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex []) := by
  letI : Subsingleton (FiniteSimplicialJoin.Space (bouquetComplex [])) :=
    ⟨fun x y => (emptyBouquet_point x).trans (emptyBouquet_point y).symm⟩
  exact {
    toFun := ContinuousMap.const _ (bouquetPoint [])
    invFun := ContinuousMap.const _ (Quotient.mk _ (bouquetPoint [], z₀, (0 : I)))
    left_inv := ⟨(pointJoinContraction (bouquetPoint []) z₀).symm⟩
    right_inv := by
      have he : (ContinuousMap.const _ (bouquetPoint [])).comp
          (ContinuousMap.const _ (Quotient.mk
            (FiniteSimplicialJoin.ordinaryJoinSetoid _ Z) (bouquetPoint [], z₀, (0 : I)))) =
          ContinuousMap.id (FiniteSimplicialJoin.Space (bouquetComplex [])) := by
        apply ContinuousMap.ext
        intro x
        exact Subsingleton.elim _ _
      simpa only [he] using (Homotopic.refl
        (ContinuousMap.id (FiniteSimplicialJoin.Space (bouquetComplex [])))) }

private def sphereFamilyHomeomorph (ds : BouquetSpec) :
    (Σ i : Fin ds.length, FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val)) ≃ₜ
      (Σ i : Fin ds.length, EuclideanSphereJoin.StdSphere (ds.get i).val) where
  toEquiv := Equiv.sigmaCongrRight (fun i => (sphereHomeomorph (ds.get i).val).toEquiv)
  continuous_toFun := continuous_sigma fun i =>
    continuous_sigmaMk.comp (sphereHomeomorph (ds.get i).val).continuous
  continuous_invFun := continuous_sigma fun i =>
    continuous_sigmaMk.comp (sphereHomeomorph (ds.get i).val).symm.continuous

/-- An actual standard-sphere point, chosen by the finite-coordinate sphere identification. -/
def standardSphereBase (d : ℕ) : EuclideanSphereJoin.StdSphere d :=
  sphereHomeomorph d (spherePoint d)

abbrev StandardBouquetSource (ds : BouquetSpec) :=
  PUnit.{1} ⊕ (Σ i : Fin ds.length, EuclideanSphereJoin.StdSphere (ds.get i).val)

private def standardBouquetBases (ds : BouquetSpec) : Set (StandardBouquetSource ds) :=
  {z | Sum.elim (fun _ => True) (fun x => x.2 = standardSphereBase (ds.get x.1).val) z}

/-- The ordinary quotient bouquet of actual Euclidean spheres; an empty list is a point. -/
abbrev StandardBouquet (ds : BouquetSpec) :=
  FiniteConeUnionWedge.Collapse (standardBouquetBases ds)

private def sphereBouquetQuotientHomeomorph (ds : BouquetSpec) :
    CoordinateBouquetQuotient ds ≃ₜ StandardBouquet ds := by
  let h := (Homeomorph.refl PUnit.{1}).sumCongr (sphereFamilyHomeomorph ds)
  apply Homeomorph.Quotient.congr h
  intro z w
  change (z = w ∨ (z ∈ bouquetBases ds ∧ w ∈ bouquetBases ds)) ↔
    (h z = h w ∨ (h z ∈ standardBouquetBases ds ∧ h w ∈ standardBouquetBases ds))
  have hb (z : BouquetSource ds) : h z ∈ standardBouquetBases ds ↔ z ∈ bouquetBases ds := by
    rcases z with _ | ⟨i, x⟩
    · rfl
    · exact (sphereHomeomorph (ds.get i).val).injective.eq_iff
  rw [h.injective.eq_iff, hb, hb]

/-- The concrete sphere bouquet quotient and the finite-coordinate realization coincide topologically. -/
def standardBouquetHomeomorph (ds : BouquetSpec) :
    FiniteSimplicialJoin.Space (bouquetComplex ds) ≃ₜ StandardBouquet ds :=
  (bouquetQuotientHomeomorph ds).symm.trans (sphereBouquetQuotientHomeomorph ds)

/-- Disjoint tagged components. A family of empty lists is a family of distinct points. -/
abbrev NormalVertices (m : ℕ) (b : Fin m → BouquetSpec) := Σ i, BouquetVertices (b i)

def normalComplex (m : ℕ) (b : Fin m → BouquetSpec) :
    PreAbstractSimplicialComplex (NormalVertices m b) :=
  coproductComplex (fun i => bouquetComplex (b i))

private theorem normalVertex_face (m : ℕ) (b : Fin m → BouquetSpec) (i : Fin m) :
    ({⟨i, none⟩} : Finset (NormalVertices m b)) ∈ normalComplex m b := by
  apply (mem_coproductComplex (fun i => bouquetComplex (b i)) _).mpr
  exact ⟨i, {none}, bouquetVertex_face (b i), Finset.image_singleton _ _⟩

def normalPoint (m : ℕ) (b : Fin m → BouquetSpec) (i : Fin m) :
    FiniteSimplicialJoin.Space (normalComplex m b) :=
  FiniteVertexCylinder.vertexPoint _ ⟨i, none⟩ (normalVertex_face m b i)

def normalHomeomorph (m : ℕ) (b : Fin m → BouquetSpec) :
    FiniteSimplicialJoin.Space (normalComplex m b) ≃ₜ
      (Σ i : Fin m, FiniteSimplicialJoin.Space (bouquetComplex (b i))) :=
  (coproductHomeomorph (fun i => bouquetComplex (b i))).symm

def WPlus {V : Type*} [Fintype V] [DecidableEq V]
    (M : PreAbstractSimplicialComplex V) : Prop :=
  ∃ m : ℕ, ∃ _ : 0 < m, ∃ b : Fin m → BouquetSpec,
    Nonempty (FiniteSimplicialJoin.Space M ≃ₕ FiniteSimplicialJoin.Space (normalComplex m b))

private theorem normalPoint_embedding (m : ℕ) (b : Fin m → BouquetSpec) (i : Fin m) :
    (normalHomeomorph m b).symm ⟨i, bouquetPoint (b i)⟩ = normalPoint m b i := by
  apply Subtype.ext
  change coordinateLinear ⟨(@Sigma.mk (Fin m) (fun i => BouquetVertices (b i)) i),
      sigma_mk_injective⟩
    (Pi.single (none : BouquetVertices (b i)) 1) =
      Pi.single (⟨i, none⟩ : NormalVertices m b) 1
  exact coordinateLinear_single _ _

private def normalPath (m : ℕ) (b : Fin m → BouquetSpec)
    (x : FiniteSimplicialJoin.Space (normalComplex m b)) :
    Path x (normalPoint m b ((normalHomeomorph m b) x).1) := by
  let z := normalHomeomorph m b x
  let p := (bouquetPath (b z.1) z.2).map
    ((normalHomeomorph m b).symm.continuous.comp
      (@continuous_sigmaMk (Fin m)
        (fun i => FiniteSimplicialJoin.Space (bouquetComplex (b i)))
        (fun i => inferInstance) z.1))
  exact p.cast ((normalHomeomorph m b).symm_apply_apply x).symm
    (normalPoint_embedding m b z.1).symm

/-- Both actual native cylinder retractions are used; the image component is selected by the map. -/
private theorem based_normalization {V : Type*} [Fintype V] [DecidableEq V]
    (M : PreAbstractSimplicialComplex V) (hM : WPlus M)
    (a : V) (ha : ({a} : Finset V) ∈ M) :
    ∃ m : ℕ, ∃ hm : 0 < m, ∃ b : Fin m → BouquetSpec, ∃ i : Fin m,
      Nonempty (SingletonRetractionBasedInverse.BasedEquivalence
        (FiniteVertexCylinder.vertexPoint M a ha) (normalPoint m b i)) := by
  obtain ⟨m, hm, b, ⟨e⟩⟩ := hM
  let x := FiniteVertexCylinder.vertexPoint M a ha
  let z := e.toFun x
  let i := ((normalHomeomorph m b) z).1
  obtain ⟨E, _, _⟩ := SingletonRetractionBasedInverse.based_inverse x (normalPoint m b i)
    (nativeCylinder M a ha)
    (nativeCylinder (normalComplex m b) ⟨i, none⟩ (normalVertex_face m b i))
    e.toFun e.invFun e.left_inv.some e.right_inv.some (normalPath m b z)
  exact ⟨m, hm, b, i, ⟨E⟩⟩

section VertexGluing

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private abbrev GluedVertices (a : V) (b : W) := FiniteConeUnionWedge.Wedge a b

private instance (a : V) (b : W) : Fintype (GluedVertices a b) := Fintype.ofFinite _
private instance (a : V) (b : W) : DecidableEq (GluedVertices a b) := Classical.decEq _

private def glueLeft (a : V) (b : W) : V ↪ GluedVertices a b where
  toFun v := Quotient.mk _ (Sum.inl v)
  inj' := by
    intro v w h
    have h := Quotient.exact h
    change (Sum.inl v = Sum.inl w ∨
      ((Sum.inl v = Sum.inl a ∨ Sum.inl v = Sum.inr b) ∧
      (Sum.inl w = Sum.inl a ∨ Sum.inl w = Sum.inr b))) at h
    simp only [Sum.inl.injEq, Sum.inl_ne_inr, or_false] at h
    exact h.elim id (fun h => h.1.trans h.2.symm)

private def glueRight (a : V) (b : W) : W ↪ GluedVertices a b where
  toFun w := Quotient.mk _ (Sum.inr w)
  inj' := by
    intro v w h
    have h := Quotient.exact h
    change (Sum.inr v = Sum.inr w ∨
      ((Sum.inr v = Sum.inl a ∨ Sum.inr v = Sum.inr b) ∧
      (Sum.inr w = Sum.inl a ∨ Sum.inr w = Sum.inr b))) at h
    simp only [Sum.inr.injEq, Sum.inr_ne_inl, false_or] at h
    exact h.elim id (fun h => h.1.trans h.2.symm)

private theorem glue_cross (a : V) (b : W) (v : V) (w : W) :
    glueLeft a b v = glueRight a b w ↔ v = a ∧ w = b := by
  change Quotient.mk _ (Sum.inl v) = Quotient.mk _ (Sum.inr w) ↔ _
  rw [Quotient.eq]
  change (Sum.inl v = Sum.inr w ∨
    ((Sum.inl v = Sum.inl a ∨ Sum.inl v = Sum.inr b) ∧
    (Sum.inr w = Sum.inl a ∨ Sum.inr w = Sum.inr b))) ↔ _
  simp

private def vertexGluing (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    PreAbstractSimplicialComplex (GluedVertices a b) :=
  K.map (glueLeft a b) ⊔ L.map (glueRight a b)

private def gluedLeft (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    C(FiniteSimplicialJoin.Space K, FiniteSimplicialJoin.Space (vertexGluing K L a b)) :=
  (FiniteConeUnionWedge.realizationInclusion le_sup_left).comp
    ⟨coordinateHomeomorph K (glueLeft a b), (coordinateHomeomorph K (glueLeft a b)).continuous⟩

private def gluedRight (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    C(FiniteSimplicialJoin.Space L, FiniteSimplicialJoin.Space (vertexGluing K L a b)) :=
  (FiniteConeUnionWedge.realizationInclusion le_sup_right).comp
    ⟨coordinateHomeomorph L (glueRight a b), (coordinateHomeomorph L (glueRight a b)).continuous⟩

private theorem gluedLeft_injective (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    Function.Injective (gluedLeft K L a b) := by
  intro x y h
  apply (coordinateHomeomorph K (glueLeft a b)).injective
  exact Subtype.ext (congrArg (fun z : FiniteSimplicialJoin.Space
    (vertexGluing K L a b) => z.val) h)

private theorem gluedRight_injective (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    Function.Injective (gluedRight K L a b) := by
  intro x y h
  apply (coordinateHomeomorph L (glueRight a b)).injective
  exact Subtype.ext (congrArg (fun z : FiniteSimplicialJoin.Space
    (vertexGluing K L a b) => z.val) h)

private theorem glued_bases (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W)
    (ha : ({a} : Finset V) ∈ K) (hb : ({b} : Finset W) ∈ L) :
    gluedLeft K L a b (FiniteVertexCylinder.vertexPoint K a ha) =
      gluedRight K L a b (FiniteVertexCylinder.vertexPoint L b hb) := by
  apply Subtype.ext
  change coordinateLinear (glueLeft a b) (Pi.single a 1) =
    coordinateLinear (glueRight a b) (Pi.single b 1)
  rw [coordinateLinear_single, coordinateLinear_single, (glue_cross a b a b).mpr ⟨rfl, rfl⟩]

private theorem glued_intersection (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W)
    (ha : ({a} : Finset V) ∈ K) (hb : ({b} : Finset W) ∈ L)
    (x : FiniteSimplicialJoin.Space K) (y : FiniteSimplicialJoin.Space L)
    (h : gluedLeft K L a b x = gluedRight K L a b y) :
    x = FiniteVertexCylinder.vertexPoint K a ha ∧
      y = FiniteVertexCylinder.vertexPoint L b hb := by
  have hx : x = FiniteVertexCylinder.vertexPoint K a ha := by
    apply coordinates_eq_vertex x a ha
    intro v hv
    have he := congrArg (fun z : FiniteSimplicialJoin.Space (vertexGluing K L a b) =>
      z.val (glueLeft a b v)) h
    have hz : coordinateLinear (glueRight a b) y.val (glueLeft a b v) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      have hn : glueRight a b w ≠ glueLeft a b v :=
        fun hh => hv ((glue_cross a b v w).mp hh.symm).1
      simp [hn]
    change coordinateLinear (glueLeft a b) x.val (glueLeft a b v) =
      coordinateLinear (glueRight a b) y.val (glueLeft a b v) at he
    rwa [coordinateLinear_at, hz] at he
  refine ⟨hx, gluedRight_injective K L a b ?_⟩
  rw [← h, hx, glued_bases K L a b ha hb]

private def gluingSum (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    C(FiniteSimplicialJoin.Space K ⊕ FiniteSimplicialJoin.Space L,
      FiniteSimplicialJoin.Space (vertexGluing K L a b)) :=
  ⟨Sum.elim (gluedLeft K L a b) (gluedRight K L a b),
    (gluedLeft K L a b).continuous.sumElim (gluedRight K L a b).continuous⟩

private theorem gluingSum_surjective (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    Function.Surjective (gluingSum K L a b) := by
  intro z
  obtain ⟨s, hs, hz⟩ := z.property
  rcases hs with hs | hs
  · let w : FiniteSimplicialJoin.Space (K.map (glueLeft a b)) := ⟨z.val, s, hs, hz⟩
    refine ⟨Sum.inl ((coordinateHomeomorph K (glueLeft a b)).symm w), ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : FiniteSimplicialJoin.Space (K.map (glueLeft a b)) => z.val)
      ((coordinateHomeomorph K (glueLeft a b)).apply_symm_apply w)
  · let w : FiniteSimplicialJoin.Space (L.map (glueRight a b)) := ⟨z.val, s, hs, hz⟩
    refine ⟨Sum.inr ((coordinateHomeomorph L (glueRight a b)).symm w), ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : FiniteSimplicialJoin.Space (L.map (glueRight a b)) => z.val)
      ((coordinateHomeomorph L (glueRight a b)).apply_symm_apply w)

private theorem gluingSum_kernel (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W)
    (ha : ({a} : Finset V) ∈ K) (hb : ({b} : Finset W) ∈ L)
    (x y : FiniteSimplicialJoin.Space K ⊕ FiniteSimplicialJoin.Space L) :
    (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
      (FiniteVertexCylinder.vertexPoint K a ha) (FiniteVertexCylinder.vertexPoint L b hb))).r
      x y ↔ gluingSum K L a b x = gluingSum K L a b y := by
  constructor
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · have h (z) (hz : z ∈ FiniteConeUnionWedge.wedgePoints
          (FiniteVertexCylinder.vertexPoint K a ha) (FiniteVertexCylinder.vertexPoint L b hb)) :
          gluingSum K L a b z = gluedLeft K L a b (FiniteVertexCylinder.vertexPoint K a ha) := by
        rcases hz with rfl | rfl
        · rfl
        · exact (glued_bases K L a b ha hb).symm
      exact (h x hx).trans (h y hy).symm
  · intro h
    rcases x with x | x <;> rcases y with y | y
    · exact Or.inl (congrArg Sum.inl (gluedLeft_injective K L a b h))
    · obtain ⟨rfl, rfl⟩ := glued_intersection K L a b ha hb x y h
      exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    · obtain ⟨rfl, rfl⟩ := glued_intersection K L a b ha hb y x h.symm
      exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
    · exact Or.inl (congrArg Sum.inr (gluedRight_injective K L a b h))

/-- The quotient wedge is homeomorphic to the actual finite coordinate vertex gluing. -/
private def vertexGluingHomeomorph (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W)
    (ha : ({a} : Finset V) ∈ K) (hb : ({b} : Finset W) ∈ L) :
    FiniteConeUnionWedge.Wedge (FiniteVertexCylinder.vertexPoint K a ha)
      (FiniteVertexCylinder.vertexPoint L b hb) ≃ₜ
      FiniteSimplicialJoin.Space (vertexGluing K L a b) := by
  letI := FiniteSimplicialJoin.realizationCompactSpace K
  letI := FiniteSimplicialJoin.realizationCompactSpace L
  have hq : IsQuotientMap (gluingSum K L a b) :=
    (gluingSum K L a b).continuous.isClosedMap.isQuotientMap
      (gluingSum K L a b).continuous (gluingSum_surjective K L a b)
  exact (Homeomorph.Quotient.congrRight (gluingSum_kernel K L a b ha hb)).trans
    (Topology.IsQuotientMap.homeomorph (f := gluingSum K L a b) hq)

/- Concrete carrier for selected-component gluing. -/
private abbrev SelectedGluedVertices (a : V) (b : W) :=
  FiniteConeUnionWedge.Wedge a b

private def selectedVertexGluing (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    PreAbstractSimplicialComplex (SelectedGluedVertices a b) :=
  vertexGluing K L a b

end VertexGluing

end D5.S3.Geometry.FiniteComponentClosure
