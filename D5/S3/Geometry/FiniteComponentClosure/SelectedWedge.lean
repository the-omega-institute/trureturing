/- GID: D5/S3/Geometry/FiniteComponentClosure/SelectedWedge
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteComponentClosure/SelectedWedge
   mirror-E: none(waiver:finite-component-closure)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: Selected-vertex wedge closure with full relative inverse homotopies. -/
import D5.S3.Geometry.FiniteComponentClosure.ConeSplits

noncomputable section
open Set Finset Topology ContinuousMap
open scoped BigOperators unitInterval

namespace D5.S3.Geometry.FiniteComponentClosure

open private
  D5.S3.Geometry.FiniteComponentClosure.nativeCylinder
  from D5.S3.Geometry.FiniteComponentClosure.Transport

open private
  D5.S3.Geometry.FiniteComponentClosure.bouquetVertex_face
  D5.S3.Geometry.FiniteComponentClosure.bouquetBases
  D5.S3.Geometry.FiniteComponentClosure.normalVertex_face
  D5.S3.Geometry.FiniteComponentClosure.normalPoint_embedding
  D5.S3.Geometry.FiniteComponentClosure.normalPath
  D5.S3.Geometry.FiniteComponentClosure.based_normalization
  D5.S3.Geometry.FiniteComponentClosure.glueLeft
  D5.S3.Geometry.FiniteComponentClosure.vertexGluing
  D5.S3.Geometry.FiniteComponentClosure.vertexGluingHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.selectedVertexGluing
  from D5.S3.Geometry.FiniteComponentClosure.Models

open private
  D5.S3.Geometry.FiniteComponentClosure.wedgeHomeomorph
  from D5.S3.Geometry.FiniteComponentClosure.ConeSplits

section BouquetConcatenation

private def collapseSumHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) (D : Set Y) (a : X) (b : Y) (ha : a ∈ C) (hb : b ∈ D) :
    FiniteConeUnionWedge.Wedge
      (Quotient.mk (FiniteConeUnionWedge.subsetSetoid C) a)
      (Quotient.mk (FiniteConeUnionWedge.subsetSetoid D) b) ≃ₜ
      FiniteConeUnionWedge.Collapse {z : X ⊕ Y | Sum.elim (· ∈ C) (· ∈ D) z} := by
  let P : FiniteConeUnionWedge.CollapseCover a b
      {z : X ⊕ Y | Sum.elim (· ∈ C) (· ∈ D) z} := {
    left := ⟨Sum.inl, continuous_inl⟩
    right := ⟨Sum.inr, continuous_inr⟩
    left_injective := Sum.inl_injective
    right_injective := Sum.inr_injective
    left_closed := isClosedMap_inl
    right_closed := isClosedMap_inr
    covers := by rintro (x | y); exact ⟨Sum.inl x, rfl⟩; exact ⟨Sum.inr y, rfl⟩
    overlap := by intro x y h; cases h
    left_base := ha
    right_base := hb }
  exact P.quotientWedgeHomeomorph

private def anchorCollapseHomeomorph {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z]
    (a : A) (B : Set Z) :
    FiniteConeUnionWedge.Collapse {z : A ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z} ≃ₜ
      FiniteConeUnionWedge.Collapse
        {z : PUnit.{1} ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z} := by
  let f : A ⊕ Z → PUnit.{1} ⊕ Z := Sum.map (fun _ => PUnit.unit) id
  let g : PUnit.{1} ⊕ Z → A ⊕ Z := Sum.map (fun _ => a) id
  have hf : ∀ z w, (FiniteConeUnionWedge.subsetSetoid
        {z : A ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z}).r z w →
      (FiniteConeUnionWedge.subsetSetoid
        {z : PUnit.{1} ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z}).r (f z) (f w) := by
    rintro z w (rfl | ⟨hz, hw⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨by cases z <;> exact hz, by cases w <;> exact hw⟩
  have hg : ∀ z w, (FiniteConeUnionWedge.subsetSetoid
        {z : PUnit.{1} ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z}).r z w →
      (FiniteConeUnionWedge.subsetSetoid
        {z : A ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z}).r (g z) (g w) := by
    rintro z w (rfl | ⟨hz, hw⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨by cases z <;> exact hz, by cases w <;> exact hw⟩
  exact {
    toFun := Quotient.map' f hf
    invFun := Quotient.map' g hg
    left_inv := by
      intro z; induction z using Quotient.inductionOn with
      | h z =>
        apply Quotient.sound
        cases z
        · exact Or.inr ⟨True.intro, True.intro⟩
        · exact Or.inl rfl
    right_inv := by
      intro z; induction z using Quotient.inductionOn with
      | h z =>
        apply Quotient.sound
        cases z with
        | inl x => exact Or.inl (congrArg Sum.inl (Subsingleton.elim _ _))
        | inr x => exact Or.inl rfl
    continuous_toFun := (continuous_const.sumMap continuous_id).quotient_map' hf
    continuous_invFun := (continuous_const.sumMap continuous_id).quotient_map' hg }

private def sphereCast {d e : ℕ} (h : d = e) :
    FiniteSimplicialJoin.Space (sphereComplex d) ≃ₜ
      FiniteSimplicialJoin.Space (sphereComplex e) := by
  subst e
  exact Homeomorph.refl _

private theorem sphereCast_point {d e : ℕ} (h : d = e) :
    sphereCast h (spherePoint d) = spherePoint e := by
  subst e
  rfl

private abbrev SphereFamily (ds : BouquetSpec) :=
  Σ i : Fin ds.length, FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val)

private def appendIndex (ds es : BouquetSpec) :
    Fin ds.length ⊕ Fin es.length ≃ Fin (ds ++ es).length :=
  finSumFinEquiv.trans (finCongr (by simp))

private def appendDimension (ds es : BouquetSpec) : Fin ds.length ⊕ Fin es.length → ℕ :=
  Sum.elim (fun i => (ds.get i).val) (fun i => (es.get i).val)

private theorem appendDimension_eq (ds es : BouquetSpec) (i : Fin ds.length ⊕ Fin es.length) :
    appendDimension ds es i = ((ds ++ es).get (appendIndex ds es i)).val := by
  cases i with
  | inl i =>
    change ds[i.val].val = (ds ++ es)[i.val].val
    rw [List.getElem_append_left i.isLt]
  | inr i =>
    change es[i.val].val = (ds ++ es)[ds.length + i.val].val
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp

private def appendFamilyEquiv (ds es : BouquetSpec) :
    SphereFamily ds ⊕ SphereFamily es ≃ SphereFamily (ds ++ es) :=
  (Equiv.sumSigmaDistrib (fun i =>
    FiniteSimplicialJoin.Space (sphereComplex (appendDimension ds es i)))).symm.trans
    (Equiv.sigmaCongr (appendIndex ds es) (fun i =>
      (sphereCast (appendDimension_eq ds es i)).toEquiv))

private def appendFamilyHomeomorph (ds es : BouquetSpec) :
    SphereFamily ds ⊕ SphereFamily es ≃ₜ SphereFamily (ds ++ es) := by
  letI (i : Fin ds.length) : CompactSpace
      (FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val)) :=
    FiniteSimplicialJoin.realizationCompactSpace _
  letI (i : Fin es.length) : CompactSpace
      (FiniteSimplicialJoin.Space (sphereComplex (es.get i).val)) :=
    FiniteSimplicialJoin.realizationCompactSpace _
  apply Continuous.homeoOfEquivCompactToT2 (f := appendFamilyEquiv ds es)
  have hl : Continuous (fun z : SphereFamily ds => appendFamilyEquiv ds es (Sum.inl z)) := by
    apply continuous_sigma
    intro i
    exact (@continuous_sigmaMk _ (fun k : Fin (ds ++ es).length =>
      FiniteSimplicialJoin.Space (sphereComplex ((ds ++ es).get k).val)) _
        (appendIndex ds es (Sum.inl i))).comp
      (sphereCast (appendDimension_eq ds es (Sum.inl i))).continuous
  have hr : Continuous (fun z : SphereFamily es => appendFamilyEquiv ds es (Sum.inr z)) := by
    apply continuous_sigma
    intro i
    exact (@continuous_sigmaMk _ (fun k : Fin (ds ++ es).length =>
      FiniteSimplicialJoin.Space (sphereComplex ((ds ++ es).get k).val)) _
        (appendIndex ds es (Sum.inr i))).comp
      (sphereCast (appendDimension_eq ds es (Sum.inr i))).continuous
  convert Continuous.sumElim hl hr using 1
  funext z
  cases z <;> rfl

private theorem appendFamily_base (ds es : BouquetSpec) (z : SphereFamily ds ⊕ SphereFamily es) :
    (appendFamilyHomeomorph ds es z).2 =
      spherePoint ((ds ++ es).get (appendFamilyHomeomorph ds es z).1).val ↔
    Sum.elim (fun x : SphereFamily ds => x.2 = spherePoint (ds.get x.1).val)
      (fun x : SphereFamily es => x.2 = spherePoint (es.get x.1).val) z := by
  have hc {d e : ℕ} (h : d = e) (x : FiniteSimplicialJoin.Space (sphereComplex d)) :
      sphereCast h x = spherePoint e ↔ x = spherePoint d := by
    subst e
    rfl
  rcases z with ⟨i, x⟩ | ⟨i, x⟩
  · convert hc (appendDimension_eq ds es (Sum.inl i)) x using 1 <;> rfl
  · convert hc (appendDimension_eq ds es (Sum.inr i)) x using 1 <;> rfl

private def bouquetSourceShuffle (ds es : BouquetSpec) :
    BouquetSource ds ⊕ BouquetSource es ≃ₜ
      (PUnit.{1} ⊕ PUnit.{1}) ⊕ SphereFamily (ds ++ es) :=
  (Homeomorph.sumSumSumComm PUnit.{1} (SphereFamily ds) PUnit.{1} (SphereFamily es)).trans
    ((Homeomorph.refl _).sumCongr (appendFamilyHomeomorph ds es))

private def bouquetAppendHomeomorph (ds es : BouquetSpec) :
    FiniteConeUnionWedge.Wedge (bouquetPoint ds) (bouquetPoint es) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex (ds ++ es)) := by
  let qd : CoordinateBouquetQuotient ds := Quotient.mk _ (Sum.inl PUnit.unit)
  let qe : CoordinateBouquetQuotient es := Quotient.mk _ (Sum.inl PUnit.unit)
  let hd := bouquetQuotientHomeomorph ds
  let he := bouquetQuotientHomeomorph es
  let first : FiniteConeUnionWedge.Wedge (bouquetPoint ds) (bouquetPoint es) ≃ₜ
      FiniteConeUnionWedge.Wedge qd qe :=
    (wedgeHomeomorph qd qe hd he).symm
  let h := bouquetSourceShuffle ds es
  let B : Set (SphereFamily (ds ++ es)) :=
    {z | z.2 = spherePoint ((ds ++ es).get z.1).val}
  let middle : FiniteConeUnionWedge.Collapse
      {z : BouquetSource ds ⊕ BouquetSource es |
        Sum.elim (· ∈ bouquetBases ds) (· ∈ bouquetBases es) z} ≃ₜ
      FiniteConeUnionWedge.Collapse
        {z : (PUnit.{1} ⊕ PUnit.{1}) ⊕ SphereFamily (ds ++ es) |
          Sum.elim (fun _ => True) (· ∈ B) z} := by
    apply Homeomorph.Quotient.congr h
    intro z w
    have hb (z : BouquetSource ds ⊕ BouquetSource es) :
        Sum.elim (fun _ => True) (· ∈ B) (h z) ↔
        Sum.elim (· ∈ bouquetBases ds) (· ∈ bouquetBases es) z := by
      rcases z with (u | x) | (v | y)
      · rfl
      · exact appendFamily_base ds es (Sum.inl x)
      · rfl
      · exact appendFamily_base ds es (Sum.inr y)
    change (z = w ∨ (_ ∧ _)) ↔ (h z = h w ∨ (_ ∧ _))
    simp only [Set.mem_setOf_eq]
    rw [h.injective.eq_iff, hb, hb]
  exact first.trans
    ((collapseSumHomeomorph (bouquetBases ds) (bouquetBases es)
      (Sum.inl PUnit.unit) (Sum.inl PUnit.unit) True.intro True.intro).trans
      (middle.trans ((anchorCollapseHomeomorph (Sum.inl PUnit.unit) B).trans
        (bouquetQuotientHomeomorph (ds ++ es)))))

/- The connected selected-component carrier is now consumed by the actual
  vertex-gluing quotient and the actual bouquet concatenation quotient. -/
private def connectedVertexGluingHomeomorph (ds es : BouquetSpec) :
    FiniteSimplicialJoin.Space
        (selectedVertexGluing (bouquetComplex ds) (bouquetComplex es) none none) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex (ds ++ es)) := by
  exact (vertexGluingHomeomorph (bouquetComplex ds) (bouquetComplex es)
      none none (bouquetVertex_face ds) (bouquetVertex_face es)).symm.trans
    (bouquetAppendHomeomorph ds es)

/- The first consumed selected-component step.  The two native based packets
  choose the actual normal-form components containing the supplied vertices;
  basedWedgeEquivalence then performs the quotient wedge replacement on the
  live carrier.  The normal spaces remain finite coproduct realizations, so
  every unselected component (including point components) stays present. -/
private def selectedComponentWedgeBased {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (hK : WPlus K) (hL : WPlus L)
    (a : V) (ha : ({a} : Finset V) ∈ K)
    (b : W) (hb : ({b} : Finset W) ∈ L) :
    ∃ m : ℕ, ∃ hm : 0 < m, ∃ p : Fin m → BouquetSpec, ∃ i : Fin m,
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ q : Fin n → BouquetSpec, ∃ j : Fin n,
      Nonempty (SingletonRetractionBasedInverse.BasedEquivalence
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
          (FiniteVertexCylinder.vertexPoint K a ha)
          (FiniteVertexCylinder.vertexPoint L b hb)))
          (Sum.inl (FiniteVertexCylinder.vertexPoint K a ha)))
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
          (normalPoint m p i) (normalPoint n q j))) (Sum.inl (normalPoint m p i)))) := by
  obtain ⟨m, hm, p, i, ⟨E⟩⟩ := based_normalization K hK a ha
  obtain ⟨n, hn, q, j, ⟨F⟩⟩ := based_normalization L hL b hb
  exact ⟨m, hm, p, i, n, hn, q, j,
    ⟨FiniteConeUnionWedge.basedWedgeEquivalence E F⟩⟩

private def selectedComponentWedgeCarrier {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (hK : WPlus K) (hL : WPlus L)
    (a : V) (ha : ({a} : Finset V) ∈ K)
    (b : W) (hb : ({b} : Finset W) ∈ L) :
    ∃ m : ℕ, ∃ hm : 0 < m, ∃ p : Fin m → BouquetSpec, ∃ i : Fin m,
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ q : Fin n → BouquetSpec, ∃ j : Fin n,
      Nonempty (SingletonRetractionBasedInverse.BasedEquivalence
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
          (FiniteVertexCylinder.vertexPoint K a ha)
          (FiniteVertexCylinder.vertexPoint L b hb)))
          (Sum.inl (FiniteVertexCylinder.vertexPoint K a ha)))
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
          (normalPoint m p i) (normalPoint n q j))) (Sum.inl (normalPoint m p i)))) ∧
      Nonempty (FiniteConeUnionWedge.Wedge
          (normalPoint m p i) (normalPoint n q j) ≃ₜ
        FiniteSimplicialJoin.Space
          (selectedVertexGluing (normalComplex m p) (normalComplex n q)
            ⟨i, none⟩ ⟨j, none⟩)) := by
  obtain ⟨m, hm, p, i, n, hn, q, j, hE⟩ :=
    selectedComponentWedgeBased K L hK hL a ha b hb
  have hi : ({⟨i, none⟩} : Finset (NormalVertices m p)) ∈ normalComplex m p :=
    normalVertex_face m p i
  have hj : ({⟨j, none⟩} : Finset (NormalVertices n q)) ∈ normalComplex n q :=
    normalVertex_face n q j
  refine ⟨m, hm, p, i, n, hn, q, j, hE, ?_⟩
  exact ⟨by
    convert vertexGluingHomeomorph (normalComplex m p) (normalComplex n q)
      ⟨i, none⟩ ⟨j, none⟩ hi hj using 1 <;> rfl⟩

private def sigmaSplitHomeomorph {A : Type*} [DecidableEq A]
    (X : A → Type*) [∀ i, TopologicalSpace (X i)] (a : A) :
    (Σ i, X i) ≃ₜ X a ⊕ (Σ i : {i : A // i ≠ a}, X i.val) where
  toFun z := if h : z.1 = a then Sum.inl (h ▸ z.2) else Sum.inr ⟨⟨z.1, h⟩, z.2⟩
  invFun := Sum.elim (Sigma.mk a) (fun z => ⟨z.1.val, z.2⟩)
  left_inv := by
    rintro ⟨i, x⟩
    by_cases h : i = a
    · subst i; simp
    · simp [h]
  right_inv := by
    rintro (x | ⟨⟨i, hi⟩, x⟩)
    · simp
    · simp [hi]
  continuous_toFun := by
    apply continuous_sigma
    intro i
    by_cases h : i = a
    · subst i; simpa using (continuous_inl : Continuous (Sum.inl : X a → _))
    · have hc : Continuous (fun x : X i =>
          (⟨⟨i, h⟩, x⟩ : Σ k : {i : A // i ≠ a}, X k.val)) :=
          @continuous_sigmaMk {i : A // i ≠ a} (fun k => X k.val) _ ⟨i, h⟩
      simp only [dif_neg h]
      exact continuous_inr.comp hc
  continuous_invFun := continuous_sigmaMk.sumElim (continuous_sigma fun _ => continuous_sigmaMk)

private def collapseLeftHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (C : Set X) :
    FiniteConeUnionWedge.Collapse
      {z : X ⊕ Y | Sum.elim (· ∈ C) (fun _ => False) z} ≃ₜ
      FiniteConeUnionWedge.Collapse C ⊕ Y := by
  let f : X ⊕ Y → FiniteConeUnionWedge.Collapse C ⊕ Y := Sum.map (Quotient.mk _) id
  have hf : ∀ z w, (FiniteConeUnionWedge.subsetSetoid
      {z : X ⊕ Y | Sum.elim (· ∈ C) (fun _ => False) z}).r z w → f z = f w := by
    rintro z w (rfl | ⟨hz, hw⟩)
    · rfl
    · rcases z with x | y <;> rcases w with x' | y'
      · exact congrArg Sum.inl (Quotient.sound (Or.inr ⟨hz, hw⟩))
      · exact hw.elim
      · exact hz.elim
      · exact hz.elim
  let g : C(FiniteConeUnionWedge.Collapse C,
      FiniteConeUnionWedge.Collapse
        {z : X ⊕ Y | Sum.elim (· ∈ C) (fun _ => False) z}) :=
    ⟨Quotient.lift (fun x => Quotient.mk _ (Sum.inl x)) (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · rfl
      · exact Quotient.sound (Or.inr ⟨hx, hy⟩)),
      (continuous_quotient_mk'.comp continuous_inl).quotient_lift _⟩
  exact {
    toFun := Quotient.lift f hf
    invFun := Sum.elim g (fun y => Quotient.mk _ (Sum.inr y))
    left_inv := by
      intro z
      induction z using Quotient.inductionOn with
      | h z => cases z <;> rfl
    right_inv := by
      rintro (x | y)
      · induction x using Quotient.inductionOn with | h x => rfl
      · rfl
    continuous_toFun := (continuous_quotient_mk'.sumMap continuous_id).quotient_lift _
    continuous_invFun := g.continuous.sumElim (continuous_quotient_mk'.comp continuous_inr) }

private def wedgeExtrasHomeomorph {X Y U V : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace U] [TopologicalSpace V]
    (a : X) (b : Y) :
    FiniteConeUnionWedge.Wedge (Sum.inl a : X ⊕ U) (Sum.inl b : Y ⊕ V) ≃ₜ
      FiniteConeUnionWedge.Wedge a b ⊕ (U ⊕ V) := by
  let h := Homeomorph.sumSumSumComm X U Y V
  refine (Homeomorph.Quotient.congr h ?_).trans
    (collapseLeftHomeomorph (Y := U ⊕ V) (FiniteConeUnionWedge.wedgePoints a b))
  intro z w
  have hb (z : (X ⊕ U) ⊕ (Y ⊕ V)) :
      Sum.elim (· ∈ FiniteConeUnionWedge.wedgePoints a b) (fun _ => False) (h z) ↔
        z ∈ FiniteConeUnionWedge.wedgePoints (Sum.inl a) (Sum.inl b) := by
    rcases z with (x | u) | (y | v) <;>
      simp [h, Homeomorph.sumSumSumComm, FiniteConeUnionWedge.wedgePoints]
  change (z = w ∨ (_ ∧ _)) ↔ (h z = h w ∨ (_ ∧ _))
  simp only [Set.mem_setOf_eq]
  rw [h.injective.eq_iff, hb, hb]

private abbrev MergedIndex {m n : ℕ} (i : Fin m) (j : Fin n) :=
  Unit ⊕ ({k : Fin m // k ≠ i} ⊕ {l : Fin n // l ≠ j})

private def mergedSpec {m n : ℕ} (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec)
    (i : Fin m) (j : Fin n) : MergedIndex i j → BouquetSpec :=
  Sum.elim (fun _ => p i ++ q j) (Sum.elim (fun k => p k.val) (fun l => q l.val))

private theorem mergedIndex_card {m n : ℕ} (i : Fin m) (j : Fin n) :
    Fintype.card (MergedIndex i j) = m + n - 1 := by
  have hm := i.isLt
  have hn := j.isLt
  have hmi : Fintype.card {k : Fin m // k ≠ i} = m - 1 := by
    simpa using Fintype.card_subtype_compl (fun k : Fin m => k = i)
  have hnj : Fintype.card {l : Fin n // l ≠ j} = n - 1 := by
    simpa using Fintype.card_subtype_compl (fun l : Fin n => l = j)
  simp only [MergedIndex, Fintype.card_sum, Fintype.card_unit, hmi, hnj]
  omega

private def mergedEnumeration {m n : ℕ} (i : Fin m) (j : Fin n) :
    MergedIndex i j ≃ Fin (m + n - 1) :=
  (Fintype.equivFin _).trans (finCongr (mergedIndex_card i j))

/-- Selected bouquets concatenate; every other component retains its full sphere list. -/
def selectedWedgeSpec {m n : ℕ} (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec)
    (i : Fin m) (j : Fin n) : Fin (m + n - 1) → BouquetSpec :=
  fun k => mergedSpec p q i j ((mergedEnumeration i j).symm k)

private def mergedSumHomeomorph {m n : ℕ} (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec)
    (i : Fin m) (j : Fin n) :
    (FiniteSimplicialJoin.Space (bouquetComplex (p i ++ q j)) ⊕
      ((Σ k : {k : Fin m // k ≠ i}, FiniteSimplicialJoin.Space (bouquetComplex (p k.val))) ⊕
       (Σ l : {l : Fin n // l ≠ j}, FiniteSimplicialJoin.Space (bouquetComplex (q l.val))))) ≃ₜ
    (Σ k : MergedIndex i j, FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) where
  toFun := Sum.elim (fun x => ⟨Sum.inl (), x⟩)
    (Sum.elim (fun x => ⟨Sum.inr (Sum.inl x.1), x.2⟩)
      (fun y => ⟨Sum.inr (Sum.inr y.1), y.2⟩))
  invFun z := match z with
    | ⟨Sum.inl _, x⟩ => Sum.inl x
    | ⟨Sum.inr (Sum.inl k), x⟩ => Sum.inr (Sum.inl ⟨k, x⟩)
    | ⟨Sum.inr (Sum.inr l), x⟩ => Sum.inr (Sum.inr ⟨l, x⟩)
  left_inv := by rintro (x | (⟨k, x⟩ | ⟨l, x⟩)) <;> rfl
  right_inv := by rintro ⟨(_ | (k | l)), x⟩ <;> rfl
  continuous_toFun := by
    apply Continuous.sumElim
    · exact @continuous_sigmaMk (MergedIndex i j) (fun k =>
        FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) _ (Sum.inl ())
    · apply Continuous.sumElim
      · apply continuous_sigma
        intro k
        exact @continuous_sigmaMk (MergedIndex i j) (fun k =>
          FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) _
            (Sum.inr (Sum.inl k))
      · apply continuous_sigma
        intro l
        exact @continuous_sigmaMk (MergedIndex i j) (fun k =>
          FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) _
            (Sum.inr (Sum.inr l))
  continuous_invFun := by
    apply continuous_sigma
    rintro (_ | (k | l))
    · exact continuous_inl
    · exact continuous_inr.comp (continuous_inl.comp continuous_sigmaMk)
    · exact continuous_inr.comp (continuous_inr.comp continuous_sigmaMk)

private def bouquetListCast {ds es : BouquetSpec} (h : ds = es) :
    FiniteSimplicialJoin.Space (bouquetComplex ds) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex es) := by
  subst es
  exact Homeomorph.refl _

private def mergedReindexHomeomorph {m n : ℕ}
    (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec) (i : Fin m) (j : Fin n) :
    (Σ k : MergedIndex i j, FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) ≃ₜ
      (Σ k : Fin (m + n - 1), FiniteSimplicialJoin.Space
        (bouquetComplex (selectedWedgeSpec p q i j k))) := by
  let e := mergedEnumeration i j
  let h (k : MergedIndex i j) := bouquetListCast
    (congrArg (mergedSpec p q i j) (e.symm_apply_apply k).symm)
  letI (k : MergedIndex i j) : CompactSpace
      (FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) :=
    FiniteSimplicialJoin.realizationCompactSpace _
  apply Continuous.homeoOfEquivCompactToT2
    (f := Equiv.sigmaCongr e (fun k => (h k).toEquiv))
  apply continuous_sigma
  intro k
  exact (@continuous_sigmaMk _ (fun l : Fin (m + n - 1) =>
    FiniteSimplicialJoin.Space (bouquetComplex (selectedWedgeSpec p q i j l))) _ (e k)).comp
      (h k).continuous

private def normalWedgeHomeomorph {m n : ℕ}
    (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec) (i : Fin m) (j : Fin n) :
    FiniteConeUnionWedge.Wedge (normalPoint m p i) (normalPoint n q j) ≃ₜ
      FiniteSimplicialJoin.Space (normalComplex (m + n - 1) (selectedWedgeSpec p q i j)) := by
  let hp := (normalHomeomorph m p).trans
    (sigmaSplitHomeomorph (fun k => FiniteSimplicialJoin.Space (bouquetComplex (p k))) i)
  let hq := (normalHomeomorph n q).trans
    (sigmaSplitHomeomorph (fun l => FiniteSimplicialJoin.Space (bouquetComplex (q l))) j)
  have hpi : hp (normalPoint m p i) = Sum.inl (bouquetPoint (p i)) := by
    rw [← normalPoint_embedding m p i]
    simp [hp, sigmaSplitHomeomorph]
  have hqj : hq (normalPoint n q j) = Sum.inl (bouquetPoint (q j)) := by
    rw [← normalPoint_embedding n q j]
    simp [hq, sigmaSplitHomeomorph]
  let first := wedgeHomeomorph (normalPoint m p i) (normalPoint n q j) hp hq
  rw [hpi, hqj] at first
  exact first.trans ((wedgeExtrasHomeomorph (bouquetPoint (p i)) (bouquetPoint (q j))).trans
    (((bouquetAppendHomeomorph (p i) (q j)).sumCongr (Homeomorph.refl _)).trans
      ((mergedSumHomeomorph p q i j).trans ((mergedReindexHomeomorph p q i j).trans
        (normalHomeomorph (m + n - 1) (selectedWedgeSpec p q i j)).symm))))

/-- The finite vertex set formed by identifying exactly the two selected vertices. -/
abbrev VertexWedgeVertices {V W : Type*} (a : V) (b : W) :=
  FiniteConeUnionWedge.Wedge a b

instance vertexWedgeVerticesFintype {V W : Type*} [Fintype V] [Fintype W] (a : V) (b : W) :
    Fintype (VertexWedgeVertices a b) := Fintype.ofFinite _

instance vertexWedgeVerticesDecidableEq {V W : Type*} (a : V) (b : W) :
    DecidableEq (VertexWedgeVertices a b) := Classical.decEq _

/-- The actual simplicial vertex wedge, rather than a homotopy-type surrogate. -/
def vertexWedgeComplex {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    PreAbstractSimplicialComplex (VertexWedgeVertices a b) := vertexGluing K L a b

private theorem vertexWedge_vertex {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (a : V) (b : W) (ha : ({a} : Finset V) ∈ K) :
    ({Quotient.mk _ (Sum.inl a)} : Finset (VertexWedgeVertices a b)) ∈
      vertexWedgeComplex K L a b := by
  apply Or.inl
  refine ⟨{a}, ha, ?_⟩
  change Finset.image (glueLeft a b) {a} = _
  rw [Finset.image_singleton]
  rfl

/-- The common actual vertex in the native finite wedge realization. -/
def vertexWedgePoint {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (a : V) (b : W) (ha : ({a} : Finset V) ∈ K) :
    FiniteSimplicialJoin.Space (vertexWedgeComplex K L a b) :=
  FiniteVertexCylinder.vertexPoint _ _ (vertexWedge_vertex K L a b ha)

/-- Complete selected-component closure data, including both relative inverse homotopies. -/
structure SelectedVertexWedgeClosure {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (a : V) (ha : ({a} : Finset V) ∈ K) (b : W) (hb : ({b} : Finset W) ∈ L) where
  leftCount : ℕ
  leftPositive : 0 < leftCount
  leftSpec : Fin leftCount → BouquetSpec
  leftSelected : Fin leftCount
  rightCount : ℕ
  rightPositive : 0 < rightCount
  rightSpec : Fin rightCount → BouquetSpec
  rightSelected : Fin rightCount
  leftNormalization : SingletonRetractionBasedInverse.BasedEquivalence
    (FiniteVertexCylinder.vertexPoint K a ha) (normalPoint leftCount leftSpec leftSelected)
  rightNormalization : SingletonRetractionBasedInverse.BasedEquivalence
    (FiniteVertexCylinder.vertexPoint L b hb) (normalPoint rightCount rightSpec rightSelected)
  normalization : SingletonRetractionBasedInverse.BasedEquivalence
    (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
      (FiniteVertexCylinder.vertexPoint K a ha) (FiniteVertexCylinder.vertexPoint L b hb)))
      (Sum.inl (FiniteVertexCylinder.vertexPoint K a ha)))
    (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
      (normalPoint leftCount leftSpec leftSelected) (normalPoint rightCount rightSpec rightSelected)))
      (Sum.inl (normalPoint leftCount leftSpec leftSelected)))
  outputComponent : Fin (leftCount + rightCount - 1)
  equivalence : SingletonRetractionBasedInverse.BasedEquivalence
    (vertexWedgePoint K L a b ha)
    (normalPoint (leftCount + rightCount - 1)
      (selectedWedgeSpec leftSpec rightSpec leftSelected rightSelected) outputComponent)

  wplus : WPlus (vertexWedgeComplex K L a b)

/-- WPlus is closed under an actual wedge at any two existing vertices, preserving point components. -/
def selectedVertexWedgeClosure {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (hK : WPlus K) (hL : WPlus L)
    (a : V) (ha : ({a} : Finset V) ∈ K) (b : W) (hb : ({b} : Finset W) ∈ L) :
    SelectedVertexWedgeClosure K L a ha b hb := by
  have h : Nonempty (SelectedVertexWedgeClosure K L a ha b hb) := by
    obtain ⟨m, hm, p, i, ⟨EL⟩⟩ := based_normalization K hK a ha
    obtain ⟨n, hn, q, j, ⟨ER⟩⟩ := based_normalization L hL b hb
    let E := FiniteConeUnionWedge.basedWedgeEquivalence EL ER
    let eW : FiniteConeUnionWedge.Wedge (FiniteVertexCylinder.vertexPoint K a ha)
        (FiniteVertexCylinder.vertexPoint L b hb) ≃ₕ
        FiniteConeUnionWedge.Wedge (normalPoint m p i) (normalPoint n q j) := {
      toFun := E.forward
      invFun := E.backward
      left_inv := ⟨E.left.toHomotopy⟩
      right_inv := ⟨E.right.toHomotopy⟩ }
    let e := ((vertexGluingHomeomorph K L a b ha hb).symm.toHomotopyEquiv.trans eW).trans
      (normalWedgeHomeomorph p q i j).toHomotopyEquiv
    let x := vertexWedgePoint K L a b ha
    let k := (normalHomeomorph (m + n - 1) (selectedWedgeSpec p q i j) (e.toFun x)).1
    obtain ⟨F, _, _⟩ := SingletonRetractionBasedInverse.based_inverse x
      (normalPoint (m + n - 1) (selectedWedgeSpec p q i j) k)
      (nativeCylinder (vertexWedgeComplex K L a b) _ (vertexWedge_vertex K L a b ha))
      (nativeCylinder (normalComplex (m + n - 1) (selectedWedgeSpec p q i j)) ⟨k, none⟩
        (normalVertex_face _ _ k)) e.toFun e.invFun e.left_inv.some e.right_inv.some
      (normalPath _ _ (e.toFun x))
    refine ⟨⟨m, hm, p, i, n, hn, q, j, EL, ER, E, k, F, ?_⟩⟩
    exact ⟨m + n - 1, by omega, selectedWedgeSpec p q i j, ⟨e⟩⟩
  exact Classical.choice h

end BouquetConcatenation

end D5.S3.Geometry.FiniteComponentClosure
