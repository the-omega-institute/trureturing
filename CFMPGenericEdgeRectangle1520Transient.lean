import CFMPGenericEdgeBandRelation1515Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate
open D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate
open D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate (PointQuotient)
open D5.S3.Geometry.Gluing.DoubleHalfPlane1490Candidate (HalfPlane DoublePlane fold seam full_kernel fold_isQuotientMap)
open Topology Set

def rectangle (a b δ : ℝ) : Set (ℝ × ℝ) :=
  {p | a < p.1 ∧ p.1 < b ∧ -δ < p.2 ∧ p.2 < δ}

theorem rectangle_open (a b δ : ℝ) : IsOpen (rectangle a b δ) :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const)))

def halfInclusion {a b δ : ℝ} (p : Band a b δ) : HalfPlane :=
  ⟨p.val,p.property.2.2.1⟩

theorem halfInclusion_openEmbedding (a b δ : ℝ) :
    IsOpenEmbedding (halfInclusion (a := a) (b := b) (δ := δ)) := by
  have he : IsEmbedding (halfInclusion (a := a) (b := b) (δ := δ)) :=
    IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal
  refine ⟨he,?_⟩
  have hr : Set.range (halfInclusion (a := a) (b := b) (δ := δ)) =
      {q : HalfPlane | a < q.val.1 ∧ q.val.1 < b ∧ q.val.2 < δ} := by
    ext q
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨p.property.1,p.property.2.1,p.property.2.2.2⟩
    · rintro ⟨ha,hb,hδ⟩
      exact ⟨⟨q.val,ha,hb,q.property,hδ⟩,Subtype.ext rfl⟩
  rw [hr]
  exact (isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val)).inter
    ((isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const).inter
      (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const))

theorem modelPoint_openEmbedding (a b δ : ℝ) :
    IsOpenEmbedding (modelPoint (a := a) (b := b) (δ := δ)) := by
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  have h := halfInclusion_openEmbedding a b δ
  refine ⟨h.continuous.sumMap h.continuous,?_,h.isOpenMap.sumMap h.isOpenMap⟩
  intro x y he
  cases x with
  | inl p =>
    cases y with
    | inl q => exact congrArg Sum.inl (h.injective (Sum.inl.inj he))
    | inr q => cases he
  | inr p =>
    cases y with
    | inl q => cases he
    | inr q => exact congrArg Sum.inr (h.injective (Sum.inr.inj he))

theorem modelPoint_range {a b δ : ℝ} (hδ : 0 < δ) :
    Set.range (modelPoint (a := a) (b := b) (δ := δ)) = fold ⁻¹' rectangle a b δ := by
  ext z
  cases z with
  | inl p =>
    constructor
    · rintro ⟨q,he⟩
      cases q with
      | inl q =>
        have h : q.val = p.val := congrArg Subtype.val (Sum.inl.inj he)
        change a < p.val.1 ∧ p.val.1 < b ∧ -δ < p.val.2 ∧ p.val.2 < δ
        rw [← h]
        exact ⟨q.property.1,q.property.2.1,by linarith [q.property.2.2.1],q.property.2.2.2⟩
      | inr q => cases he
    · intro hp
      change a < p.val.1 ∧ p.val.1 < b ∧ -δ < p.val.2 ∧ p.val.2 < δ at hp
      exact ⟨.inl ⟨p.val,hp.1,hp.2.1,p.property,hp.2.2.2⟩,rfl⟩
  | inr p =>
    constructor
    · rintro ⟨q,he⟩
      cases q with
      | inl q => cases he
      | inr q =>
        have h : q.val = p.val := congrArg Subtype.val (Sum.inr.inj he)
        change a < p.val.1 ∧ p.val.1 < b ∧ -δ < -p.val.2 ∧ -p.val.2 < δ
        rw [← h]
        exact ⟨q.property.1,q.property.2.1,by linarith [q.property.2.2.2],by linarith [q.property.2.2.1]⟩
    · intro hp
      change a < p.val.1 ∧ p.val.1 < b ∧ -δ < -p.val.2 ∧ -p.val.2 < δ at hp
      exact ⟨.inr ⟨p.val,hp.1,hp.2.1,p.property,by linarith [hp.2.2.1]⟩,rfl⟩

def modelPreimageHomeomorph {a b δ : ℝ} (hδ : 0 < δ) :
    (Band a b δ ⊕ Band a b δ) ≃ₜ ↥(fold ⁻¹' rectangle a b δ) :=
  (modelPoint_openEmbedding a b δ).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (modelPoint_range hδ))

def signedBand {a b δ : ℝ} (hδ : 0 < δ) :
    (Band a b δ ⊕ Band a b δ) → ↥(rectangle a b δ) :=
  (rectangle a b δ).restrictPreimage fold ∘ modelPreimageHomeomorph hδ

theorem signedBand_isQuotientMap {a b δ : ℝ} (hδ : 0 < δ) :
    IsQuotientMap (signedBand (a := a) (b := b) hδ) :=
  (fold_isQuotientMap.restrictPreimage_isOpen (rectangle_open a b δ)).comp
    (modelPreimageHomeomorph hδ).isQuotientMap

variable {T : Type*} [TopologicalSpace T] [DiscreteTopology T]

def actualPreimageHomeomorph (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1) :
    (Band a b δ ⊕ Band a b δ) ≃ₜ
      ↥((@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) ⁻¹'
        quotientBandImage P ν t e hc ha hb) :=
  (doublePoint_openEmbedding P ν t e hc ha hb hδa hbδ).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (actual_open_edge_quotient P ν t e hc ha hb hδa hbδ).1.symm)

def actualBand (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1) :
    (Band a b δ ⊕ Band a b δ) → ↥(quotientBandImage P ν t e hc ha hb) :=
  (quotientBandImage P ν t e hc ha hb).restrictPreimage
    (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) ∘
      actualPreimageHomeomorph P ν t e hc ha hb hδa hbδ

theorem actualBand_isQuotientMap (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1) :
    IsQuotientMap (actualBand P ν t e hc ha hb hδa hbδ) :=
  (isQuotientMap_quotient_mk'.restrictPreimage_isOpen
    (actual_open_edge_quotient P ν t e hc ha hb hδa hbδ).2).comp
      (actualPreimageHomeomorph P ν t e hc ha hb hδa hbδ).isQuotientMap

theorem same_kernel (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1) (hδ : 0 < δ)
    (x y : Band a b δ ⊕ Band a b δ) :
    Setoid.ker (actualBand P ν t e hc ha hb hδa hbδ) x y ↔
      Setoid.ker (signedBand (a := a) (b := b) hδ) x y := by
  constructor
  · intro h
    have he : (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν))))
        (doublePoint P ν t e hc ha hb x) =
        (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν))))
        (doublePoint P ν t e hc ha hb y) := congrArg Subtype.val h
    exact Subtype.ext ((full_kernel _ _).mp
      ((full_model_correspondence P ν t e hc ha hb hδa hbδ x y).mp (Quotient.exact he)))
  · intro h
    have he : fold (modelPoint x) = fold (modelPoint y) := congrArg Subtype.val h
    exact Subtype.ext (Quotient.sound
      ((full_model_correspondence P ν t e hc ha hb hδa hbδ x y).mpr
        ((full_kernel _ _).mpr he)))

def originalEdgeRectangleChart (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1) (hδ : 0 < δ) :
    ↥(quotientBandImage P ν t e hc ha hb) ≃ₜ ↥(rectangle a b δ) :=
  (Topology.IsQuotientMap.homeomorph
    (f := (⟨actualBand P ν t e hc ha hb hδa hbδ,
      (actualBand_isQuotientMap P ν t e hc ha hb hδa hbδ).continuous⟩ :
        C(Band a b δ ⊕ Band a b δ,↥(quotientBandImage P ν t e hc ha hb))))
    (actualBand_isQuotientMap P ν t e hc ha hb hδa hbδ)).symm.trans
  ((Homeomorph.Quotient.congrRight (same_kernel P ν t e hc ha hb hδa hbδ hδ)).trans
    (Topology.IsQuotientMap.homeomorph
      (f := (⟨signedBand (a := a) (b := b) hδ,
        (signedBand_isQuotientMap (a := a) (b := b) hδ).continuous⟩ :
          C(Band a b δ ⊕ Band a b δ,↥(rectangle a b δ))))
      (signedBand_isQuotientMap (a := a) (b := b) hδ)))

end D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.rectangle_open,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.halfInclusion_openEmbedding,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.modelPoint_openEmbedding,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.modelPoint_range,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.modelPreimageHomeomorph,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.signedBand_isQuotientMap,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.actualPreimageHomeomorph,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.actualBand_isQuotientMap,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.same_kernel,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate.originalEdgeRectangleChart] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1520 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1520 disallowed {ax}"
    Lean.logInfo m!"CFMP1520 CHECKED {name} axioms={axioms}"
