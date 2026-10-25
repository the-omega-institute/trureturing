import CFMPGenericEdgeBand1511Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate
open D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate
open D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate (PointQuotient)
open D5.S3.Geometry.Gluing.DoubleHalfPlane1490Candidate (HalfPlane DoublePlane fold seam full_kernel)
open Topology Set
variable {T : Type*}

theorem point_injective (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) :
    Function.Injective (point P ν t e hc ha hb) := by
  intro p q he
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg (fun x : Point P ν => x.val.2 (e 1)) he
    simpa only [point,(coords_values e p.val).2.1,(coords_values e q.val).2.1] using h
  · have h := congrArg (fun x : Point P ν => x.val.2 (e 2)) he
    simpa only [point,(coords_values e p.val).2.2.1,(coords_values e q.val).2.2.1] using h

theorem point_interior (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (p : Band a b δ) (hp : p.val.2 ≠ 0) :
    Interior P (point P ν t e hc ha hb p) := by
  have h1 : 0 < p.val.1 := ha.trans p.property.1
  have h3 : 0 < 1-p.val.1-p.val.2 := by linarith [p.property.2.1,p.property.2.2.2]
  intro f hf
  change f ≠ e 0 at hf
  change coords e p.val f ≠ 0
  obtain ⟨k,rfl⟩ := e.surjective f
  fin_cases k
  · exact False.elim (hf rfl)
  · change coords e p.val (e 1) ≠ 0
    rw [(coords_values e p.val).2.1];linarith
  · change coords e p.val (e 2) ≠ 0
    rw [(coords_values e p.val).2.2.1];exact hp
  · change coords e p.val (e 3) ≠ 0
    rw [(coords_values e p.val).2.2.2];linarith

theorem point_edge (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (p : Band a b δ) (hp : p.val.2 = 0) :
    EdgePoint P (point P ν t e hc ha hb p) (e 2) := by
  have h1 : 0 < p.val.1 := ha.trans p.property.1
  have h3 : 0 < 1-p.val.1-p.val.2 := by linarith [p.property.2.1,p.property.2.2.2]
  refine ⟨e.injective.ne (by decide),?_,?_⟩
  · change coords e p.val (e 2) = 0
    exact (coords_values e p.val).2.2.1.trans hp
  · intro f hfj hf
    change f ≠ e 0 at hfj
    change coords e p.val f = 0 at hf
    obtain ⟨k,rfl⟩ := e.surjective f
    fin_cases k
    · exact False.elim (hfj rfl)
    · change coords e p.val (e 1) = 0 at hf
      rw [(coords_values e p.val).2.1] at hf;linarith
    · rfl
    · change coords e p.val (e 3) = 0 at hf
      rw [(coords_values e p.val).2.2.2] at hf;linarith

theorem point_normal_form (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (p : Band a b δ) (y : Point P ν) :
    Related P (point P ν t e hc ha hb p) y ↔
      y = point P ν t e hc ha hb p ∨
      p.val.2 = 0 ∧ y = point P ν (partnerTet P t e) (partnerFrame P t e)
        (paired_label P ν t e hc) ha hb p := by
  by_cases hp : p.val.2 = 0
  · have hE := point_edge P ν t e hc ha hb p hp
    have hN := (positive_side_normal_form P _ y (e 2) hE).2
    constructor
    · intro h
      rcases hN.mp h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hp,h.trans (point_partner P ν t e hc ha hb p).symm⟩
    · rintro (h | ⟨_,h⟩)
      · exact hN.mpr (Or.inl h)
      · exact hN.mpr (Or.inr (h.trans (point_partner P ν t e hc ha hb p)))
  · have hN := interior_normal_form P _ y (point_interior P ν t e hc ha hb p hp)
    constructor
    · intro h;exact Or.inl (hN.mp h)
    · rintro (h | ⟨h,_⟩)
      · exact hN.mpr h
      · exact False.elim (hp h)

def doublePoint (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) : Band a b δ ⊕ Band a b δ → Point P ν :=
  Sum.elim (point P ν t e hc ha hb)
    (point P ν (partnerTet P t e) (partnerFrame P t e) (paired_label P ν t e hc) ha hb)

def modelPoint {a b δ : ℝ} : Band a b δ ⊕ Band a b δ → DoublePlane :=
  Sum.map (fun p => (⟨p.val,p.property.2.2.1⟩ : HalfPlane))
    (fun p => (⟨p.val,p.property.2.2.1⟩ : HalfPlane))

theorem paired_related (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (p : Band a b δ) (hp : p.val.2 = 0) :
    Related P (doublePoint P ν t e hc ha hb (.inl p))
      (doublePoint P ν t e hc ha hb (.inr p)) := by
  apply Relation.EqvGen.rel
  refine ⟨e 2,e.injective.ne (by decide),?_,?_⟩
  · exact (coords_values e p.val).2.2.1.trans hp
  · exact congrArg Subtype.val (point_partner P ν t e hc ha hb p)

theorem cross_normal_form (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1)
    (p q : Band a b δ) :
    Related P (doublePoint P ν t e hc ha hb (.inl p))
      (doublePoint P ν t e hc ha hb (.inr q)) ↔ p = q ∧ p.val.2 = 0 := by
  simp only [doublePoint,Sum.elim_inl,Sum.elim_inr]
  rw [point_normal_form P ν t e hc ha hb p]
  constructor
  · rintro (h | ⟨hp,h⟩)
    · exact False.elim (branches_disjoint P ν t e hc ha hb hδa hbδ p q h.symm)
    · exact ⟨(point_injective P ν _ _ _ ha hb h).symm,hp⟩
  · rintro ⟨rfl,hp⟩
    exact Or.inr ⟨hp,rfl⟩

theorem same_left_normal_form (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1)
    (p q : Band a b δ) :
    Related P (doublePoint P ν t e hc ha hb (.inl p))
      (doublePoint P ν t e hc ha hb (.inl q)) ↔ p = q := by
  simp only [doublePoint,Sum.elim_inl,Sum.elim_inr]
  rw [point_normal_form P ν t e hc ha hb p]
  constructor
  · rintro (h | ⟨_,h⟩)
    · exact (point_injective P ν t e hc ha hb h).symm
    · exact False.elim (branches_disjoint P ν t e hc ha hb hδa hbδ q p h)
  · rintro rfl
    exact Or.inl rfl

theorem same_right_normal_form (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1)
    (p q : Band a b δ) :
    Related P (doublePoint P ν t e hc ha hb (.inr p))
      (doublePoint P ν t e hc ha hb (.inr q)) ↔ p = q := by
  constructor
  · intro h
    by_cases hp : p.val.2 = 0
    · exact (cross_normal_form P ν t e hc ha hb hδa hbδ p q).mp
        (Relation.EqvGen.trans _ _ _ (paired_related P ν t e hc ha hb p hp) h) |>.1
    · have hi := point_interior P ν (partnerTet P t e) (partnerFrame P t e)
        (paired_label P ν t e hc) ha hb p hp
      have he := (interior_normal_form P _ _ hi).mp h
      exact (point_injective P ν (partnerTet P t e) (partnerFrame P t e) (paired_label P ν t e hc) ha hb he).symm
  · rintro rfl
    exact Relation.EqvGen.refl _

theorem full_model_correspondence (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1)
    (z w : Band a b δ ⊕ Band a b δ) :
    Related P (doublePoint P ν t e hc ha hb z) (doublePoint P ν t e hc ha hb w) ↔
      Relation.EqvGen seam (modelPoint z) (modelPoint w) := by
  rw [full_kernel]
  cases z with
  | inl p =>
    cases w with
    | inl q =>
      rw [same_left_normal_form P ν t e hc ha hb hδa hbδ]
      change p = q ↔ p.val = q.val
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    | inr q =>
      rw [cross_normal_form P ν t e hc ha hb hδa hbδ]
      change p = q ∧ p.val.2 = 0 ↔ p.val = (q.val.1,-q.val.2)
      constructor
      · rintro ⟨rfl,hp⟩
        exact Prod.ext rfl (by linarith)
      · intro he
        have hx := congrArg Prod.fst he
        have hy := congrArg Prod.snd he
        have hp : p.val.2 = 0 := by linarith [p.property.2.2.1,q.property.2.2.1]
        have hq : q.val.2 = 0 := by linarith [p.property.2.2.1,q.property.2.2.1]
        exact ⟨Subtype.ext (Prod.ext hx (hp.trans hq.symm)),hp⟩
  | inr p =>
    cases w with
    | inl q =>
      rw [show Related P (doublePoint P ν t e hc ha hb (.inr p))
          (doublePoint P ν t e hc ha hb (.inl q)) ↔
          Related P (doublePoint P ν t e hc ha hb (.inl q))
          (doublePoint P ν t e hc ha hb (.inr p)) from ⟨fun h => h.symm,fun h => h.symm⟩]
      rw [cross_normal_form P ν t e hc ha hb hδa hbδ]
      change q = p ∧ q.val.2 = 0 ↔ (p.val.1,-p.val.2) = q.val
      constructor
      · rintro ⟨rfl,hp⟩
        exact Prod.ext rfl (by linarith)
      · intro he
        have hx := congrArg Prod.fst he
        have hy := congrArg Prod.snd he
        have hp : p.val.2 = 0 := by linarith [p.property.2.2.1,q.property.2.2.1]
        have hq : q.val.2 = 0 := by linarith [p.property.2.2.1,q.property.2.2.1]
        exact ⟨Subtype.ext (Prod.ext hx.symm (hq.trans hp.symm)),hq⟩
    | inr q =>
      rw [same_right_normal_form P ν t e hc ha hb hδa hbδ]
      constructor
      · rintro rfl;rfl
      · intro he
        change (p.val.1,-p.val.2) = (q.val.1,-q.val.2) at he
        have hx := congrArg Prod.fst he
        have hy := congrArg Prod.snd he
        exact Subtype.ext (Prod.ext hx (by linarith))

theorem full_range_saturated (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (x y : Point P ν)
    (hx : x ∈ Set.range (doublePoint P ν t e hc ha hb)) (hxy : Related P x y) :
    y ∈ Set.range (doublePoint P ν t e hc ha hb) := by
  obtain ⟨z,rfl⟩ := hx
  have left {p : Band a b δ} (h : Related P (doublePoint P ν t e hc ha hb (.inl p)) y) :
      y ∈ Set.range (doublePoint P ν t e hc ha hb) := by
    rcases (point_normal_form P ν t e hc ha hb p y).mp h with h | ⟨_,h⟩
    · exact ⟨.inl p,h.symm⟩
    · exact ⟨.inr p,h.symm⟩
  cases z with
  | inl p => exact left hxy
  | inr p =>
    by_cases hp : p.val.2 = 0
    · exact left (Relation.EqvGen.trans _ _ _ (paired_related P ν t e hc ha hb p hp) hxy)
    · have hi := point_interior P ν (partnerTet P t e) (partnerFrame P t e)
        (paired_label P ν t e hc) ha hb p hp
      exact ⟨.inr p,((interior_normal_form P _ _ hi).mp hxy).symm⟩

section Topology
variable [TopologicalSpace T] [DiscreteTopology T]
theorem doublePoint_openEmbedding (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1) :
    IsOpenEmbedding (doublePoint P ν t e hc ha hb) := by
  apply (point_openEmbedding P ν t e hc ha hb).sumElim
    (point_openEmbedding P ν _ _ (paired_label P ν t e hc) ha hb)
  intro z w he
  cases z with
  | inl p =>
    cases w with
    | inl q => exact congrArg Sum.inl (point_injective P ν t e hc ha hb he)
    | inr q => exact False.elim (branches_disjoint P ν t e hc ha hb hδa hbδ p q he)
  | inr p =>
    cases w with
    | inl q => exact False.elim (branches_disjoint P ν t e hc ha hb hδa hbδ q p he.symm)
    | inr q => exact congrArg Sum.inr (point_injective P ν (partnerTet P t e) (partnerFrame P t e) (paired_label P ν t e hc) ha hb he)

def quotientBandImage (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) : Set (PointQuotient P ν) :=
  (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) ''
    Set.range (doublePoint P ν t e hc ha hb)

theorem actual_open_edge_quotient (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1) :
    ((@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) ⁻¹'
      quotientBandImage P ν t e hc ha hb = Set.range (doublePoint P ν t e hc ha hb)) ∧
      IsOpen (quotientBandImage P ν t e hc ha hb) := by
  have hs : ((@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) ⁻¹'
      quotientBandImage P ν t e hc ha hb = Set.range (doublePoint P ν t e hc ha hb)) := by
    ext y
    constructor
    · rintro ⟨x,hx,he⟩
      exact full_range_saturated P ν t e hc ha hb x y hx (Quotient.exact he)
    · intro hy;exact ⟨y,hy,rfl⟩
  refine ⟨hs,?_⟩
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  rw [hs]
  exact (doublePoint_openEmbedding P ν t e hc ha hb hδa hbδ).isOpen_range
end Topology

end D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.point_injective,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.point_interior,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.point_edge,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.point_normal_form,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.paired_related,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.cross_normal_form,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.same_left_normal_form,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.same_right_normal_form,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.full_model_correspondence,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.full_range_saturated,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.doublePoint_openEmbedding,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate.actual_open_edge_quotient] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1515 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1515 disallowed {ax}"
    Lean.logInfo m!"CFMP1515 CHECKED {name} axioms={axioms}"
