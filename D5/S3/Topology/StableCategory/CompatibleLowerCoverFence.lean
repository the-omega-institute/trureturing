/- GID: D5/S3/Topology/StableCategory/CompatibleLowerCoverFence
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/CompatibleLowerCoverFence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compatible regional order homotopies glue on a lower cover. -/

module

public import D5.S3.Topology.BarycentricGraphDistance
public import D5.S3.Topology.ConnectedCategoryGraft
public import Mathlib.Data.Finset.Lattice.Lemmas

/-! # Compatible fences on a lower cover

For two lower sets covering a face poset, compatible regional maps glue by
intersection on the overlap. Two frames with separately comparable regional
maps have a compatible common upper frame. This gives the ambient fence used
in the lower-cover obstruction for Mosquera–Lois and Tanaka, Question 6.3.
-/

public section

set_option autoImplicit false

namespace D5.S3.Topology.StableCategory.CompatibleLowerCoverFence

open BarycentricGraphDistance (Face)
open ConnectedCategoryGraft (Categorical)
open Relation (EqvGen)

variable {V : Type*} {J : PreAbstractSimplicialComplex V}
variable {U W : Set (Face J)}

/-- Two maps from the covering regions into the ambient face poset. -/
abbrev RegionalMaps (U W : Set (Face J)) :=
  (U →o Face J) × (W →o Face J)

variable [DecidableEq V]

/-- Both images of each shared face contain a common vertex. -/
def Compatible (a : RegionalMaps U W) : Prop :=
  ∀ (x : Face J) (hx : x ∈ U) (hy : x ∈ W),
    ((a.1 ⟨x, hx⟩).val ∩ (a.2 ⟨x, hy⟩).val).Nonempty

/-- Compatible pairs carry the induced pointwise product order. -/
abbrev CompatiblePair (U W : Set (Face J)) :=
  {a : RegionalMaps U W // Compatible a}

/-- A transition compares each coordinate in its own direction. -/
def Step (a b : RegionalMaps U W) : Prop :=
  (a.1 ≤ b.1 ∨ b.1 ≤ a.1) ∧ (a.2 ≤ b.2 ∨ b.2 ≤ a.2)

private theorem map_eqvGen {A B : Type*} {r : A → A → Prop} {s : B → B → Prop}
    (f : A → B) (hmap : ∀ a b, r a b → EqvGen s (f a) (f b))
    {a b : A} (h : EqvGen r a b) : EqvGen s (f a) (f b) := by
  induction h with
  | rel a b hab => exact hmap a b hab
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private def intersectFaces (p q : Face J) (h : (p.val ∩ q.val).Nonempty) : Face J :=
  ⟨p.val ∩ q.val, (J.isRelLowerSet_faces p.property).2 Finset.inter_subset_left h⟩

private noncomputable def gluedFace (cover : ∀ x : Face J, x ∈ U ∨ x ∈ W)
    (a : CompatiblePair U W) (x : Face J) : Face J := by
  classical
  exact if hx : x ∈ U then
    if hy : x ∈ W then intersectFaces (a.val.1 ⟨x, hx⟩) (a.val.2 ⟨x, hy⟩)
      (a.property x hx hy)
    else a.val.1 ⟨x, hx⟩
  else a.val.2 ⟨x, (cover x).resolve_left hx⟩

private theorem le_gluedFace_iff (cover : ∀ x : Face J, x ∈ U ∨ x ∈ W)
    (a : CompatiblePair U W) (x z : Face J) :
    z ≤ gluedFace cover a x ↔
      (∀ hx : x ∈ U, z ≤ a.val.1 ⟨x, hx⟩) ∧ (∀ hy : x ∈ W, z ≤ a.val.2 ⟨x, hy⟩) := by
  classical
  by_cases hx : x ∈ U
  · by_cases hy : x ∈ W
    · rw [gluedFace, dite_eq_left hx, dite_eq_left hy]
      change (z.val ⊆ (a.val.1 ⟨x, hx⟩).val ∩ (a.val.2 ⟨x, hy⟩).val) ↔ _
      rw [Finset.subset_inter_iff]
      exact ⟨fun h => ⟨fun _ => h.1, fun _ => h.2⟩, fun h => ⟨h.1 hx, h.2 hy⟩⟩
    · rw [gluedFace, dite_eq_left hx, dite_eq_right hy]
      exact ⟨fun h => ⟨fun _ => h, fun hy' => (hy hy').elim⟩, fun h => h.1 hx⟩
  · rw [gluedFace, dite_eq_right hx]
    exact ⟨fun h => ⟨fun hx' => (hx hx').elim, fun _ => h⟩,
      fun h => h.2 ((cover x).resolve_left hx)⟩

variable (hU : IsLowerSet U) (hW : IsLowerSet W)
  (cover : ∀ x : Face J, x ∈ U ∨ x ∈ W)

/-- The gluing is monotone in the input face and in both regional maps. -/
noncomputable def glue : CompatiblePair U W →o (Face J →o Face J) where
  toFun a :=
    { toFun := gluedFace cover a
      monotone' := by
        intro x y hxy
        have hx := (le_gluedFace_iff cover a x (gluedFace cover a x)).mp le_rfl
        refine (le_gluedFace_iff cover a y (gluedFace cover a x)).mpr ⟨?_, ?_⟩
        · intro hy
          have hle : (⟨x, hU hxy hy⟩ : U) ≤ ⟨y, hy⟩ := hxy
          exact (hx.1 (hU hxy hy)).trans (a.val.1.monotone hle)
        · intro hy
          have hle : (⟨x, hW hxy hy⟩ : W) ≤ ⟨y, hy⟩ := hxy
          exact (hx.2 (hW hxy hy)).trans (a.val.2.monotone hle) }
  monotone' := by
    intro a b hab
    apply OrderHom.le_def.mpr
    intro x
    have hx := (le_gluedFace_iff cover a x (gluedFace cover a x)).mp le_rfl
    have hab' : a.val.1 ≤ b.val.1 ∧ a.val.2 ≤ b.val.2 := hab
    exact (le_gluedFace_iff cover b x (gluedFace cover a x)).mpr
      ⟨fun hu => (hx.1 hu).trans (OrderHom.le_def.mp hab'.1 ⟨x, hu⟩),
       fun hw => (hx.2 hw).trans (OrderHom.le_def.mp hab'.2 ⟨x, hw⟩)⟩

/-- The glued map is the greatest ambient order map below both regional maps. -/
theorem le_glue_iff (a : CompatiblePair U W) (t : Face J →o Face J) :
    t ≤ glue hU hW cover a ↔
      (∀ x : U, t x.val ≤ a.val.1 x) ∧ (∀ x : W, t x.val ≤ a.val.2 x) := by
  change (∀ x, t x ≤ gluedFace cover a x) ↔ _
  constructor
  · intro h
    exact ⟨fun x => ((le_gluedFace_iff cover a x.val (t x.val)).mp (h x.val)).1 x.property,
      fun x => ((le_gluedFace_iff cover a x.val (t x.val)).mp (h x.val)).2 x.property⟩
  · intro h x
    exact (le_gluedFace_iff cover a x (t x)).mpr
      ⟨fun hu => h.1 ⟨x, hu⟩, fun hw => h.2 ⟨x, hw⟩⟩

/-- An ambient lower extension itself supplies the intersection witnesses. -/
theorem compatible_of_lower_extension {a : RegionalMaps U W} (t : Face J →o Face J)
    (h₁ : ∀ x : U, t x.val ≤ a.1 x) (h₂ : ∀ x : W, t x.val ≤ a.2 x) :
    Compatible a :=
  fun x hu hw => (J.isRelLowerSet_faces (t x).property).1.mono
    (Finset.subset_inter (h₁ ⟨x, hu⟩) (h₂ ⟨x, hw⟩))

theorem Compatible.mono {a b : RegionalMaps U W} (ha : Compatible a) (hab : a ≤ b) :
    Compatible b := by
  intro x hu hw
  exact (ha x hu hw).mono (Finset.subset_inter
    (Finset.inter_subset_left.trans (OrderHom.le_def.mp hab.1 ⟨x, hu⟩))
    (Finset.inter_subset_right.trans (OrderHom.le_def.mp hab.2 ⟨x, hw⟩)))

private theorem exists_upper_of_comparable {A : Type*} [Preorder A] {a b : A}
    (h : a ≤ b ∨ b ≤ a) : ∃ c, a ≤ c ∧ b ≤ c :=
  h.elim (fun hab => ⟨b, hab, le_rfl⟩) (fun hba => ⟨a, le_rfl, hba⟩)

/-- The larger map in each coordinate gives a compatible intermediate frame. -/
theorem glue_fence {a b : CompatiblePair U W}
    (h : EqvGen (fun x y : CompatiblePair U W => Step x.val y.val) a b) :
    EqvGen (· ≤ ·) (glue hU hW cover a) (glue hU hW cover b) := by
  refine map_eqvGen (glue hU hW cover) (fun x y hxy => ?_) h
  obtain ⟨f, hxf, hyf⟩ := exists_upper_of_comparable hxy.1
  obtain ⟨g, hxg, hyg⟩ := exists_upper_of_comparable hxy.2
  have hx : x.val ≤ (f, g) := ⟨hxf, hxg⟩
  have hy : y.val ≤ (f, g) := ⟨hyf, hyg⟩
  let z : CompatiblePair U W := ⟨(f, g), Compatible.mono x.property hx⟩
  exact .trans _ _ _ (.rel _ _ ((glue hU hW cover).monotone (show x ≤ z from hx)))
    (.symm _ _ (.rel _ _ ((glue hU hW cover).monotone (show y ≤ z from hy))))

/-- The inclusion maps at the initial frame. -/
def inclusions (U W : Set (Face J)) : RegionalMaps U W :=
  ((OrderEmbedding.subtype U).toOrderHom, (OrderEmbedding.subtype W).toOrderHom)

/-- The constant maps at a terminal frame. -/
def constants (U W : Set (Face J)) (p q : Face J) : RegionalMaps U W :=
  (OrderHom.const U p, OrderHom.const W q)

/-- The restrictions of a single ambient map give a compatible pair. -/
def restrict (U W : Set (Face J)) (t : Face J →o Face J) : CompatiblePair U W :=
  ⟨(t.comp (OrderEmbedding.subtype U).toOrderHom, t.comp (OrderEmbedding.subtype W).toOrderHom),
    compatible_of_lower_extension t (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- Gluing the restrictions of an ambient map recovers that map. -/
theorem glue_restrict (t : Face J →o Face J) :
    glue hU hW cover (restrict U W t) = t := by
  apply le_antisymm
  · have hb := (le_glue_iff hU hW cover (restrict U W t)
      (glue hU hW cover (restrict U W t))).mp le_rfl
    apply OrderHom.le_def.mpr
    intro x
    rcases cover x with hx | hx
    · exact hb.1 ⟨x, hx⟩
    · exact hb.2 ⟨x, hx⟩
  · exact (le_glue_iff hU hW cover (restrict U W t) t).mpr
      ⟨fun _ => le_rfl, fun _ => le_rfl⟩

/-- An ambient contraction restricts to a compatible fence. -/
theorem compatible_fence_of_ambient_fence {c : Face J}
    (h : EqvGen (· ≤ ·) (OrderHom.id : Face J →o Face J) (OrderHom.const (Face J) c)) :
    EqvGen (fun x y : CompatiblePair U W => Step x.val y.val)
      (restrict U W OrderHom.id) (restrict U W (OrderHom.const (Face J) c)) := by
  refine map_eqvGen (restrict U W) (fun f g hfg => .rel _ _ ?_) h
  exact ⟨Or.inl (OrderHom.le_def.mpr fun x => OrderHom.le_def.mp hfg x.val),
    Or.inl (OrderHom.le_def.mpr fun x => OrderHom.le_def.mp hfg x.val)⟩

include hU hW cover in
/-- A compatible fence from the two inclusions to a common constant contracts
the ambient face poset. The statement also applies to disconnected face posets. -/
theorem contracts_of_common_endpoint {c : Face J}
    (h : EqvGen (fun x y : CompatiblePair U W => Step x.val y.val)
      (restrict U W OrderHom.id) (restrict U W (OrderHom.const (Face J) c))) :
    EqvGen (· ≤ ·) (OrderHom.id : Face J →o Face J) (OrderHom.const (Face J) c) := by
  simpa only [glue_restrict] using glue_fence hU hW cover h

include hU hW cover in
/-- Connectedness allows the terminal constants to differ. With overlap the
constant intersection lies below the glued endpoint. With empty overlap all
faces belong to the same covering piece. -/
theorem contracts_of_connected {p q : Face J} {b : CompatiblePair U W}
    (connected : ∀ x : Face J, EqvGen (· ≤ ·) x p)
    (hfinish : b.val = constants U W p q)
    (h : EqvGen (fun x y : CompatiblePair U W => Step x.val y.val)
      (restrict U W OrderHom.id) b) :
    ∃ c : Face J, EqvGen (· ≤ ·) (OrderHom.id : Face J →o Face J)
      (OrderHom.const (Face J) c) := by
  classical
  have hf : EqvGen (· ≤ ·) (OrderHom.id : Face J →o Face J) (glue hU hW cover b) := by
    simpa only [glue_restrict] using glue_fence hU hW cover h
  suffices ∃ c : Face J, OrderHom.const (Face J) c ≤ glue hU hW cover b by
    obtain ⟨c, hc⟩ := this
    exact ⟨c, .trans _ _ _ hf (.symm _ _ (.rel _ _ hc))⟩
  by_cases overlap : ∃ x : Face J, x ∈ U ∧ x ∈ W
  · obtain ⟨x, hx, hy⟩ := overlap
    have hb : Compatible (constants U W p q) := by
      simpa only [hfinish] using b.property
    let c := intersectFaces p q (hb x hx hy)
    refine ⟨c, (le_glue_iff hU hW cover b _).mpr ?_⟩
    rw [hfinish]
    exact ⟨fun _ => Finset.inter_subset_left, fun _ => Finset.inter_subset_right⟩
  · have samePiece {x y : Face J} (hxy : EqvGen (· ≤ ·) x y) : x ∈ U ↔ y ∈ U := by
      induction hxy with
      | rel x y hxy =>
        refine ⟨fun hx => (cover y).elim id (fun hy => ?_), hU hxy⟩
        exact (overlap ⟨x, hx, hW hxy hy⟩).elim
      | refl x => exact Iff.rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    by_cases hp : p ∈ U
    · refine ⟨p, (le_glue_iff hU hW cover b _).mpr ?_⟩
      rw [hfinish]
      exact ⟨fun _ => le_rfl, fun x =>
        (overlap ⟨x.val, (samePiece (connected x.val)).mpr hp, x.property⟩).elim⟩
    · refine ⟨q, (le_glue_iff hU hW cover b _).mpr ?_⟩
      rw [hfinish]
      exact ⟨fun x => (hp ((samePiece (connected x.val)).mp x.property)).elim,
        fun _ => le_rfl⟩

omit [DecidableEq V] in
private theorem categorical_univ_of_fence {c : Face J}
    (h : EqvGen (· ≤ ·) (OrderHom.id : Face J →o Face J) (OrderHom.const (Face J) c)) :
    Categorical (Set.univ : Set (Face J)) := by
  let inc : (Set.univ : Set (Face J)) →o Face J :=
    (OrderEmbedding.subtype (Set.univ : Set (Face J))).toOrderHom
  have hf : EqvGen (· ≤ ·) (OrderHom.id.comp inc) ((OrderHom.const (Face J) c).comp inc) :=
    map_eqvGen (fun f => f.comp inc)
      (fun f g hfg => .rel _ _ (OrderHom.le_def.mpr fun x => OrderHom.le_def.mp hfg (inc x))) h
  exact ⟨c, by simpa only [OrderHom.id_comp, OrderHom.const_comp] using hf⟩

include hU hW in
/-- A failure on a shared face restricts to a failure on a shared singleton. -/
theorem exists_disjoint_singleton_of_not_compatible {a : RegionalMaps U W}
    (ha : ¬ Compatible a) :
    ∃ (v : V) (s : Face J) (hu : s ∈ U) (hw : s ∈ W),
      s.val = {v} ∧ Disjoint (a.1 ⟨s, hu⟩).val (a.2 ⟨s, hw⟩).val := by
  classical
  have hbad : ∃ (x : Face J) (hu : x ∈ U) (hw : x ∈ W),
      ¬ ((a.1 ⟨x, hu⟩).val ∩ (a.2 ⟨x, hw⟩).val).Nonempty := by
    simpa only [Compatible, not_forall] using ha
  obtain ⟨x, hu, hw, hx⟩ := hbad
  obtain ⟨v, hv⟩ := (J.isRelLowerSet_faces x.property).1
  have hsub : ({v} : Finset V) ⊆ x.val := Finset.singleton_subset_iff.mpr hv
  let s : Face J :=
    ⟨{v}, (J.isRelLowerSet_faces x.property).2 hsub (Finset.singleton_nonempty v)⟩
  have hsu := hU (show s ≤ x from hsub) hu
  have hsw := hW (show s ≤ x from hsub) hw
  have h₁ := a.1.monotone (show (⟨s, hsu⟩ : U) ≤ ⟨x, hu⟩ from hsub)
  have h₂ := a.2.monotone (show (⟨s, hsw⟩ : W) ≤ ⟨x, hw⟩ from hsub)
  refine ⟨v, s, hsu, hsw, rfl, Finset.disjoint_iff_inter_eq_empty.mpr ?_⟩
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hs
  exact hx (hs.mono (Finset.subset_inter
    (Finset.inter_subset_left.trans h₁) (Finset.inter_subset_right.trans h₂)))

omit [DecidableEq V] in
include hU hW cover in
/-- For any frame schedule from the inclusions to terminal constants, an
ambient noncontractibility obstruction forces disjoint images of a shared
singleton at some frame. The schedule can use any index relation and any
finite path in its equivalence closure. -/
theorem exists_disjoint_singleton_of_schedule {I : Type*} {next : I → I → Prop}
    {start finish : I} (frames : I → RegionalMaps U W) (path : EqvGen next start finish)
    (step : ∀ i j, next i j → Step (frames i) (frames j))
    (hfirst : frames start = inclusions U W) {p q : Face J}
    (hlast : frames finish = constants U W p q)
    (hends : p = q ∨ ∀ x : Face J, EqvGen (· ≤ ·) x p)
    (hnoncontractible : ¬ Categorical (Set.univ : Set (Face J))) :
    ∃ (i : I) (v : V) (s : Face J) (hu : s ∈ U) (hw : s ∈ W),
      s.val = {v} ∧ Disjoint ((frames i).1 ⟨s, hu⟩).val ((frames i).2 ⟨s, hw⟩).val := by
  classical
  by_contra hbad
  have hc (i : I) : Compatible (frames i) := by
    by_contra hn
    obtain ⟨v, s, hu, hw, hs, hd⟩ := exists_disjoint_singleton_of_not_compatible hU hW hn
    exact hbad ⟨i, v, s, hu, hw, hs, hd⟩
  let lift (i : I) : CompatiblePair U W := ⟨frames i, hc i⟩
  have hfence : EqvGen (fun x y : CompatiblePair U W => Step x.val y.val)
      (lift start) (lift finish) :=
    map_eqvGen lift (fun i j hij => .rel _ _ (step i j hij)) path
  have hs : lift start = restrict U W OrderHom.id := by
    apply Subtype.ext
    simpa only [lift, restrict, OrderHom.id_comp, inclusions] using hfirst
  rw [hs] at hfence
  apply hnoncontractible
  rcases hends with he | connected
  · subst q
    have ht : lift finish = restrict U W (OrderHom.const (Face J) p) := by
      apply Subtype.ext
      simpa only [lift, restrict, OrderHom.const_comp, constants] using hlast
    rw [ht] at hfence
    exact categorical_univ_of_fence (contracts_of_common_endpoint hU hW cover hfence)
  · obtain ⟨c, h⟩ := contracts_of_connected hU hW cover connected hlast hfence
    exact categorical_univ_of_fence h

end D5.S3.Topology.StableCategory.CompatibleLowerCoverFence
