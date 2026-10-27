/- GID: D5/S3/Geometry/FiniteGraphVertexSubstitution
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphVertexSubstitution
   mirror-E: none(waiver:finite-graph-vertex-substitution)
   anchors: [D5/S3/Geometry/FiniteConeUnionWedge, D5/S3/Geometry/FiniteSimplicialJoin]
   utility: none
   digest: A singleton-fiber graph replacement decomposes into the old complex and the actual simplicial link join. -/
import D5.S3.Geometry.FiniteConeUnionWedge
import D5.S3.Geometry.FiniteSimplicialJoin
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Single-vertex substitution

The classical cone-union decomposition for graph substitution is realized in
finite barycentric coordinates. The join is the simplicial join, including its
pure right faces when the restricted current-fiber link has no vertices.
This construction is used in the route of Carnero Bravo, arXiv:2505.06457v2,
Question 22; it does not settle that question.
-/

noncomputable section
open Set Topology
open scoped BigOperators

namespace D5.S3.Geometry.FiniteGraphVertexSubstitution

open FiniteConeCollapse FiniteSimplicialJoin FiniteConeUnionWedge

section Coordinates
variable {U X : Type*} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

private def push (f : U ↪ X) (x : U → ℝ) (z : X) : ℝ :=
  ∑ u, if f u = z then x u else 0

private theorem push_at (f : U ↪ X) (x : U → ℝ) (u : U) :
    push f x (f u) = x u := by
  simp [push, f.injective.eq_iff]

private theorem push_off (f : U ↪ X) (x : U → ℝ) (z : X)
    (hz : z ∉ Set.range f) : push f x z = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  exact if_neg (fun h => hz ⟨u, h⟩)

private theorem sum_push (f : U ↪ X) (x : U → ℝ) :
    ∑ z, push f x z = ∑ u, x u := by
  simp only [push]
  rw [Finset.sum_comm]
  simp

private theorem native_mem (K : PreAbstractSimplicialComplex U) (x : U → ℝ) :
    x ∈ realization K ↔ ∃ s ∈ K, x ∈ faceSimplex s := by
  simp only [realization, Set.mem_setOf_eq, faceSimplex_eq_convexHull]

private theorem push_mem (K : PreAbstractSimplicialComplex U) (f : U ↪ X)
    (x : Space K) : push f x.val ∈ realization (K.map f) := by
  obtain ⟨s, hs, hx⟩ := (native_mem K x.val).mp x.property
  apply (native_mem _ _).mpr
  refine ⟨s.image f, ⟨s, hs, rfl⟩, ?_⟩
  refine ⟨fun z => Finset.sum_nonneg (fun u _ => ?_), ?_, ?_⟩
  · split_ifs
    · exact hx.1 u
    · exact le_rfl
  · rw [sum_push]
    exact hx.2.1
  · intro z hz
    by_cases hr : z ∈ Set.range f
    · obtain ⟨u, rfl⟩ := hr
      rw [push_at]
      exact hx.2.2 u (fun hu => hz (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
    · exact push_off f x.val z hr

private theorem mapped_off (K : PreAbstractSimplicialComplex U) (f : U ↪ X)
    (y : Space (K.map f)) (z : X) (hz : z ∉ Set.range f) : y.val z = 0 := by
  obtain ⟨t, ⟨s, hs, rfl⟩, hy⟩ := (native_mem _ _).mp y.property
  exact hy.2.2 z (by
    rintro h
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
    exact hz ⟨u, hu⟩)

private theorem push_restrict (K : PreAbstractSimplicialComplex U) (f : U ↪ X)
    (y : Space (K.map f)) : push f (fun u => y.val (f u)) = y.val := by
  funext z
  by_cases hz : z ∈ Set.range f
  · obtain ⟨u, rfl⟩ := hz
    exact push_at _ _ _
  · rw [push_off f _ z hz, mapped_off K f y z hz]

private theorem restrict_mem (K : PreAbstractSimplicialComplex U) (f : U ↪ X)
    (y : Space (K.map f)) : (fun u => y.val (f u)) ∈ realization K := by
  obtain ⟨t, ⟨s, hs, rfl⟩, hy⟩ := (native_mem _ _).mp y.property
  apply (native_mem _ _).mpr
  refine ⟨s, hs, fun u => hy.1 (f u), ?_, ?_⟩
  · rw [← sum_push f, push_restrict K f y]
    exact hy.2.1
  · intro u hu
    apply hy.2.2
    simpa only [Finset.mem_image, f.injective.eq_iff, exists_eq_right] using hu

/-- Native coordinate transport through a vertex embedding. Coordinates at all
ambient vertices outside its image vanish; no surjectivity is required. -/
def mapHomeomorph (K : PreAbstractSimplicialComplex U) (f : U ↪ X) :
    Space K ≃ₜ Space (K.map f) where
  toFun x := ⟨push f x.val, push_mem K f x⟩
  invFun y := ⟨fun u => y.val (f u), restrict_mem K f y⟩
  left_inv x := Subtype.ext (funext (push_at f x.val))
  right_inv y := Subtype.ext (push_restrict K f y)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro z
    change Continuous (fun x : Space K => ∑ u, if f u = z then x.val u else 0)
    apply continuous_finset_sum
    intro u _
    by_cases h : f u = z
    · simpa only [if_pos h] using
        (continuous_apply u).comp (continuous_subtype_val : Continuous (Subtype.val : Space K → _))
    · simpa only [if_neg h] using (continuous_const : Continuous (fun _ : Space K => (0 : ℝ)))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun u => (continuous_apply (f u)).comp continuous_subtype_val)

private def vertex (K : PreAbstractSimplicialComplex U) (a : U)
    (ha : ({a} : Finset U) ∈ K) : Space K :=
  ⟨Pi.single a 1, ⟨{a}, ha, subset_convexHull ℝ _ ⟨a, by simp, rfl⟩⟩⟩

end Coordinates

section Faces
variable {U X : Type*} [DecidableEq U] [DecidableEq X]

/-- The actual nonempty independent faces, with Mathlib's abstract-complex convention. -/
def independenceComplex (G : SimpleGraph U) : AbstractSimplicialComplex U where
  faces := {s | s.Nonempty ∧ G.IsIndepSet (s : Set U)}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => ⟨ht, hs.2.mono (fun _ hx => hts hx)⟩⟩
  singleton_mem a := by
    refine ⟨Finset.singleton_nonempty a, ?_⟩
    intro x hx y hy hxy
    exact (hxy ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm)).elim

private def restricted (G : SimpleGraph U) (p : U → Prop) :
    PreAbstractSimplicialComplex U where
  faces := {s | s.Nonempty ∧ G.IsIndepSet (s : Set U) ∧ ∀ a ∈ s, p a}
  isRelLowerSet_faces := by
    rintro s ⟨hn, hi, hp⟩
    exact ⟨hn, fun t hts ht => ⟨ht, hi.mono (fun _ hx => hts hx),
      fun a ha => hp a (hts ha)⟩⟩

private theorem unrestricted (G : SimpleGraph U) :
    restricted G (fun _ => True) = (independenceComplex G).toPreAbstractSimplicialComplex := by
  ext s
  simp [restricted, independenceComplex]

private theorem restricted_map (G : SimpleGraph U) (F : SimpleGraph X)
    (f : U ↪ X) (hf : ∀ a b, G.Adj a b ↔ F.Adj (f a) (f b)) (p : U → Prop) :
    (restricted G p).map f = restricted F (fun x => ∃ a, p a ∧ f a = x) := by
  classical
  ext s
  change (∃ t, (t.Nonempty ∧ G.IsIndepSet (t : Set U) ∧ ∀ a ∈ t, p a) ∧
    t.image f = s) ↔ s.Nonempty ∧ F.IsIndepSet (s : Set X) ∧
      ∀ x ∈ s, ∃ a, p a ∧ f a = x
  constructor
  · rintro ⟨t, ⟨hn, hi, hp⟩, rfl⟩
    refine ⟨hn.image _, ?_, ?_⟩
    · rintro x hx y hy hxy hadj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hi ha hb (fun h => hxy (congrArg f h)) ((hf a b).mpr hadj)
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨a, hp a ha, rfl⟩
  · rintro ⟨hn, hi, hp⟩
    let t := s.preimage f f.injective.injOn
    have he : t.image f = s := by
      ext x
      simp only [Finset.mem_image, Finset.mem_preimage]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hx
        obtain ⟨a, _, rfl⟩ := hp x hx
        exact ⟨a, hx, rfl⟩
    refine ⟨t, ⟨?_, ?_, ?_⟩, he⟩
    · exact Finset.image_nonempty.mp (he.symm ▸ hn)
    · intro a ha b hb hab hadj
      exact hi (Finset.mem_preimage.mp ha) (Finset.mem_preimage.mp hb)
        (fun h => hab (f.injective h)) ((hf a b).mp hadj)
    · intro a ha
      obtain ⟨b, hb, heq⟩ := hp (f a) (Finset.mem_preimage.mp ha)
      exact f.injective heq ▸ hb

private def disjointGraph (G : SimpleGraph U) (H : SimpleGraph X) : SimpleGraph (U ⊕ X) where
  Adj := Sum.elim (fun a => Sum.elim (fun b => G.Adj a b) (fun _ => False))
    (fun a => Sum.elim (fun _ => False) (fun b => H.Adj a b))
  symm := ⟨by rintro (a | a) (b | b) h <;> try exact h.elim
               · exact h.symm
               · exact h.symm⟩
  loopless := ⟨by rintro (a | a) h <;> exact h.ne rfl⟩

private theorem restricted_join (G : SimpleGraph U) (H : SimpleGraph X)
    (p : U → Prop) (q : X → Prop) :
    simplicialJoin (restricted G p) (restricted H q) =
      restricted (disjointGraph G H) (Sum.elim p q) := by
  ext s
  change (s.Nonempty ∧
    (s.toLeft = ∅ ∨ (s.toLeft.Nonempty ∧ G.IsIndepSet (s.toLeft : Set U) ∧
      ∀ a ∈ s.toLeft, p a)) ∧
    (s.toRight = ∅ ∨ (s.toRight.Nonempty ∧ H.IsIndepSet (s.toRight : Set X) ∧
      ∀ a ∈ s.toRight, q a))) ↔ _
  constructor
  · rintro ⟨hn, hl, hr⟩
    have hil : G.IsIndepSet (s.toLeft : Set U) := by
      rcases hl with he | h
      · simp [he, SimpleGraph.IsIndepSet]
      · exact h.2.1
    have hir : H.IsIndepSet (s.toRight : Set X) := by
      rcases hr with he | h
      · simp [he, SimpleGraph.IsIndepSet]
      · exact h.2.1
    refine ⟨hn, ?_, ?_⟩
    · rintro (a | a) ha (b | b) hb hab hadj
      · exact hil (Finset.mem_toLeft.mpr ha) (Finset.mem_toLeft.mpr hb)
          (fun h => hab (congrArg Sum.inl h)) hadj
      · exact hadj.elim
      · exact hadj.elim
      · exact hir (Finset.mem_toRight.mpr ha) (Finset.mem_toRight.mpr hb)
          (fun h => hab (congrArg Sum.inr h)) hadj
    · rintro (a | a) ha
      · rcases hl with he | h
        · have := Finset.mem_toLeft.mpr ha
          simpa [he] using this
        · exact h.2.2 a (Finset.mem_toLeft.mpr ha)
      · rcases hr with he | h
        · have := Finset.mem_toRight.mpr ha
          simpa [he] using this
        · exact h.2.2 a (Finset.mem_toRight.mpr ha)
  · rintro ⟨hn, hi, hp⟩
    refine ⟨hn, ?_, ?_⟩
    · by_cases he : s.toLeft = ∅
      · exact Or.inl he
      · right
        refine ⟨Finset.nonempty_iff_ne_empty.mpr he, ?_, ?_⟩
        · intro a ha b hb hab hadj
          exact hi (Finset.mem_toLeft.mp ha) (Finset.mem_toLeft.mp hb)
            (fun h => hab (Sum.inl.inj h)) hadj
        · exact fun a ha => hp (Sum.inl a) (Finset.mem_toLeft.mp ha)
    · by_cases he : s.toRight = ∅
      · exact Or.inl he
      · right
        refine ⟨Finset.nonempty_iff_ne_empty.mpr he, ?_, ?_⟩
        · intro a ha b hb hab hadj
          exact hi (Finset.mem_toRight.mp ha) (Finset.mem_toRight.mp hb)
            (fun h => hab (Sum.inr.inj h)) hadj
        · exact fun a ha => hp (Sum.inr a) (Finset.mem_toRight.mp ha)

end Faces

section Substitution
variable {V : Type*} {D : V → Type*}

/-- Heterogeneous sigma substitution, completely joining fibers over base edges. -/
def substitution (G : SimpleGraph V) (H : ∀ u, SimpleGraph (D u)) :
    SimpleGraph (Σ u, D u) where
  Adj x y := G.Adj x.1 y.1 ∨
    ∃ (u : V) (a b : D u), x = ⟨u, a⟩ ∧ y = ⟨u, b⟩ ∧ (H u).Adj a b
  symm := ⟨by
    rintro x y (h | ⟨u, a, b, hx, hy, hab⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨u, b, a, hy, hx, hab.symm⟩⟩
  loopless := ⟨by
    rintro x (h | ⟨u, a, b, ha, hb, hab⟩)
    · exact G.loopless.irrefl x.1 h
    · exact hab.ne (sigma_mk_injective (ha.symm.trans hb))⟩

end Substitution

end D5.S3.Geometry.FiniteGraphVertexSubstitution
