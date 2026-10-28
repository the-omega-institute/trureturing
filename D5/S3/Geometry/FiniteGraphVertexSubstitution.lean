/- GID: D5/S3/Geometry/FiniteGraphVertexSubstitution
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphVertexSubstitution
   mirror-E: none(waiver:finite-graph-vertex-substitution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
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
open scoped BigOperators ContinuousMap

namespace D5.S3.Geometry.FiniteGraphVertexSubstitution

open FiniteConeCollapse FiniteSimplicialJoin FiniteConeUnionWedge
universe u w

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

/-- Coordinates of an embedded realization are recovered from the image
coordinates, including zero coordinates at every unused ambient vertex. -/
theorem mapped_coordinates (K : PreAbstractSimplicialComplex U) (f : U ↪ X)
    (y : Space (K.map f)) :
    (fun z => ∑ u, if f u = z then y.val (f u) else 0) = y.val := by
  change push f (fun u => y.val (f u)) = y.val
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
  · rw [← sum_push f]
    have he : push f (fun u => y.val (f u)) = y.val := mapped_coordinates K f y
    rw [he]
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
  right_inv y := Subtype.ext (mapped_coordinates K f y)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro z
    change Continuous (fun x : Space K => ∑ u, if f u = z then x.val u else 0)
    apply continuous_finset_sum
    intro u _
    by_cases h : f u = z
    · simpa only [if_pos h, Function.comp_def] using
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
  change (∃ t : Finset U, (t.Nonempty ∧ G.IsIndepSet (t : Set U) ∧ ∀ a ∈ t, p a) ∧
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
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact Finset.mem_preimage.mp ha
      · intro hx
        obtain ⟨a, _, rfl⟩ := hp x hx
        exact ⟨a, Finset.mem_preimage.mpr hx, rfl⟩
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
  symm := ⟨by
    rintro (a | a) (b | b) h
    · exact h.symm
    · exact h.elim
    · exact h.elim
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

private theorem substitution_same (G : SimpleGraph V) (H : ∀ u, SimpleGraph (D u))
    (u : V) (a b : D u) :
    (substitution G H).Adj ⟨u, a⟩ ⟨u, b⟩ ↔ (H u).Adj a b := by
  constructor
  · rintro (h | ⟨i, c, d, hx, hy, hcd⟩)
    · exact (h.ne rfl).elim
    · have hui : u = i := congrArg Sigma.fst hx
      subst i
      have hac := sigma_mk_injective hx
      have hbd := sigma_mk_injective hy
      simpa only [hac, hbd] using hcd
  · exact fun h => Or.inr ⟨u, a, b, rfl, rfl, h⟩

private theorem substitution_ne (G : SimpleGraph V) (H : ∀ u, SimpleGraph (D u))
    {u w : V} (huw : u ≠ w) (a : D u) (b : D w) :
    (substitution G H).Adj ⟨u, a⟩ ⟨w, b⟩ ↔ G.Adj u w := by
  constructor
  · rintro (h | ⟨i, c, d, hx, hy, _⟩)
    · exact h
    · exact (huw ((congrArg Sigma.fst hx).trans (congrArg Sigma.fst hy).symm)).elim
  · exact Or.inl

private theorem restriction_adj (G : SimpleGraph V) (H : ∀ u, SimpleGraph (D u))
    (p : Set V) (x y : Σ u : p, D u.val) :
    (substitution (G.induce p) (fun u : p => H u.val)).Adj x y ↔
      (substitution G H).Adj ⟨x.1.val, x.2⟩ ⟨y.1.val, y.2⟩ := by
  classical
  rcases x with ⟨u, a⟩
  rcases y with ⟨w, b⟩
  by_cases h : u = w
  · subst w
    rw [substitution_same, substitution_same]
  · have hv : u.val ≠ w.val := fun he => h (Subtype.ext he)
    rw [substitution_ne _ _ h, substitution_ne _ _ hv]
    rfl

end Substitution

section Replacement
variable {V : Type u} {D : V → Type w} {W : Type w}
variable [Fintype V] [DecidableEq V] [∀ u, Fintype (D u)] [∀ u, DecidableEq (D u)]
variable [Fintype W] [DecidableEq W]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- All current vertices away from the replaced base vertex. -/
abbrev Tail (v : V) (D : V → Type*) := Σ u : {u : V // u ≠ v}, D u.val

/-- The base complement of the closed neighborhood, keeping the current fibers. -/
def LinkBaseSet (G : SimpleGraph V) (v : V) : Set V := {u | u ≠ v ∧ ¬ G.Adj v u}

/-- Vertices of the current-fiber restricted link. -/
abbrev LinkVerts (G : SimpleGraph V) (v : V) (D : V → Type*) :=
  Σ u : LinkBaseSet G v, D u.val

variable (G : SimpleGraph V) (H : ∀ u, SimpleGraph (D u)) (v : V)

private abbrev tailGraph : SimpleGraph (Tail v D) :=
  substitution (G.induce {u | u ≠ v}) (fun u => H u.val)

private abbrev linkGraph : SimpleGraph (LinkVerts G v D) :=
  substitution (G.induce (LinkBaseSet G v)) (fun u => H u.val)

/-- The restricted independence complex uses the original current fibers. -/
def linkComplex : PreAbstractSimplicialComplex (LinkVerts G v D) :=
  (independenceComplex (linkGraph G H v)).toPreAbstractSimplicialComplex

private def linkEmbedding : LinkVerts G v D ↪ Tail v D :=
  Function.Embedding.sigmaMap
    ⟨fun u => ⟨u.val, u.property.1⟩, fun x y h =>
      Subtype.ext (congrArg (fun z : {u : V // u ≠ v} => z.val) h)⟩
    (fun _ => Function.Embedding.refl _)

private theorem link_adj (a b : LinkVerts G v D) :
    (linkGraph G H v).Adj a b ↔
      (tailGraph G H v).Adj (linkEmbedding G v a) (linkEmbedding G v b) := by
  exact (restriction_adj G H (LinkBaseSet G v) a b).trans
    (restriction_adj G H {u | u ≠ v} (linkEmbedding G v a) (linkEmbedding G v b)).symm

variable (Hnew : SimpleGraph W)

private def replacementGraph : SimpleGraph (Tail v D ⊕ W) where
  Adj := Sum.elim
    (fun a => Sum.elim (fun b => (tailGraph G H v).Adj a b) (fun _ => G.Adj v a.1.val))
    (fun a => Sum.elim (fun b => G.Adj v b.1.val) (fun b => Hnew.Adj a b))
  symm := ⟨by
    rintro (a | a) (b | b) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by rintro (a | a) h <;> exact h.ne rfl⟩

private def joinEmbedding : LinkVerts G v D ⊕ W ↪ Tail v D ⊕ W :=
  (linkEmbedding G v).sumMap (Function.Embedding.refl W)

private def allowed : Tail v D ⊕ W → Prop :=
  Sum.elim (fun a => ¬ G.Adj v a.1.val) (fun _ => True)

private def atMostApex (l0 : W) : Tail v D ⊕ W → Prop :=
  Sum.elim (fun _ => True) (fun w => w = l0)

private theorem join_adj (a b : LinkVerts G v D ⊕ W) :
    (disjointGraph (linkGraph G H v) Hnew).Adj a b ↔
      (replacementGraph G H v Hnew).Adj (joinEmbedding G v a) (joinEmbedding G v b) := by
  rcases a with a | a <;> rcases b with b | b
  · exact link_adj G H v a b
  · exact iff_of_false id (fun h => a.1.property.2 h)
  · exact iff_of_false id (fun h => b.1.property.2 h)
  · rfl

private theorem join_range (x : Tail v D ⊕ W) :
    (∃ a : LinkVerts G v D ⊕ W, True ∧ joinEmbedding G v a = x) ↔ allowed G v x := by
  rcases x with ⟨⟨u, hu⟩, d⟩ | w
  · constructor
    · rintro ⟨a | a, _, h⟩
      · have he := congrArg (fun x : Tail v D => x.1.val) (Sum.inl.inj h)
        change a.1.val = u at he
        change ¬ G.Adj v u
        exact he ▸ a.1.property.2
      · cases h
    · intro h
      exact ⟨Sum.inl ⟨⟨u, hu, h⟩, d⟩, trivial, rfl⟩
  · exact ⟨fun _ => trivial, fun _ => ⟨Sum.inr w, trivial, rfl⟩⟩

private def pointComplex (l0 : W) : PreAbstractSimplicialComplex W :=
  restricted Hnew (fun w => w = l0)

private def deletion : PreAbstractSimplicialComplex (Tail v D ⊕ W) :=
  ((independenceComplex (tailGraph G H v)).toPreAbstractSimplicialComplex).map Sum.inl

private def Bpiece : PreAbstractSimplicialComplex (Tail v D ⊕ W) :=
  (simplicialJoin (linkComplex G H v)
    (independenceComplex Hnew).toPreAbstractSimplicialComplex).map (joinEmbedding G v)

private def cone (l0 : W) : PreAbstractSimplicialComplex (Tail v D ⊕ W) :=
  (simplicialJoin (linkComplex G H v) (pointComplex Hnew l0)).map (joinEmbedding G v)

private def A (l0 : W) : PreAbstractSimplicialComplex (Tail v D ⊕ W) :=
  deletion G H v ⊔ cone G H v Hnew l0

private theorem deletion_eq : deletion G H v =
    restricted (replacementGraph G H v Hnew) (Sum.elim (fun _ => True) (fun _ => False)) := by
  unfold deletion
  rw [← unrestricted]
  change (restricted (tailGraph G H v) (fun _ => True)).map
    (Function.Embedding.inl : Tail v D ↪ Tail v D ⊕ W) = _
  rw [restricted_map _ (replacementGraph G H v Hnew)
    (Function.Embedding.inl) (fun _ _ => Iff.rfl)]
  congr 1
  funext x
  cases x <;> simp

private theorem Bpiece_eq : Bpiece G H v Hnew =
    restricted (replacementGraph G H v Hnew) (allowed G v) := by
  unfold Bpiece linkComplex
  rw [← unrestricted, ← unrestricted, restricted_join,
    restricted_map _ _ (joinEmbedding G v) (join_adj G H v Hnew)]
  congr 1
  funext x
  apply propext
  have hp : Sum.elim (fun _ : LinkVerts G v D => True) (fun _ : W => True) =
      (fun _ => True) := by funext a; cases a <;> rfl
  rw [hp]
  exact join_range G v x

private theorem cone_eq (l0 : W) : cone G H v Hnew l0 =
    restricted (replacementGraph G H v Hnew)
      (fun x => allowed G v x ∧ atMostApex v l0 x) := by
  unfold cone linkComplex pointComplex
  rw [← unrestricted, restricted_join,
    restricted_map _ _ (joinEmbedding G v) (join_adj G H v Hnew)]
  congr 1
  funext x
  apply propext
  rcases x with ⟨⟨u, hu⟩, d⟩ | w
  · constructor
    · rintro ⟨a | a, hp, h⟩
      · have he := congrArg (fun x : Tail v D => x.1.val) (Sum.inl.inj h)
        change a.1.val = u at he
        change (¬ G.Adj v u) ∧ True
        exact ⟨he ▸ a.1.property.2, trivial⟩
      · cases h
    · rintro ⟨h, _⟩
      exact ⟨Sum.inl ⟨⟨u, hu, h⟩, d⟩, trivial, rfl⟩
  · constructor
    · rintro ⟨a | a, hp, h⟩
      · cases h
      · exact ⟨trivial, (Sum.inr.inj h) ▸ hp⟩
    · rintro ⟨_, h⟩
      exact ⟨Sum.inr w, h, rfl⟩

private theorem face_dichotomy (s : Finset (Tail v D ⊕ W))
    (hi : (replacementGraph G H v Hnew).IsIndepSet (s : Set (Tail v D ⊕ W))) :
    (∀ x ∈ s, Sum.elim (fun _ => True) (fun _ => False) x) ∨
      (∀ x ∈ s, allowed G v x) := by
  by_cases hr : ∃ w, Sum.inr w ∈ s
  · right
    obtain ⟨w, hw⟩ := hr
    rintro (a | a) ha
    · exact fun h => hi ha hw (by simp) h
    · trivial
  · left
    rintro (a | a) ha
    · trivial
    · exact hr ⟨a, ha⟩

private theorem A_eq (l0 : W) : A G H v Hnew l0 =
    restricted (replacementGraph G H v Hnew) (atMostApex v l0) := by
  unfold A
  rw [deletion_eq G H v Hnew, cone_eq]
  ext s
  constructor
  · rintro (⟨hn, hi, hp⟩ | ⟨hn, hi, hp⟩)
    · refine ⟨hn, hi, ?_⟩
      rintro (a | a) ha
      · trivial
      · exact (hp (Sum.inr a) ha).elim
    · exact ⟨hn, hi, fun a ha => (hp a ha).2⟩
  · rintro ⟨hn, hi, hp⟩
    rcases face_dichotomy G H v Hnew s hi with hl | hr
    · exact Or.inl ⟨hn, hi, hl⟩
    · exact Or.inr ⟨hn, hi, fun a ha => ⟨hr a ha, hp a ha⟩⟩

private theorem cover_eq (l0 : W) :
    (independenceComplex (replacementGraph G H v Hnew)).toPreAbstractSimplicialComplex =
      A G H v Hnew l0 ⊔ Bpiece G H v Hnew := by
  rw [A_eq, Bpiece_eq]
  ext s
  constructor
  · rintro ⟨hn, hi⟩
    rcases face_dichotomy G H v Hnew s hi with hl | hr
    · left
      refine ⟨hn, hi, ?_⟩
      rintro (a | a) ha
      · trivial
      · exact (hl (Sum.inr a) ha).elim
    · exact Or.inr ⟨hn, hi, hr⟩
  · rintro (⟨hn, hi, _⟩ | ⟨hn, hi, _⟩) <;> exact ⟨hn, hi⟩

private theorem intersection_eq (l0 : W) :
    A G H v Hnew l0 ⊓ Bpiece G H v Hnew = cone G H v Hnew l0 := by
  rw [A_eq, Bpiece_eq, cone_eq]
  ext s
  constructor
  · rintro ⟨⟨hn, hi, ha⟩, ⟨_, _, hb⟩⟩
    exact ⟨hn, hi, fun a ha' => ⟨hb a ha', ha a ha'⟩⟩
  · rintro ⟨hn, hi, hp⟩
    exact ⟨⟨hn, hi, fun a ha => (hp a ha).2⟩,
      ⟨hn, hi, fun a ha => (hp a ha).1⟩⟩

private theorem apex_face (l0 : W) :
    ({Sum.inr l0} : Finset (Tail v D ⊕ W)) ∈ cone G H v Hnew l0 := by
  rw [cone_eq]
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · exact (independenceComplex (replacementGraph G H v Hnew)).singleton_mem _ |>.2
  · intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact ⟨trivial, rfl⟩

private theorem cone_face (l0 : W) (s : Finset (Tail v D ⊕ W))
    (hs : s ∈ cone G H v Hnew l0) : insert (Sum.inr l0) s ∈ cone G H v Hnew l0 := by
  rw [cone_eq] at hs ⊢
  have hn (x) (hx : x ∈ s) : ¬ (replacementGraph G H v Hnew).Adj (Sum.inr l0) x := by
    rcases x with a | w
    · exact (hs.2.2 (Sum.inl a) hx).1
    · have he : w = l0 := (hs.2.2 (Sum.inr w) hx).2
      subst w
      exact Hnew.loopless.irrefl l0
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro a ha b hb hab hadj
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hab rfl
      · exact hn b hb hadj
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hn a ha hadj.symm
      · exact hs.2.1 ha hb hab hadj
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨trivial, rfl⟩
    · exact hs.2.2 a ha

private def coneUnion (l0 : W) : ConeUnion (Tail v D ⊕ W) where
  left := A G H v Hnew l0
  right := Bpiece G H v Hnew
  cone := cone G H v Hnew l0
  intersection := intersection_eq G H v Hnew l0
  apex := Sum.inr l0
  apex_face := apex_face G H v Hnew l0
  cone_face := cone_face G H v Hnew l0

private def oldTo (l0 : W) (x : Σ u, D u) : Tail v D ⊕ W :=
  if h : x.1 = v then Sum.inr l0 else Sum.inl ⟨⟨x.1, h⟩, x.2⟩

variable (d0 : D v) (hsingle : ∀ d : D v, d = d0)

private def oldEmbedding (l0 : W) : (Σ u, D u) ↪ Tail v D ⊕ W where
  toFun := oldTo v l0
  inj' := by
    have hl : Function.LeftInverse
        (Sum.elim (fun x : Tail v D => (⟨x.1.val, x.2⟩ : Σ u, D u))
          (fun _ : W => (⟨v, d0⟩ : Σ u, D u))) (oldTo v l0) := by
      rintro ⟨u, d⟩
      by_cases h : u = v
      · subst u
        simp [oldTo, hsingle d]
      · simp [oldTo, h]
    exact hl.injective

private theorem old_adj (l0 : W) (x y : Σ u, D u) :
    (substitution G H).Adj x y ↔ (replacementGraph G H v Hnew).Adj
      (oldEmbedding v d0 hsingle l0 x) (oldEmbedding v d0 hsingle l0 y) := by
  rcases x with ⟨u, a⟩
  rcases y with ⟨w, b⟩
  change _ ↔ (replacementGraph G H v Hnew).Adj (oldTo v l0 ⟨u, a⟩) (oldTo v l0 ⟨w, b⟩)
  by_cases hu : u = v
  · subst u
    by_cases hw : w = v
    · subst w
      rw [hsingle a, hsingle b]
      simp [oldTo, replacementGraph, substitution_same]
    · rw [substitution_ne _ _ (Ne.symm hw)]
      simp [oldTo, hw, replacementGraph]
  · by_cases hw : w = v
    · subst w
      rw [substitution_ne _ _ hu]
      simpa [oldTo, hu, replacementGraph] using (G.adj_comm u v)
    · dsimp only [oldTo]
      rw [dif_neg hu, dif_neg hw]
      exact (restriction_adj G H {u | u ≠ v} ⟨⟨u, hu⟩, a⟩ ⟨⟨w, hw⟩, b⟩).symm

private theorem old_eq (l0 : W) :
    ((independenceComplex (substitution G H)).toPreAbstractSimplicialComplex).map
      (oldEmbedding v d0 hsingle l0) = A G H v Hnew l0 := by
  rw [← unrestricted, restricted_map _ _ _ (old_adj G H v Hnew d0 hsingle l0), A_eq]
  congr 1
  funext x
  apply propext
  rcases x with ⟨⟨u, hu⟩, d⟩ | w
  · constructor
    · intro _
      trivial
    · intro _
      exact ⟨⟨u, d⟩, trivial, by simp [oldEmbedding, oldTo, hu]⟩
  · constructor
    · rintro ⟨⟨u, d⟩, _, h⟩
      change oldTo v l0 ⟨u, d⟩ = Sum.inr w at h
      by_cases hu : u = v
      · simpa [oldTo, hu, atMostApex] using h.symm
      · simp [oldTo, hu] at h
    · intro h
      subst w
      exact ⟨⟨v, d0⟩, trivial, by simp [oldEmbedding, oldTo]⟩

/-- The new sigma family changes precisely the distinguished fiber. -/
def newFiber (v : V) (D : V → Type w) (W : Type w) (u : V) : Type w :=
  if u = v then W else D u

instance newFiberFintype (u : V) : Fintype (newFiber v D W u) := by
  unfold newFiber
  split_ifs <;> infer_instance

instance newFiberDecidableEq (u : V) : DecidableEq (newFiber v D W u) := by
  unfold newFiber
  split_ifs <;> infer_instance

/-- The actual replacement graphs on the new sigma fibers. -/
def newGraphs (u : V) : SimpleGraph (newFiber v D W u) := by
  by_cases h : u = v
  · exact Hnew.comap (fun a => cast (by simp only [newFiber, if_pos h]) a)
  · exact (H u).comap (fun a => cast (by simp only [newFiber, if_neg h]) a)

private theorem cast_cancel {A B : Type w} (h : A = B) (k : B = A) (a : A) :
    _root_.cast k (_root_.cast h a) = a := by
  subst B
  rfl

private def newTo (x : Σ u, newFiber v D W u) : Tail v D ⊕ W :=
  if h : x.1 = v then Sum.inr (cast (by simp only [newFiber, if_pos h]) x.2)
  else Sum.inl ⟨⟨x.1, h⟩, cast (by simp only [newFiber, if_neg h]) x.2⟩

private def newFrom : Tail v D ⊕ W → Σ u, newFiber v D W u :=
  Sum.elim (fun a => ⟨a.1.val, cast (by simp only [newFiber, if_neg a.1.property]) a.2⟩)
    (fun w => ⟨v, cast (by simp [newFiber]) w⟩)

private def newEquiv : (Σ u, newFiber v D W u) ≃ Tail v D ⊕ W where
  toFun := newTo v
  invFun := newFrom v
  left_inv := by
    rintro ⟨u, d⟩
    by_cases h : u = v
    · subst u
      simp [newTo, newFrom]
    · simp [newTo, newFrom, h]
  right_inv := by
    rintro (⟨⟨u, hu⟩, d⟩ | w)
    · simp [newTo, newFrom, hu]
      exact cast_cancel _ _ d
    · simp [newTo, newFrom]
      exact cast_cancel _ _ w

private theorem new_adj (x y : Σ u, newFiber v D W u) :
    (substitution G (newGraphs H v Hnew)).Adj x y ↔
      (replacementGraph G H v Hnew).Adj (newEquiv v x) (newEquiv v y) := by
  rcases x with ⟨u, a⟩
  rcases y with ⟨z, b⟩
  by_cases hu : u = v
  · subst u
    by_cases hz : z = v
    · subst z
      rw [substitution_same]
      simp [newEquiv, newTo, newGraphs, replacementGraph]
    · rw [substitution_ne _ _ (Ne.symm hz)]
      simp [newEquiv, newTo, hz, replacementGraph]
  · by_cases hz : z = v
    · subst z
      rw [substitution_ne _ _ hu]
      simpa [newEquiv, newTo, hu, replacementGraph] using (G.adj_comm u v)
    · by_cases huz : u = z
      · subst z
        rw [substitution_same]
        simp [newEquiv, newTo, hu, replacementGraph, substitution_same, newGraphs]
      · rw [substitution_ne _ _ huz]
        simp [newEquiv, newTo, hu, hz, replacementGraph,
          substitution_ne _ _ (show (⟨u, hu⟩ : {u : V // u ≠ v}) ≠ ⟨z, hz⟩ from
            fun h => huz (congrArg Subtype.val h))]

private theorem new_eq :
    ((independenceComplex (substitution G (newGraphs H v Hnew))).toPreAbstractSimplicialComplex).map
      (newEquiv (D := D) (W := W) v).toEmbedding =
      (independenceComplex (replacementGraph G H v Hnew)).toPreAbstractSimplicialComplex := by
  rw [← unrestricted, restricted_map _ _ (newEquiv v).toEmbedding (new_adj G H v Hnew),
    ← unrestricted]
  congr 1
  funext x
  apply propext
  exact ⟨fun _ => trivial, fun _ => ⟨(newEquiv v).symm x, trivial,
    (newEquiv v).apply_symm_apply x⟩⟩

private def complexHomeomorph {U : Type*} [Fintype U] [DecidableEq U]
    {K M : PreAbstractSimplicialComplex U} (h : K = M) : Space K ≃ₜ Space M :=
  Homeomorph.setCongr (congrArg realization h)

/-- The old chosen coordinate vertex. -/
def oldPoint : Space (independenceComplex (substitution G H)).toPreAbstractSimplicialComplex :=
  vertex _ ⟨v, d0⟩ ((independenceComplex (substitution G H)).singleton_mem _)

/-- The pure-right singleton of the actual simplicial join, even for an empty link. -/
def joinPoint (l0 : W) : Space (simplicialJoin (linkComplex G H v)
    (independenceComplex Hnew).toPreAbstractSimplicialComplex) :=
  vertex _ (Sum.inr l0) (by
    have hl : ({Sum.inr l0} : Finset (LinkVerts G v D ⊕ W)).toLeft = ∅ := by
      ext a
      simp only [Finset.mem_toLeft, Finset.mem_singleton, Sum.inl_ne_inr, Finset.notMem_empty]
    have hr : ({Sum.inr l0} : Finset (LinkVerts G v D ⊕ W)).toRight = {l0} := by
      ext a
      simp only [Finset.mem_toRight, Finset.mem_singleton, Sum.inr.injEq]
    exact ⟨Finset.singleton_nonempty _, Or.inl hl,
      Or.inr (hr.symm ▸ (independenceComplex Hnew).singleton_mem l0)⟩)

private def oldHomeomorph (l0 : W) :
    Space (independenceComplex (substitution G H)).toPreAbstractSimplicialComplex ≃ₜ
      Space (A G H v Hnew l0) :=
  (mapHomeomorph _ (oldEmbedding v d0 hsingle l0)).trans
    (complexHomeomorph (old_eq G H v Hnew d0 hsingle l0))

private def joinHomeomorph :
    Space (simplicialJoin (linkComplex G H v)
      (independenceComplex Hnew).toPreAbstractSimplicialComplex) ≃ₜ
      Space (Bpiece G H v Hnew) :=
  mapHomeomorph _ (joinEmbedding G v)

private theorem push_vertex {U X : Type*} [Fintype U] [DecidableEq U]
    [Fintype X] [DecidableEq X] (f : U ↪ X) (a : U) :
    push f (Pi.single a 1) = Pi.single (f a) 1 := by
  funext z
  by_cases hz : z ∈ Set.range f
  · obtain ⟨b, rfl⟩ := hz
    rw [push_at]
    simp [Pi.single_apply, f.injective.eq_iff]
  · rw [push_off f _ z hz]
    have he : z ≠ f a := fun h => hz ⟨a, h.symm⟩
    simp [Pi.single_apply, he, Ne.symm he]

private def wedgeHomeomorph {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (e : X ≃ₜ X') (f : Y ≃ₜ Y') {a : X} {b : Y} {a' : X'} {b' : Y'}
    (ha : e a = a') (hb : f b = b') : Wedge a b ≃ₜ Wedge a' b' := by
  apply Homeomorph.Quotient.congr (e.sumCongr f)
  have hp (z : X ⊕ Y) : z ∈ wedgePoints a b ↔
      (e.sumCongr f) z ∈ wedgePoints a' b' := by
    rcases z with x | y
    · simp [wedgePoints, Homeomorph.sumCongr, Equiv.sumCongr, ← ha, e.injective.eq_iff]
    · simp [wedgePoints, Homeomorph.sumCongr, Equiv.sumCongr, ← hb, f.injective.eq_iff]
  intro z t
  change (z = t ∨ (z ∈ wedgePoints a b ∧ t ∈ wedgePoints a b)) ↔ _
  exact or_congr (e.sumCongr f).injective.eq_iff.symm (and_congr (hp z) (hp t))

/-- The actual new sigma independence realization is homotopy equivalent to the
actual quotient wedge of the old realization and the simplicial current-link
join. All finite fibers, including empty other fibers and an empty link, are in
scope. Only the distinguished old fiber is required to be a singleton. -/
def oneVertexReplacementEquiv (l0 : W) :
    Space (independenceComplex (substitution G (newGraphs H v Hnew))).toPreAbstractSimplicialComplex ≃ₕ
      Wedge (oldPoint G H v d0) (joinPoint G H v Hnew l0) := by
  let P := coneUnion G H v Hnew l0
  let en := (mapHomeomorph
    (independenceComplex (substitution G (newGraphs H v Hnew))).toPreAbstractSimplicialComplex
    (newEquiv v).toEmbedding).trans
    (complexHomeomorph ((new_eq G H v Hnew).trans (cover_eq G H v Hnew l0)))
  let eo := oldHomeomorph G H v Hnew d0 hsingle l0
  let ej := joinHomeomorph G H v Hnew
  have ho : eo (oldPoint G H v d0) = P.leftPair.apexPoint := by
    apply Subtype.ext
    change push (oldEmbedding v d0 hsingle l0) (Pi.single ⟨v, d0⟩ 1) = Pi.single (Sum.inr l0) 1
    rw [push_vertex]
    simp [oldEmbedding, oldTo]
  have hj : ej (joinPoint G H v Hnew l0) = P.rightPair.apexPoint := by
    apply Subtype.ext
    change push (joinEmbedding G v) (Pi.single (Sum.inr l0) 1) = Pi.single (Sum.inr l0) 1
    rw [push_vertex]
    rfl
  exact (en.toHomotopyEquiv.trans P.homotopyEquiv).trans
    (wedgeHomeomorph eo ej ho hj).symm.toHomotopyEquiv

#print axioms oneVertexReplacementEquiv

end Replacement


section HereditaryTransports

/-- Graph isomorphisms act on the actual independence realizations. -/
def graphIsoHomeomorph {U X : Type*} [Fintype U] [DecidableEq U]
    [Fintype X] [DecidableEq X] {G : SimpleGraph U} {F : SimpleGraph X}
    (e : G ≃g F) :
    Space (independenceComplex G).toPreAbstractSimplicialComplex ≃ₜ
      Space (independenceComplex F).toPreAbstractSimplicialComplex := by
  have he : ((independenceComplex G).toPreAbstractSimplicialComplex).map
      e.toEquiv.toEmbedding = (independenceComplex F).toPreAbstractSimplicialComplex := by
    rw [← unrestricted, restricted_map G F e.toEquiv.toEmbedding
      (fun a b => (e.map_adj_iff).symm), ← unrestricted]
    congr 1
    funext x
    apply propext
    exact ⟨fun _ => trivial, fun _ => ⟨e.symm x, trivial, e.apply_symm_apply x⟩⟩
  exact (mapHomeomorph _ e.toEquiv.toEmbedding).trans
    (Homeomorph.setCongr (congrArg realization he))

/-- Fiberwise graph isomorphisms preserve substitution and the base coordinate. -/
def substitutionFiberIso {V : Type*} {D E : V → Type*} (G : SimpleGraph V)
    (H : ∀ v, SimpleGraph (D v)) (K : ∀ v, SimpleGraph (E v))
    (e : ∀ v, H v ≃g K v) : substitution G H ≃g substitution G K where
  toEquiv := Equiv.sigmaCongrRight (fun v => (e v).toEquiv)
  map_rel_iff' := by
    rintro ⟨v, a⟩ ⟨z, b⟩
    change (substitution G K).Adj ⟨v, e v a⟩ ⟨z, e z b⟩ ↔
      (substitution G H).Adj ⟨v, a⟩ ⟨z, b⟩
    by_cases h : v = z
    · subst z
      rw [substitution_same, substitution_same]
      exact (e v).map_adj_iff
    · rw [substitution_ne G K h, substitution_ne G H h]

/-- Reindex two successive induced subsets by their actual image in the base. -/
def nestedInduceIso {V : Type*} (G : SimpleGraph V) (B : Set V) (S : Set B) :
    (G.induce B).induce S ≃g G.induce (Subtype.val '' S) where
  toEquiv := Equiv.ofBijective
    (fun x : S => (⟨x.val.val, ⟨x.val, x.property, rfl⟩⟩ : Subtype.val '' S))
    ⟨fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : Subtype.val '' S => (y.val : V)) h)), by
      rintro ⟨x, b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩⟩
  map_rel_iff' := Iff.rfl

private def univInduceIso {V : Type*} (G : SimpleGraph V) : G.induce Set.univ ≃g G where
  toEquiv := {
    toFun := Subtype.val
    invFun := fun v => ⟨v, Set.mem_univ v⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

/-- The all-singleton substitution is the original graph, including a singleton base. -/
def singletonSubstitutionIso {V : Type*} (G : SimpleGraph V) :
    substitution G (fun _ => (⊥ : SimpleGraph PUnit)) ≃g G where
  toEquiv := {
    toFun := Sigma.fst
    invFun := fun v => ⟨v, PUnit.unit⟩
    left_inv := by rintro ⟨v, a⟩; cases a; rfl
    right_inv := fun _ => rfl }
  map_rel_iff' := by
    rintro ⟨v, a⟩ ⟨z, b⟩
    simp [substitution]

/-- The empty left simplicial complex is an augmented join unit, by pure right faces. -/
def emptyLeftJoinHomeomorph {U X : Type*} [Fintype U] [DecidableEq U]
    [Fintype X] [DecidableEq X] (M : PreAbstractSimplicialComplex U)
    (N : PreAbstractSimplicialComplex X) (hM : ∀ s, s ∉ M) :
    Space N ≃ₜ Space (simplicialJoin M N) := by
  have he : simplicialJoin M N = N.map (Function.Embedding.inr : X ↪ U ⊕ X) := by
    ext s
    constructor
    · rintro ⟨hn, hl, hr⟩
      have hl0 : s.toLeft = ∅ := hl.resolve_right (hM _)
      have hs : s.toRight.image Sum.inr = s := by
        ext x
        cases x with
        | inl a =>
          have ha : Sum.inl a ∉ s := by
            intro h
            have : a ∈ s.toLeft := Finset.mem_toLeft.mpr h
            simpa [hl0] using this
          simp [ha]
        | inr a => simp
      have hrn : s.toRight.Nonempty := Finset.image_nonempty.mp (hs.symm ▸ hn)
      have hrm : s.toRight ∈ N := hr.resolve_left (fun h => hrn.ne_empty h)
      exact ⟨s.toRight, hrm, hs⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨(N.isRelLowerSet_faces hs).1.image _, Or.inl ?_, Or.inr ?_⟩
      · ext a
        simp
      · have hr : (s.image (Function.Embedding.inr : X ↪ U ⊕ X)).toRight = s := by
          ext a
          simp
        exact hr.symm ▸ hs
  exact (mapHomeomorph N Function.Embedding.inr).trans
    (Homeomorph.setCongr (congrArg realization he.symm))

end HereditaryTransports

section Stages
variable {V : Type u} [Fintype V] [DecidableEq V] {D : V → Type w}
variable [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]

/-- Mixed fibers: final fibers on the replaced set and singletons elsewhere. -/
def stageFiber (R : Finset V) (v : V) : Type w :=
  if v ∈ R then D v else PUnit

instance stageFiberFintype (R : Finset V) (v : V) : Fintype (stageFiber (D := D) R v) := by
  unfold stageFiber
  split_ifs <;> infer_instance

instance stageFiberDecidableEq (R : Finset V) (v : V) :
    DecidableEq (stageFiber (D := D) R v) := by
  unfold stageFiber
  split_ifs <;> infer_instance

instance stageFiberNonempty [∀ v, Nonempty (D v)] (R : Finset V) (v : V) :
    Nonempty (stageFiber (D := D) R v) := by
  unfold stageFiber
  split_ifs <;> infer_instance

/-- Actual mixed graphs, transported across the two branch equalities. -/
def stageGraphs (H : ∀ v, SimpleGraph (D v)) (R : Finset V) (v : V) :
    SimpleGraph (stageFiber (D := D) R v) := by
  by_cases h : v ∈ R
  · exact (H v).comap (cast (by simp only [stageFiber, if_pos h]))
  · exact (⊥ : SimpleGraph PUnit).comap (cast (by simp only [stageFiber, if_neg h]))

private def stageSelectedIso (H : ∀ v, SimpleGraph (D v)) (R : Finset V)
    (v : V) (h : v ∈ R) : stageGraphs H R v ≃g H v where
  toEquiv := Equiv.cast (by simp [stageFiber, h])
  map_rel_iff' := by intro a b; simp [stageGraphs, h, Equiv.cast]

private def stageSingletonIso (H : ∀ v, SimpleGraph (D v)) (R : Finset V)
    (v : V) (h : v ∉ R) : stageGraphs H R v ≃g (⊥ : SimpleGraph PUnit) where
  toEquiv := Equiv.cast (by simp [stageFiber, h])
  map_rel_iff' := by intro a b; simp [stageGraphs, h, Equiv.cast]

/-- The initial mixed stage is genuinely the base graph. -/
def initialStageIso (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v)) :
    substitution G (stageGraphs H ∅) ≃g G :=
  (substitutionFiberIso G _ _ (fun v => stageSingletonIso H ∅ v (by simp))).trans
    (singletonSubstitutionIso G)

/-- The final mixed stage is genuinely the original full substitution. -/
def finalStageIso (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v)) :
    substitution G (stageGraphs H Finset.univ) ≃g substitution G H :=
  substitutionFiberIso G _ _ (fun v => stageSelectedIso H Finset.univ v (by simp))

private def replacementStageFiberIso (H : ∀ v, SimpleGraph (D v))
    (R : Finset V) (v z : V) :
    newGraphs (stageGraphs H R) v (H v) z ≃g stageGraphs H (insert v R) z := by
  by_cases hz : z = v
  · subst z
    refine { toEquiv := Equiv.cast (by simp [newFiber, stageFiber]), map_rel_iff' := ?_ }
    intro a b
    simp [newGraphs, stageGraphs, SimpleGraph.comap, newFiber, stageFiber]
    simp only [Equiv.cast_apply, cast_cast]
  · by_cases hr : z ∈ R
    · refine { toEquiv := Equiv.cast (by simp [newFiber, stageFiber, hz, hr]),
               map_rel_iff' := ?_ }
      intro a b
      simp [newGraphs, stageGraphs, SimpleGraph.comap, newFiber, stageFiber, hz, hr]
      simp only [Equiv.cast_apply, cast_cast]
    · refine { toEquiv := Equiv.cast (by simp [newFiber, stageFiber, hz, hr]),
               map_rel_iff' := ?_ }
      intro a b
      simp [newGraphs, stageGraphs, SimpleGraph.comap, newFiber, stageFiber, hz, hr]

/-- A single supplier replacement is the next actual mixed stage. -/
def replacementStageIso (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (R : Finset V) (v : V) :
    substitution G (newGraphs (stageGraphs H R) v (H v)) ≃g
      substitution G (stageGraphs H (insert v R)) :=
  substitutionFiberIso G _ _ (replacementStageFiberIso H R v)

end Stages


section HereditaryCore

private def pointIndependenceHomeomorph :
    Space (independenceComplex (⊥ : SimpleGraph PUnit.{u + 1})).toPreAbstractSimplicialComplex ≃ₜ
      PUnit.{u + 1} where
  toFun _ := PUnit.unit
  invFun _ := vertex _ PUnit.unit ((independenceComplex _).singleton_mem _)
  left_inv x := by
    apply Subtype.ext
    funext a
    cases a
    obtain ⟨s, hs, hx⟩ := (native_mem _ x.val).mp x.property
    have hx1 := hx.2.1
    simpa [vertex, Pi.single_apply] using hx1.symm
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- Inference inputs for a class of actual spaces; none is asserted for W here. -/
private abbrev ClassHomotopyClosed
    (C : (X : Type u) → [TopologicalSpace X] → Prop) : Prop :=
  ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y],
    (X ≃ₕ Y) → C X → C Y

private abbrev ClassJoinClosed
    (C : (X : Type u) → [TopologicalSpace X] → Prop) : Prop :=
  ∀ {U X : Type u} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    (M : PreAbstractSimplicialComplex U) (N : PreAbstractSimplicialComplex X),
    Nonempty (Space M) → Nonempty (Space N) → C (Space M) → C (Space N) →
      C (OrdinaryJoin (Space M) (Space N))

private abbrev ClassVertexWedgeClosed
    (C : (X : Type u) → [TopologicalSpace X] → Prop) : Prop :=
  ∀ {U X : Type u} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    (M : PreAbstractSimplicialComplex U) (N : PreAbstractSimplicialComplex X)
    (a : Space M) (b : Space N),
    (∃ v, a.val = Pi.single v 1) → (∃ w, b.val = Pi.single w 1) →
    C (Space M) → C (Space N) → C (Wedge a b)

/-- Strong induction on the actual base cardinality, with an inner induction
on the replaced vertices. The right summand always retains all current fibers. -/
private theorem hereditarySubstitutionCore
    (C : (X : Type u) → [TopologicalSpace X] → Prop)
    (hom : ClassHomotopyClosed C) (point : C PUnit.{u + 1})
    (join : ClassJoinClosed C) (wedge : ClassVertexWedgeClosed C)
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {D : V → Type u} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
    [∀ v, Nonempty (D v)] (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (hbase : ∀ S : Set V, S.Nonempty →
      C (Space (independenceComplex (G.induce S)).toPreAbstractSimplicialComplex))
    (hfiber : ∀ v, C (Space (independenceComplex (H v)).toPreAbstractSimplicialComplex)) :
    C (Space (independenceComplex (substitution G H)).toPreAbstractSimplicialComplex) := by
  classical
  generalize hn : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    have hstageFiber (R : Finset V) (v : V) :
        C (Space (independenceComplex (stageGraphs H R v)).toPreAbstractSimplicialComplex) := by
      by_cases hv : v ∈ R
      · exact hom (graphIsoHomeomorph (stageSelectedIso H R v hv)).symm.toHomotopyEquiv
          (hfiber v)
      · exact hom (graphIsoHomeomorph (stageSingletonIso H R v hv)).symm.toHomotopyEquiv
          (hom pointIndependenceHomeomorph.symm.toHomotopyEquiv point)
    have hstage : ∀ R : Finset V,
        C (Space (independenceComplex (substitution G (stageGraphs H R))).toPreAbstractSimplicialComplex) := by
      intro R
      induction R using Finset.induction_on with
      | empty =>
        have hb := hbase Set.univ ⟨Classical.choice (inferInstance : Nonempty V), trivial⟩
        have hg := hom (graphIsoHomeomorph (univInduceIso G)).toHomotopyEquiv hb
        exact hom (graphIsoHomeomorph (initialStageIso G H)).symm.toHomotopyEquiv hg
      | @insert v R hv hr =>
        let e0 := stageSingletonIso H R v hv
        let d0 : stageFiber (D := D) R v := e0.symm PUnit.unit
        have hsingle : ∀ d : stageFiber (D := D) R v, d = d0 := by
          intro d
          exact e0.injective (Subsingleton.elim _ _)
        let l0 : D v := Classical.choice (inferInstance : Nonempty (D v))
        let M := linkComplex G (stageGraphs H R) v
        let N := (independenceComplex (H v)).toPreAbstractSimplicialComplex
        have hN : C (Space N) := hfiber v
        have hNne : Nonempty (Space N) :=
          ⟨vertex N l0 ((independenceComplex (H v)).singleton_mem l0)⟩
        have hright : C (Space (simplicialJoin M N)) := by
          by_cases hL : Nonempty (LinkBaseSet G v)
          · letI : Nonempty (LinkBaseSet G v) := hL
            have hlt : Fintype.card (LinkBaseSet G v) < n := by
              rw [← hn]
              apply Fintype.card_lt_of_injective_of_notMem
                (fun x : LinkBaseSet G v => x.val) Subtype.val_injective (b := v)
              rintro ⟨x, hx⟩
              exact x.property.1 hx
            have hb : ∀ S : Set (LinkBaseSet G v), S.Nonempty →
                C (Space (independenceComplex
                  ((G.induce (LinkBaseSet G v)).induce S)).toPreAbstractSimplicialComplex) := by
              intro S hs
              exact hom (graphIsoHomeomorph (nestedInduceIso G (LinkBaseSet G v) S)).symm.toHomotopyEquiv
                (hbase (Subtype.val '' S) (hs.image Subtype.val))
            have hM : C (Space M) := by
              exact ih (Fintype.card (LinkBaseSet G v)) hlt
                (G := G.induce (LinkBaseSet G v))
                (H := fun x : LinkBaseSet G v => stageGraphs H R x.val)
                hb (fun x => hstageFiber R x.val) rfl
            let x : LinkBaseSet G v := Classical.choice hL
            let d : stageFiber (D := D) R x.val := Classical.choice inferInstance
            have hMne : Nonempty (Space M) :=
              ⟨vertex M ⟨x, d⟩ ((independenceComplex _).singleton_mem _)⟩
            exact hom (FiniteSimplicialJoin.joinHomeomorph M N hMne hNne).toHomotopyEquiv
              (join M N hMne hNne hM hN)
          · have hempty : ∀ s, s ∉ M := by
              intro s hs
              obtain ⟨x, _⟩ := (M.isRelLowerSet_faces hs).1
              exact hL ⟨x.1⟩
            exact hom (emptyLeftJoinHomeomorph M N hempty).toHomotopyEquiv hN
        have hw := wedge
          (independenceComplex (substitution G (stageGraphs H R))).toPreAbstractSimplicialComplex
          (simplicialJoin M N) (oldPoint G (stageGraphs H R) v d0)
          (joinPoint G (stageGraphs H R) v (H v) l0)
          ⟨⟨v, d0⟩, rfl⟩ ⟨Sum.inr l0, rfl⟩ hr hright
        have hnew := hom
          (oneVertexReplacementEquiv G (stageGraphs H R) v (H v) d0 hsingle l0).symm hw
        exact hom (graphIsoHomeomorph (replacementStageIso G H R v)).toHomotopyEquiv hnew
    exact hom (graphIsoHomeomorph (finalStageIso G H)).toHomotopyEquiv (hstage Finset.univ)

#print axioms hereditarySubstitutionCore

end HereditaryCore

end D5.S3.Geometry.FiniteGraphVertexSubstitution
