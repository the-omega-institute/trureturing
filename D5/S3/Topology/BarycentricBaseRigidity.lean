/- GID: D5/S3/Topology/BarycentricBaseRigidity
   generality: G
   mirror-B: D5/B/S3/Topology/BarycentricBaseRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Maximal base faces obstruct first moves in contiguity at every subdivision depth. -/

module

public import D5.S3.Topology.BarycentricNeighborhoodIteration
import OmegaBuild.Commands

/-! # Ambient contiguity rigidity under barycentric subdivision -/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Topology.BarycentricBaseRigidity

open BarycentricGraphDistance BarycentricNeighborhoodIteration SimpleGraph
open scoped ENat

universe u

variable {V : Type u}

noncomputable section

local instance classicalDecEq (X : Type u) : DecidableEq X := Classical.decEq X

/-- The original vertex is the sole vertex that can be adjoined to every incident
maximal base face in the ambient complex. For a subcomplex, it can itself be adjoined. -/
def MaximalFaceCriterion (K A : PreAbstractSimplicialComplex V) : Prop :=
  ∀ (a : Vertex A) (w : V),
    (∀ F : Face A, IsMax F → a.val ∈ F.val → insert w F.val ∈ K) → w = a.val

/-- The ordinary subdivision of the ambient complex. -/
abbrev sd (J : PreAbstractSimplicialComplex V) := subdivision J J

/-- The ambient one-skeleton with the equality decision used in `ContainsBall`. -/
abbrev skeleton (J : PreAbstractSimplicialComplex V) := @oneSkeleton V (Classical.decEq V) J

private theorem singleton_mem_of_mem {J : PreAbstractSimplicialComplex V} {s : Finset V}
    (hs : s ∈ J) {x : V} (hx : x ∈ s) : ({x} : Finset V) ∈ J :=
  (J.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)

private theorem singleton_subdivision {J P : PreAbstractSimplicialComplex V} {s : Face J} :
    ({s} : Finset (Face J)) ∈ subdivision J P ↔ s.val ∈ P := by
  constructor
  · intro h
    exact h.2.2 s (Finset.mem_singleton_self s)
  · intro h
    refine ⟨Finset.singleton_nonempty s, ?_, ?_⟩
    · simpa only [Finset.coe_singleton] using (IsChain.singleton (r := (· < ·)) (a := s))
    · intro t ht
      rwa [Finset.mem_singleton.mp ht]

/-- The vertex of the ordinary subdivision labeled by an ambient face. -/
def vertexOfFace (J : PreAbstractSimplicialComplex V) (s : Face J) : Vertex (sd J) :=
  ⟨s, by exact singleton_subdivision.mpr s.property⟩

/-- An original vertex included as its singleton face in one subdivision. -/
def subdividedVertex {J : PreAbstractSimplicialComplex V} (x : Vertex J) :
    Vertex (sd J) :=
  vertexOfFace J ⟨{x.val}, x.property⟩

/-- The successive singleton-face vertices representing an original vertex. -/
def retainedVertex {J : PreAbstractSimplicialComplex V} :
    (n : ℕ) → Vertex J → Vertex (iteratedAmbient J n).2
  | 0, x => x
  | n + 1, x => subdividedVertex (retainedVertex n x)

private theorem retainedVertex_mem {J P : PreAbstractSimplicialComplex V} {x : Vertex J}
    (hx : x ∈ vertexSet J P) (n : ℕ) :
    retainedVertex n x ∈ vertexSet (iteratedAmbient J n).2 (iteratedSubcomplex J P n) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact singleton_subdivision.mpr ih

private def fullOn (J : PreAbstractSimplicialComplex V) (p : V → Prop) :
    PreAbstractSimplicialComplex V where
  faces := {s | s ∈ J ∧ ∀ v ∈ s, p v}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨(J.isRelLowerSet_faces hs.1).1,
      fun _ hts ht => ⟨(J.isRelLowerSet_faces hs.1).2 hts ht, fun v hv => hs.2 v (hts hv)⟩⟩

private theorem fullOn_full (J : PreAbstractSimplicialComplex V) (p : V → Prop) :
    FullIn (fullOn J p) J :=
  ⟨fun _ hs => hs.1,
    fun s h => ⟨s.property, fun v hv => (h v hv).2 v (Finset.mem_singleton_self v)⟩⟩

private theorem mem_vertexSet_fullOn {J : PreAbstractSimplicialComplex V} {p : V → Prop}
    {x : Vertex J} : x ∈ vertexSet J (fullOn J p) ↔ p x.val := by
  constructor
  · intro h
    exact h.2 x.val (Finset.mem_singleton_self _)
  · intro h
    exact ⟨x.property, fun v hv => by rwa [Finset.mem_singleton.mp hv]⟩

private abbrev pointComplex (J : PreAbstractSimplicialComplex V) (x : Vertex J) :=
  fullOn J (· = x.val)

private theorem iterated_point_face {J : PreAbstractSimplicialComplex V} (x : Vertex J)
    (n : ℕ) {s : Finset (iteratedAmbient J n).1}
    (hs : s ∈ iteratedSubcomplex J (pointComplex J x) n) :
    s = {(retainedVertex n x).val} := by
  induction n with
  | zero =>
    exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨(J.isRelLowerSet_faces hs.1).1, hs.2⟩
  | succ n ih =>
    change _ ∈ subdivision _ _ at hs
    apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    refine ⟨hs.1, fun v hv => Subtype.ext ?_⟩
    exact ih (hs.2.2 v hv)

private theorem iterated_mem_of_forall {J R : PreAbstractSimplicialComplex V}
    {ι : Type u} {Q : ι → PreAbstractSimplicialComplex V}
    (h : ∀ s ∈ J, (∀ i, s ∈ Q i) → s ∈ R) (n : ℕ)
    {s : Finset (iteratedAmbient J n).1} (hs : s ∈ (iteratedAmbient J n).2)
    (hall : ∀ i, s ∈ iteratedSubcomplex J (Q i) n) :
    s ∈ iteratedSubcomplex J R n := by
  induction n with
  | zero => exact h s hs hall
  | succ n ih =>
    change _ ∈ subdivision _ _ at hs ⊢
    exact ⟨hs.1, hs.2.1, fun v hv => ih v.property (fun i => (hall i).2.2 v hv)⟩

private theorem graphSetEdist_le_edist {X : Type u} {G : SimpleGraph X} {T : Set X}
    {x y : X} (hy : y ∈ T) : graphSetEdist G {x} T ≤ G.edist x y :=
  iInf_le_of_le ⟨x, Set.mem_singleton x⟩ (iInf_le _ (⟨y, hy⟩ : T))

private theorem exists_near_vertex {J P : PreAbstractSimplicialComplex V} {x : Vertex J}
    (h : graphSetEdist (skeleton J) {x} (vertexSet J P) ≤ (1 : ℕ∞)) :
    ∃ y ∈ vertexSet J P, (skeleton J).Adj x y ∨ x = y := by
  have hlt : graphSetEdist (skeleton J) {x} (vertexSet J P) < (2 : ℕ∞) :=
    h.trans_lt (by decide)
  simp only [graphSetEdist, iInf_lt_iff] at hlt
  obtain ⟨a, b, hab⟩ := hlt
  have ha : a.val = x := Set.mem_singleton_iff.mp a.property
  rw [ha] at hab
  obtain ⟨walk, hwalk⟩ :=
    exists_walk_of_edist_ne_top (ne_top_of_lt (hab.trans (by decide : (2 : ℕ∞) < ⊤)))
  have hlen : walk.length < 2 := by
    apply ENat.natCast_lt_natCast.mp
    rw [hwalk]
    exact hab
  exact ⟨b.val, b.property, edist_le_one_iff_adj_or_eq.mp
    (hwalk.ge.trans (by exact_mod_cast (Nat.lt_succ_iff.mp hlen)))⟩

private theorem comparable_of_adj {K : PreAbstractSimplicialComplex V} {s t : Vertex (sd K)}
    (h : (skeleton (sd K)).Adj s t) : s.val.val ⊆ t.val.val ∨ t.val.val ⊆ s.val.val := by
  let : DecidableEq (Face K) := Classical.decEq _
  have hne : s.val ≠ t.val := fun he => h.1 (Subtype.ext he)
  exact (h.2.2.1 (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hne).imp le_of_lt le_of_lt

/-- The original vertex in the first subdivision corresponding to an element of a face. -/
def incidentVertex {K : PreAbstractSimplicialComplex V} (F : Face K)
    (x : {x : V // x ∈ F.val}) : Vertex (sd K) :=
  subdividedVertex ⟨x.val, by exact singleton_mem_of_mem F.property x.property⟩

private abbrev containingVertex (K : PreAbstractSimplicialComplex V) (x : V) :=
  fullOn (sd K) (fun S => x ∈ S.val)

private abbrev containingFace (K : PreAbstractSimplicialComplex V) (F : Face K) :=
  fullOn (sd K) (fun S => F.val ⊆ S.val)

private abbrev adjoiningFace (K : PreAbstractSimplicialComplex V) (F : Face K) :=
  fullOn (sd K) (fun S => S.val ∪ F.val ∈ K)

private theorem containsBall_incidentVertex {K : PreAbstractSimplicialComplex V}
    (F : Face K) (x : {x : V // x ∈ F.val}) :
    ContainsBall (sd K) (pointComplex (sd K) (incidentVertex F x))
      (containingVertex K x.val) 1 := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := exists_near_vertex hs
  have htval : t.val = (incidentVertex F x).val := (mem_vertexSet_fullOn (x := t)).mp ht
  apply mem_vertexSet_fullOn.mpr
  have hcomp : s.val.val ⊆ ({x.val} : Finset V) ∨ ({x.val} : Finset V) ⊆ s.val.val := by
    rcases hst with hadj | rfl
    · have h := comparable_of_adj hadj
      rw [htval] at h
      exact h
    · exact .inr (by rw [htval]; exact Finset.Subset.rfl)
  rcases hcomp with hsub | hsup
  · obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces s.val.property).1
    have he : v = x.val := Finset.mem_singleton.mp (hsub hv)
    exact he ▸ hv
  · exact hsup (Finset.mem_singleton_self _)

private theorem containsBall_containingFace {K : PreAbstractSimplicialComplex V} (F : Face K) :
    ContainsBall (sd K) (containingFace K F) (adjoiningFace K F) 1 := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := exists_near_vertex hs
  have htF : F.val ⊆ t.val.val := mem_vertexSet_fullOn.mp ht
  obtain ⟨T, hT, hsT, hFT⟩ : ∃ T : Finset V, T ∈ K ∧ s.val.val ⊆ T ∧ F.val ⊆ T := by
    rcases hst with hadj | rfl
    · rcases comparable_of_adj hadj with hsub | hsup
      · exact ⟨t.val.val, t.val.property, hsub, htF⟩
      · exact ⟨s.val.val, s.val.property, Finset.Subset.rfl, htF.trans hsup⟩
    · exact ⟨s.val.val, s.val.property, Finset.Subset.rfl, htF⟩
  apply mem_vertexSet_fullOn.mpr
  refine (K.isRelLowerSet_faces hT).2 (Finset.union_subset hsT hFT) ?_
  exact (K.isRelLowerSet_faces s.val.property).1.mono Finset.subset_union_left

/-- At positive depth, the two radius bounds along incident faces force a vertex to be
the image of the original vertex under repeated singleton subdivision. -/
theorem fixed_of_incident_face_distances {K A : PreAbstractSimplicialComplex V} (hAK : A ≤ K)
    (hcriterion : MaximalFaceCriterion K A) (a : Vertex A) (n : ℕ)
    (center : Face A → Vertex (iteratedAmbient (sd K) n).2)
    (y : Vertex (iteratedAmbient (sd K) n).2)
    (hcenter : ∀ (F : Face A), IsMax F → a.val ∈ F.val →
      ∀ x : {x : V // x ∈ F.val},
        (skeleton (iteratedAmbient (sd K) n).2).edist (center F)
          (retainedVertex n (incidentVertex ⟨F.val, hAK F.property⟩ x)) ≤
            ((2 ^ n : ℕ) : ℕ∞))
    (hmove : ∀ (F : Face A), IsMax F → a.val ∈ F.val →
      (skeleton (iteratedAmbient (sd K) n).2).edist y (center F) ≤ ((2 ^ n : ℕ) : ℕ∞)) :
    y = retainedVertex n (subdividedVertex (⟨a.val, hAK a.property⟩ : Vertex K)) := by
  let J := sd K
  let original := subdividedVertex (⟨a.val, hAK a.property⟩ : Vertex K)
  have hface (F : Face A) (hmax : IsMax F) (ha : a.val ∈ F.val) :
      y ∈ vertexSet (iteratedAmbient J n).2
        (iteratedSubcomplex J (adjoiningFace K ⟨F.val, hAK F.property⟩) n) := by
    let FK : Face K := ⟨F.val, hAK F.property⟩
    have hcontaining : center F ∈ vertexSet (iteratedAmbient J n).2
        (iteratedSubcomplex J (containingFace K FK) n) := by
      refine iterated_mem_of_forall
        (Q := fun x : {x : V // x ∈ F.val} => containingVertex K x.val)
        ?_ n (center F).property ?_
      · intro s hs hall
        exact ⟨hs, fun S hS w hw => (hall ⟨w, hw⟩).2 S hS⟩
      · intro x
        have hx : incidentVertex FK x ∈ vertexSet J (pointComplex J (incidentVertex FK x)) :=
          mem_vertexSet_fullOn.mpr rfl
        have hpoint := retainedVertex_mem hx n
        have hball := containsBall_iteratedSubdivision (fullOn_full _ _).1 (fullOn_full _ _)
          (containsBall_incidentVertex FK x) n
        rw [one_mul] at hball
        exact hball (center F) ((graphSetEdist_le_edist hpoint).trans (hcenter F hmax ha x))
    have hball := containsBall_iteratedSubdivision (fullOn_full _ _).1 (fullOn_full _ _)
      (containsBall_containingFace FK) n
    rw [one_mul] at hball
    exact hball y ((graphSetEdist_le_edist hcontaining).trans (hmove F hmax ha))
  have hy : y ∈ vertexSet (iteratedAmbient J n).2
      (iteratedSubcomplex J (pointComplex J original) n) := by
    refine iterated_mem_of_forall (Q := fun F : {F : Face A // IsMax F ∧ a.val ∈ F.val} =>
      adjoiningFace K ⟨F.val.val, hAK F.val.property⟩) ?_ n y.property ?_
    · intro s hs hall
      refine ⟨hs, fun S hS => Subtype.ext ?_⟩
      apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      refine ⟨(K.isRelLowerSet_faces S.property).1, fun w hw => hcriterion a w ?_⟩
      intro F hmax ha
      have hjoin : S.val ∪ F.val ∈ K := (hall ⟨F, hmax, ha⟩).2 S hS
      exact (K.isRelLowerSet_faces hjoin).2
        (Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hw, Finset.subset_union_right⟩)
        (Finset.insert_nonempty _ _)
    · intro F
      exact hface F.val F.property.1 F.property.2
  exact Subtype.ext (Finset.singleton_injective (iterated_point_face original n hy))

/-- Inclusion on vertices of a subcomplex. -/
def includeVertex {J P : PreAbstractSimplicialComplex V} (hPJ : P ≤ J) (x : Vertex P) :
    Vertex J :=
  ⟨x.val, hPJ x.property⟩

private theorem iterated_le {J P : PreAbstractSimplicialComplex V} (hPJ : P ≤ J)
    (n : ℕ) : iteratedSubcomplex J P n ≤ (iteratedAmbient J n).2 := by
  cases n with
  | zero => exact hPJ
  | succ n => exact (subdivision_full _ _).1

private def retainIn {J P : PreAbstractSimplicialComplex V} (hPJ : P ≤ J)
    (n : ℕ) (x : Vertex P) : Vertex (iteratedSubcomplex J P n) :=
  ⟨(retainedVertex n (includeVertex hPJ x)).val, retainedVertex_mem (x := includeVertex hPJ x) x.property n⟩

private def subdivideIn {J P : PreAbstractSimplicialComplex V} (hPJ : P ≤ J)
    (x : Vertex P) : Vertex (subdivision J P) :=
  ⟨(subdividedVertex (includeVertex hPJ x)).val, singleton_subdivision.mpr x.property⟩

private theorem subdivision_adj_of_lt {J P : PreAbstractSimplicialComplex V}
    {s t : Vertex (subdivision J P)} (hst : s.val < t.val) :
    (skeleton (subdivision J P)).Adj s t := by
  let : DecidableEq (Face J) := Classical.decEq _
  refine ⟨fun he => hst.ne (congrArg Subtype.val he), Finset.insert_nonempty _ _, ?_, ?_⟩
  · simpa only [Finset.coe_insert, Finset.coe_singleton] using IsChain.pair hst
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact singleton_subdivision.mp s.property
    · obtain rfl := Finset.mem_singleton.mp hv
      exact singleton_subdivision.mp t.property

private theorem bisect_walk {J P : PreAbstractSimplicialComplex V} (hPJ : P ≤ J)
    {x y : Vertex P} (p : (skeleton P).Walk x y) :
    ∃ q : (skeleton (subdivision J P)).Walk (subdivideIn hPJ x) (subdivideIn hPJ y),
      q.length = 2 * p.length := by
  let : DecidableEq V := Classical.decEq _
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons x y z h p ih =>
    obtain ⟨q, hq⟩ := ih
    let m : Vertex (subdivision J P) :=
      ⟨⟨{x.val, y.val}, hPJ h.2⟩, singleton_subdivision.mpr h.2⟩
    have hne : x.val ≠ y.val := fun he => h.1 (Subtype.ext he)
    have hx : (subdivideIn hPJ x).val < m.val := by
      change ({x.val} : Finset V) ⊂ {x.val, y.val}
      refine Finset.ssubset_iff_subset_ne.mpr ⟨by simp, fun he => hne.symm ?_⟩
      exact Finset.mem_singleton.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hy : (subdivideIn hPJ y).val < m.val := by
      change ({y.val} : Finset V) ⊂ {x.val, y.val}
      refine Finset.ssubset_iff_subset_ne.mpr ⟨by simp, fun he => hne ?_⟩
      exact Finset.mem_singleton.mp (he ▸ Finset.mem_insert_self _ _)
    refine ⟨.cons (subdivision_adj_of_lt hx) (.cons (subdivision_adj_of_lt hy).symm q), ?_⟩
    change q.length + 1 + 1 = 2 * (p.length + 1)
    omega

private theorem iterated_walk {J P : PreAbstractSimplicialComplex V} (hPJ : P ≤ J)
    {x y : Vertex P} (p : (skeleton P).Walk x y) (n : ℕ) :
    ∃ q : (skeleton (iteratedSubcomplex J P n)).Walk (retainIn hPJ n x) (retainIn hPJ n y),
      q.length = 2 ^ n * p.length := by
  induction n with
  | zero => exact ⟨p, (Nat.one_mul _).symm⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨q', hq'⟩ := bisect_walk (iterated_le hPJ n) q
    exact ⟨q', hq'.trans (by rw [hq, pow_succ', Nat.mul_assoc])⟩

variable {W : Type u}

/-- The image of a face under a function defined on the vertices of its complex. -/
def faceImage {P : PreAbstractSimplicialComplex V} {J : PreAbstractSimplicialComplex W}
    (f : Vertex P → Vertex J) {s : Finset V} (hs : s ∈ P) : Finset W :=
  s.attach.image fun x => (f ⟨x.val, by exact singleton_mem_of_mem hs x.property⟩).val

/-- Two vertex maps are contiguous when their combined images of every source face
are an ambient face. This condition includes simpliciality of each map. -/
def Contiguous {P : PreAbstractSimplicialComplex V} {J : PreAbstractSimplicialComplex W}
    (f g : Vertex P → Vertex J) : Prop :=
  ∀ (s : Finset V) (hs : s ∈ P), faceImage f hs ∪ faceImage g hs ∈ J

private theorem mem_faceImage {P : PreAbstractSimplicialComplex V}
    {J : PreAbstractSimplicialComplex W} (f : Vertex P → Vertex J)
    {s : Finset V} (hs : s ∈ P) {x : Vertex P} (hx : x.val ∈ s) :
    (f x).val ∈ faceImage f hs :=
  Finset.mem_image.mpr ⟨⟨x.val, hx⟩, Finset.mem_attach _ _, rfl⟩

private theorem edist_le_one_of_face {J : PreAbstractSimplicialComplex V}
    {s : Finset V} (hs : s ∈ J) {x y : Vertex J} (hx : x.val ∈ s) (hy : y.val ∈ s) :
    (skeleton J).edist x y ≤ 1 := by
  let : DecidableEq V := Classical.decEq _
  apply edist_le_one_iff_adj_or_eq.mpr
  by_cases h : x = y
  · exact Or.inr h
  · exact Or.inl ⟨h, (J.isRelLowerSet_faces hs).2
      (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩)
      (Finset.insert_nonempty _ _)⟩

private theorem contiguous_walk_bounds {P : PreAbstractSimplicialComplex V}
    {J : PreAbstractSimplicialComplex W} {f g : Vertex P → Vertex J} (hfg : Contiguous f g)
    {x y : Vertex P} (p : (skeleton P).Walk x y) :
    (skeleton J).edist (f x) (f y) ≤ p.length ∧
      (skeleton J).edist (g x) (f y) ≤ ((max 1 p.length : ℕ) : ℕ∞) := by
  let : DecidableEq V := Classical.decEq _
  induction p with
  | @nil x =>
    exact ⟨by simp, by
      simpa only [Walk.length_nil, max_eq_left (Nat.zero_le 1), Nat.cast_one] using
        edist_le_one_of_face (hfg _ x.property)
          (Finset.mem_union_right _ (mem_faceImage g x.property (Finset.mem_singleton_self _)))
          (Finset.mem_union_left _ (mem_faceImage f x.property (Finset.mem_singleton_self _)))⟩
  | @cons x z y h p ih =>
    have hx : x.val ∈ ({x.val, z.val} : Finset V) := Finset.mem_insert_self _ _
    have hz : z.val ∈ ({x.val, z.val} : Finset V) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hF := edist_le_one_of_face (hfg _ h.2)
      (Finset.mem_union_left _ (mem_faceImage f h.2 hx))
      (Finset.mem_union_left _ (mem_faceImage f h.2 hz))
    have hG := edist_le_one_of_face (hfg _ h.2)
      (Finset.mem_union_right _ (mem_faceImage g h.2 hx))
      (Finset.mem_union_left _ (mem_faceImage f h.2 hz))
    have dist (v : Vertex J) (hv : (skeleton J).edist v (f z) ≤ 1) :
        (skeleton J).edist v (f y) ≤ ((p.length + 1 : ℕ) : ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
        ((skeleton J).edist_triangle (u := v) (v := f z) (w := f y)).trans
          (add_le_add hv ih.1)
    exact ⟨dist _ hF, (dist _ hG).trans
      (ENat.natCast_le_natCast.mpr (le_max_right _ _))⟩

/-- The ambient complex at depth zero, and at positive depth its iterated subdivision
starting from the first subdivision. -/
def ambientAtDepth (K : PreAbstractSimplicialComplex V) :
    ℕ → Σ X : Type u, PreAbstractSimplicialComplex X
  | 0 => ⟨V, K⟩
  | n + 1 => iteratedAmbient (sd K) n

/-- The base at the same depth, realized on the ambient vertex carrier. -/
def baseAtDepth (K A : PreAbstractSimplicialComplex V) :
    (r : ℕ) → PreAbstractSimplicialComplex (ambientAtDepth K r).1
  | 0 => A
  | n + 1 => iteratedSubcomplex (sd K) (subdivision K A) n

/-- The subdivided base is a subcomplex of the ambient subdivision at the same depth. -/
theorem baseAtDepth_le {K A : PreAbstractSimplicialComplex V} (hAK : A ≤ K) (r : ℕ) :
    baseAtDepth K A r ≤ (ambientAtDepth K r).2 := by
  cases r with
  | zero => exact hAK
  | succ n => exact iterated_le (subdivision_full _ _).1 n

/-- The vertex of the subdivided base retained from an original base vertex. -/
def baseVertexAtDepth {K A : PreAbstractSimplicialComplex V} (hAK : A ≤ K)
    (r : ℕ) (a : Vertex A) : Vertex (baseAtDepth K A r) :=
  match r with
  | 0 => a
  | n + 1 =>
    ⟨(retainedVertex n (subdividedVertex (includeVertex hAK a))).val, by
      exact retainedVertex_mem (singleton_subdivision.mpr a.property) n⟩

private def facetVertex {K A : PreAbstractSimplicialComplex V} (hAK : A ≤ K)
    (F : Face A) : Vertex (subdivision K A) :=
  ⟨⟨F.val, hAK F.property⟩, singleton_subdivision.mpr F.property⟩

private theorem incident_face_walk {K A : PreAbstractSimplicialComplex V} (hAK : A ≤ K)
    (F : Face A) (x : Vertex A) (hx : x.val ∈ F.val) :
    ∃ p : (skeleton (subdivision K A)).Walk (subdivideIn hAK x) (facetVertex hAK F),
      p.length ≤ 1 := by
  have hle : (subdivideIn hAK x).val ≤ (facetVertex hAK F).val :=
    Finset.singleton_subset_iff.mpr hx
  by_cases he : (subdivideIn hAK x).val = (facetVertex hAK F).val
  · have h : subdivideIn hAK x = facetVertex hAK F := Subtype.ext he
    let p : (skeleton (subdivision K A)).Walk (subdivideIn hAK x) (subdivideIn hAK x) := .nil
    exact ⟨p.copy rfl h, (Walk.length_copy _ _ _).le.trans (Nat.zero_le _)⟩
  · exact ⟨(subdivision_adj_of_lt (lt_of_le_of_ne hle he)).toWalk, le_rfl⟩

private theorem first_move_zero {K A : PreAbstractSimplicialComplex V} (hAK : A ≤ K)
    (hcriterion : MaximalFaceCriterion K A) {f g : Vertex A → Vertex K}
    (hfg : Contiguous f g) (hf : ∀ x, f x = includeVertex hAK x) (a : Vertex A) :
    g a = includeVertex hAK a := by
  apply Subtype.ext
  apply hcriterion a
  intro F _ ha
  have hface := hfg F.val F.property
  refine (K.isRelLowerSet_faces hface).2 (Finset.insert_subset_iff.mpr ⟨?_, ?_⟩)
    (Finset.insert_nonempty _ _)
  · exact Finset.mem_union_right _ (mem_faceImage g F.property ha)
  · intro x hx
    let v : Vertex A := ⟨x, singleton_mem_of_mem F.property hx⟩
    have hmem := mem_faceImage f F.property (x := v) hx
    rw [hf v] at hmem
    exact Finset.mem_union_left _ hmem

private theorem first_move_positive {K A : PreAbstractSimplicialComplex V} (hAK : A ≤ K)
    (hcriterion : MaximalFaceCriterion K A) (n : ℕ)
    {f g : Vertex (baseAtDepth K A (n + 1)) → Vertex (ambientAtDepth K (n + 1)).2}
    (hfg : Contiguous f g)
    (hf : ∀ x, f (baseVertexAtDepth hAK (n + 1) x) =
      includeVertex (baseAtDepth_le hAK (n + 1)) (baseVertexAtDepth hAK (n + 1) x))
    (a : Vertex A) :
    g (baseVertexAtDepth hAK (n + 1) a) =
      includeVertex (baseAtDepth_le hAK (n + 1)) (baseVertexAtDepth hAK (n + 1) a) := by
  let hsub : subdivision K A ≤ sd K := (subdivision_full K A).1
  let center (F : Face A) := f (retainIn hsub n (facetVertex hAK F))
  have hpath (F : Face A) (x : Vertex A) (hx : x.val ∈ F.val) :
      ∃ p : (skeleton (baseAtDepth K A (n + 1))).Walk
          (baseVertexAtDepth hAK (n + 1) x) (retainIn hsub n (facetVertex hAK F)),
        p.length ≤ 2 ^ n := by
    obtain ⟨p, hp⟩ := incident_face_walk hAK F x hx
    obtain ⟨q, hq⟩ := iterated_walk hsub p n
    exact ⟨q, hq.le.trans ((Nat.mul_le_mul_left _ hp).trans (Nat.mul_one _).le)⟩
  apply fixed_of_incident_face_distances hAK hcriterion a n center
  · intro F _ _ x
    let v : Vertex A := ⟨x.val, singleton_mem_of_mem F.property x.property⟩
    obtain ⟨p, hp⟩ := hpath F v x.property
    have h := (contiguous_walk_bounds hfg p).1.trans (ENat.natCast_le_natCast.mpr hp)
    rw [hf v, edist_comm] at h
    exact h
  · intro F _ ha
    obtain ⟨p, hp⟩ := hpath F a ha
    exact (contiguous_walk_bounds hfg p).2.trans (ENat.natCast_le_natCast.mpr
      (max_le (Nat.one_le_pow _ _ (by decide)) hp))

/-- If one map fixes all original base vertices, any contiguous map fixes them as well.
Both maps have the same subdivision depth in the base and in the ambient complex. -/
theorem contiguous_preserves_original_vertices {K A : PreAbstractSimplicialComplex V}
    (hAK : A ≤ K) (hcriterion : MaximalFaceCriterion K A) (r : ℕ)
    {f g : Vertex (baseAtDepth K A r) → Vertex (ambientAtDepth K r).2}
    (hfg : Contiguous f g)
    (hf : ∀ a, f (baseVertexAtDepth hAK r a) =
      includeVertex (baseAtDepth_le hAK r) (baseVertexAtDepth hAK r a)) (a : Vertex A) :
    g (baseVertexAtDepth hAK r a) =
      includeVertex (baseAtDepth_le hAK r) (baseVertexAtDepth hAK r a) := by
  cases r with
  | zero => exact first_move_zero hAK hcriterion hfg hf a
  | succ n => exact first_move_positive hAK hcriterion n hfg hf a

/-- Every map reached by a finite contiguity chain from the same-depth inclusion fixes
all original base vertices. Applying the theorem to any prefix also fixes those vertices
at every stage of the chain. -/
theorem contiguity_chain_fixes_original_vertices {K A : PreAbstractSimplicialComplex V}
    (hAK : A ≤ K) (hcriterion : MaximalFaceCriterion K A) (r : ℕ)
    {g : Vertex (baseAtDepth K A r) → Vertex (ambientAtDepth K r).2}
    (hchain : Relation.ReflTransGen Contiguous (includeVertex (baseAtDepth_le hAK r)) g)
    (a : Vertex A) :
    g (baseVertexAtDepth hAK r a) =
      includeVertex (baseAtDepth_le hAK r) (baseVertexAtDepth hAK r a) := by
  revert a
  induction hchain with
  | refl => intro a; rfl
  | tail _ hstep ih =>
    exact contiguous_preserves_original_vertices hAK hcriterion r hstep ih

end

end D5.S3.Topology.BarycentricBaseRigidity
