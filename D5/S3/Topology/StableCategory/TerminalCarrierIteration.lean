/- GID: D5/S3/Topology/StableCategory/TerminalCarrierIteration
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-refinement)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Accelerated parameter maps transport fixed-target graph contractions. -/

import D5.S3.Topology.StableCategory.GraphCarrierContiguity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.TerminalCarrierIteration

open BarycentricGraphDistance (Face Vertex subdivisionGraph)
open BarycentricBaseRigidity (Contiguous faceImage retainedVertex sd skeleton vertexOfFace)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open GraphSubdivisionIntervals (originalSupport originalSupport_mem)
open OrdinaryContiguityLift (Simplicial comp_chains comp_image iterate_comp lift_iterates
  ofTotal of_total_simplicial subdivide subdivide_of_total)
open PathContiguity (intervalComplex)
open Relation (ReflTransGen)
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private constant_face_image faceMap from D5.S3.Topology.StableCategory.OrdinaryContiguityLift
open OrdinarySubdivisionMap (iterate)
open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private exists_bisected_walk singletonFace from D5.S3.Topology.BarycentricGraphDistance

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {X Y : Type}

/-- Ordinary subdivision preserves edge connectedness: old edges become
two-step walks, and every new vertex is joined to a vertex of its face. -/
theorem subdivision_connected (A : PreAbstractSimplicialComplex X)
    (connected : ∀ a b : Vertex A, (skeleton A).Reachable a b) (n : ℕ) :
    ∀ a b : Vertex (iteratedAmbient A n).2,
      (skeleton (iteratedAmbient A n).2).Reachable a b := by
  induction n with
  | zero => exact connected
  | succ n ih =>
    let J := (iteratedAmbient A n).2
    change ∀ a b : Vertex (sd J), (skeleton (sd J)).Reachable a b
    have edge {a b : Face J} (hab : (subdivisionGraph J).Adj a b) :
        (skeleton (sd J)).Adj (vertexOfFace J a) (vertexOfFace J b) := by
      refine ⟨fun h => hab.ne (congrArg Subtype.val h), ?_⟩
      change ({a, b} : Finset (Face J)) ∈ sd J
      refine ⟨by simp, ?_, fun f _ => f.property⟩
      intro x hx y hy hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hne rfl).elim
      · exact hab
      · exact hab.symm
      · exact (hne rfl).elim
    have bisect {a b : Face J} (p : (subdivisionGraph J).Walk a b) :
        (skeleton (sd J)).Reachable (vertexOfFace J a) (vertexOfFace J b) := by
      induction p with
      | nil => exact SimpleGraph.Reachable.rfl
      | cons h _ hp => exact (edge h).reachable.trans hp
    have attach (u : Vertex (sd J)) :
        ∃ a : Vertex J,
          (skeleton (sd J)).Reachable (vertexOfFace J (singletonFace a)) u := by
      obtain ⟨x, hx⟩ := (J.isRelLowerSet_faces u.val.property).1
      let a : Vertex J := ⟨x, (J.isRelLowerSet_faces u.val.property).2
        (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty _)⟩
      have hle : singletonFace a ≤ u.val := Finset.singleton_subset_iff.mpr hx
      refine ⟨a, ?_⟩
      rcases lt_or_eq_of_le hle with h | h
      · exact (edge (Or.inl h)).reachable
      · have he : vertexOfFace J (singletonFace a) = u := Subtype.ext h
        rw [he]
    intro u v
    obtain ⟨a, ha⟩ := attach u
    obtain ⟨b, hb⟩ := attach v
    obtain ⟨p⟩ := ih a b
    obtain ⟨q, _⟩ := exists_bisected_walk p
    exact ha.symm.trans ((bisect q).trans hb)

/-- Original support is the union of the supports of its vertices. -/
theorem originalSupport_singletons (A : PreAbstractSimplicialComplex X) (m : ℕ)
    (s : Finset (iteratedAmbient A m).1) :
    originalSupport A m s =
      s.biUnion (fun v => originalSupport A m {v}) := by
  induction m with
  | zero => exact Finset.biUnion_singleton_eq_self.symm
  | succ m ih =>
      change originalSupport A m (s.biUnion Subtype.val) =
        s.biUnion (fun v => originalSupport A m (({v} : Finset _).biUnion Subtype.val))
      simp only [Finset.singleton_biUnion]
      calc
        _ = (s.biUnion Subtype.val).biUnion (fun u => originalSupport A m {u}) := ih _
        _ = s.biUnion (fun v => v.val.biUnion (fun u => originalSupport A m {u})) :=
          Finset.biUnion_biUnion _ _ _
        _ = _ := Finset.biUnion_congr rfl (fun v _ => (ih v.val).symm)

/-- Original support is monotone in the current face. -/
theorem originalSupport_mono (A : PreAbstractSimplicialComplex X) (m : ℕ)
    {s t : Finset (iteratedAmbient A m).1} (h : s ⊆ t) :
    originalSupport A m s ⊆ originalSupport A m t := by
  induction m with
  | zero => exact h
  | succ m ih =>
      exact ih (Finset.biUnion_subset_biUnion_of_subset_left Subtype.val h)

/-- The equality supplied by `iterated_ambient_add` transports a finset of
vertices from an iterated subdivision viewed in two stages to the single
iterated subdivision. -/
def rebracketFinset (A : PreAbstractSimplicialComplex X) (a b : ℕ)
    (s : Finset (iteratedAmbient (iteratedAmbient A a).2 b).1) :
    Finset (iteratedAmbient A (a + b)).1 :=
  cast
    (congrArg (fun J : Σ V : Type, PreAbstractSimplicialComplex V => Finset J.1)
      (OrdinaryContiguityLift.iterated_ambient_add A a b)) s

private theorem cast_biUnion_subtype
    {J K : Σ V : Type, PreAbstractSimplicialComplex V} (h : J = K)
    (s : Finset (Face J.2)) :
    cast (congrArg (fun T : Σ V : Type, PreAbstractSimplicialComplex V => Finset T.1) h)
        (s.biUnion Subtype.val) =
      (cast
        (congrArg (fun T : Σ V : Type, PreAbstractSimplicialComplex V =>
          Finset (Face T.2)) h) s).biUnion Subtype.val := by
  cases h
  rfl

/-- The support of a rebracketed finset is its outer support followed by
its support in the original complex. -/
theorem originalSupport_rebracket (A : PreAbstractSimplicialComplex X) (a b : ℕ)
    (s : Finset (iteratedAmbient (iteratedAmbient A a).2 b).1) :
    originalSupport A (a + b) (rebracketFinset A a b s) =
      originalSupport A a
        (originalSupport (iteratedAmbient A a).2 b s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      let h := OrdinaryContiguityLift.iterated_ambient_add A a b
      change originalSupport A (a + b)
          ((cast (congrArg (fun T : Σ V : Type, PreAbstractSimplicialComplex V =>
            Finset (Face T.2)) h) s).biUnion Subtype.val) =
        originalSupport A a
          (originalSupport (iteratedAmbient A a).2 b (s.biUnion Subtype.val))
      rw [← cast_biUnion_subtype h s]
      exact ih (s.biUnion Subtype.val)

/-- A map between subdivision levels preserves carriers if the original
support of its value is contained in that of its input. -/
def CarrierPreserving (A : PreAbstractSimplicialComplex X) (a c : ℕ)
    (f : Vertex (iteratedAmbient A a).2 → Vertex (iteratedAmbient A c).2) : Prop :=
  ∀ u, originalSupport A c {(f u).val} ⊆ originalSupport A a {u.val}

/-- The total-label subdivision API preserves support after rebracketing.
The support hypothesis is only required at actual vertices. -/
theorem originalSupport_iterate_image_subset (A : PreAbstractSimplicialComplex X)
    (a c : ℕ) (f : (iteratedAmbient A a).1 → (iteratedAmbient A c).1)
    (hf : ∀ t ∈ (iteratedAmbient A a).2, image t f ∈ (iteratedAmbient A c).2)
    (hcarrier : CarrierPreserving A a c (OrdinaryContiguityLift.ofTotal f hf))
    (r : ℕ) (s : Finset (iteratedAmbient (iteratedAmbient A a).2 r).1)
    (hs : s ∈ (iteratedAmbient (iteratedAmbient A a).2 r).2) :
    originalSupport A (c + r)
        (rebracketFinset A c r (image s (OrdinarySubdivisionMap.iterate f hf r).val)) ⊆
      originalSupport A (a + r) (rebracketFinset A a r s) := by
  rw [originalSupport_rebracket A c r, originalSupport_rebracket A a r,
    OrdinarySubdivisionMap.originalSupport_image f hf]
  let t := originalSupport (iteratedAmbient A a).2 r s
  have ht : t ∈ (iteratedAmbient A a).2 := originalSupport_mem r hs
  change originalSupport A c (image t f) ⊆ originalSupport A a t
  rw [originalSupport_singletons A c, originalSupport_singletons A a]
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
  let v : Vertex (iteratedAmbient A a).2 := ⟨u,
    ((iteratedAmbient A a).2.isRelLowerSet_faces ht).2
      (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_nonempty _)⟩
  exact Finset.mem_biUnion.mpr ⟨u, hu, hcarrier v hxy⟩

/-- The subdivision of a simplicial map is simplicial. -/
private theorem subdivide_simplicial {P : PreAbstractSimplicialComplex X}
    {Q : PreAbstractSimplicialComplex Y} (f : Vertex P → Vertex Q)
    (hf : Simplicial f) : Simplicial (subdivide f hf) := by
  intro s hs
  let F := faceMap f hf
  have himage : faceImage (subdivide f hf) hs = s.image F := by
    ext y
    rw [mem_faceImage_iff, Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.val, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨vertexOfFace P v, hv, rfl⟩
  rw [himage]
  refine ⟨hs.1.image _, ?_, fun v _ => v.property⟩
  intro x hx y hy hne
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  rcases hs.2.1 hu hv (fun h => hne (congrArg (fun z => F z) h)) with huv | hvu
  · exact Or.inl (lt_of_le_of_ne (F.monotone huv.le) hne)
  · exact Or.inr (lt_of_le_of_ne (F.monotone hvu.le) hne.symm)

/-- One ordinary subdivision preserves the old-carrier containment. -/
theorem subdivide_preserves_carrier (A : PreAbstractSimplicialComplex X) (a c : ℕ)
    (f : Vertex (iteratedAmbient A a).2 → Vertex (iteratedAmbient A c).2)
    (hf : Simplicial f) (hcarrier : CarrierPreserving A a c f) :
    CarrierPreserving A (a + 1) (c + 1) (subdivide f hf) := by
  intro u
  change originalSupport A c
      (({(subdivide f hf u).val} : Finset _).biUnion Subtype.val) ⊆
    originalSupport A a (({u.val} : Finset _).biUnion Subtype.val)
  simp only [Finset.singleton_biUnion]
  change originalSupport A c (faceImage f u.val.property) ⊆
    originalSupport A a u.val.val
  rw [originalSupport_singletons, originalSupport_singletons]
  intro x hx
  obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨w, hw, hfw⟩ := (mem_faceImage_iff f u.val.property v).mp hv
  exact Finset.mem_biUnion.mpr ⟨w.val, hw, hcarrier w (hfw.symm ▸ hxv)⟩

/-- Iterate subdivision on actual vertices, keeping the depths in sum form. -/
def iteratedCarrierMap (A : PreAbstractSimplicialComplex X) (a c : ℕ)
    (f : Vertex (iteratedAmbient A a).2 → Vertex (iteratedAmbient A c).2)
    (hf : Simplicial f) :
    (r : ℕ) →
      {g : Vertex (iteratedAmbient A (a + r)).2 →
        Vertex (iteratedAmbient A (c + r)).2 // Simplicial g}
  | 0 => ⟨f, hf⟩
  | r + 1 =>
      let g := iteratedCarrierMap A a c f hf r
      ⟨subdivide g.1 g.2, subdivide_simplicial g.1 g.2⟩

/-- Iteration preserves the carrier condition. -/
theorem iteratedCarrierMap_preserves_carrier (A : PreAbstractSimplicialComplex X)
    (a c : ℕ) (f : Vertex (iteratedAmbient A a).2 → Vertex (iteratedAmbient A c).2)
    (hf : Simplicial f) (hcarrier : CarrierPreserving A a c f) (r : ℕ) :
    CarrierPreserving A (a + r) (c + r) (iteratedCarrierMap A a c f hf r).1 := by
  induction r with
  | zero => exact hcarrier
  | succ r ih =>
      exact subdivide_preserves_carrier A (a + r) (c + r)
        (iteratedCarrierMap A a c f hf r).1 (iteratedCarrierMap A a c f hf r).2 ih

/-- Carrier containment is transitive under composition of vertex maps. -/
theorem CarrierPreserving.comp (A : PreAbstractSimplicialComplex X) {a b c : ℕ}
    {f : Vertex (iteratedAmbient A a).2 → Vertex (iteratedAmbient A b).2}
    {g : Vertex (iteratedAmbient A b).2 → Vertex (iteratedAmbient A c).2}
    (hg : CarrierPreserving A b c g) (hf : CarrierPreserving A a b f) :
    CarrierPreserving A a c (g ∘ f) :=
  fun u => (hg (f u)).trans (hf u)

/-- A face-member selector preserves carriers at any depth. -/
theorem selector_preserves_carrier (A : PreAbstractSimplicialComplex X) (r : ℕ)
    (f : Vertex (iteratedAmbient A (r + 1)).2 → Vertex (iteratedAmbient A r).2)
    (hf : ∀ u, (f u).val ∈ u.val.val) :
    CarrierPreserving A (r + 1) r f := by
  intro u
  change originalSupport A r {(f u).val} ⊆
    originalSupport A r (({u.val} : Finset _).biUnion Subtype.val)
  rw [Finset.singleton_biUnion]
  exact originalSupport_mono A r (Finset.singleton_subset_iff.mpr (hf u))

/-- A face-member selector at one subdivision step. -/
structure SelectorStep (A : PreAbstractSimplicialComplex X) (r : ℕ) where
  map : Vertex (iteratedAmbient A (r + 1)).2 → Vertex (iteratedAmbient A r).2
  simplicial : Simplicial map
  member : ∀ u, (map u).val ∈ u.val.val

private theorem flag_has_top {U : Type} (J : PreAbstractSimplicialComplex U)
    {s : Finset (Face J)} (hs : s ∈ sd J) :
    ∃ top ∈ s, ∀ u ∈ s, u ≤ top := by
  obtain ⟨top, htop, hcard⟩ :=
    Finset.exists_max_image s (fun u : Face J => u.val.card) hs.1
  refine ⟨top, htop, fun u hu => ?_⟩
  by_cases he : u = top
  · exact he.le
  rcases hs.2.1 hu htop he with h | h
  · exact h.le
  · exact (not_lt_of_ge (hcard u hu) (Finset.card_lt_card h)).elim

/-- Choosing a member of every face gives a simplicial map out of the
ordinary subdivision. All labels in a flag lie in its greatest face. -/
def chooseSelectorStep (A : PreAbstractSimplicialComplex X) (r : ℕ) :
    SelectorStep A r := by
  let J := (iteratedAmbient A r).2
  let member (u : Face J) := (J.isRelLowerSet_faces u.property).1
  let pick (u : Face J) : Vertex J :=
    ⟨(member u).choose, (J.isRelLowerSet_faces u.property).2
      (Finset.singleton_subset_iff.mpr (member u).choose_spec) (Finset.singleton_nonempty _)⟩
  refine ⟨fun u => pick u.val, ?_, fun u => (member u.val).choose_spec⟩
  intro s hs
  obtain ⟨top, _, hle⟩ := flag_has_top J hs
  apply (J.isRelLowerSet_faces top.property).2
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := (mem_faceImage_iff (fun u => pick u.val) hs a).mp ha
    exact (hle u.val hu) (member u.val).choose_spec
  · exact hs.1.attach.image _

/-- Face-member selection commutes with an arbitrary simplicial map up to
one contiguity. Both routes on a flag land in the image of its largest face. -/
theorem selector_naturality {P : PreAbstractSimplicialComplex X}
    {Q : PreAbstractSimplicialComplex Y} (f : Vertex P → Vertex Q) (hf : Simplicial f)
    (p : Vertex (sd P) → Vertex P) (q : Vertex (sd Q) → Vertex Q)
    (hp : ∀ u, (p u).val ∈ u.val.val) (hq : ∀ u, (q u).val ∈ u.val.val) :
    Contiguous (f ∘ p) (q ∘ subdivide f hf) := by
  intro s hs
  obtain ⟨top, _, hle⟩ := flag_has_top P hs
  have left : faceImage (f ∘ p) hs ⊆ faceImage f top.property := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (mem_faceImage_iff (f ∘ p) hs y).mp hy
    exact (mem_faceImage_iff f top.property _).mpr ⟨p u, hle _ hu (hp u), rfl⟩
  have right : faceImage (q ∘ subdivide f hf) hs ⊆ faceImage f top.property := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (mem_faceImage_iff (q ∘ subdivide f hf) hs y).mp hy
    have hm := hq (subdivide f hf u)
    change (q (subdivide f hf u)).val ∈ faceImage f u.val.property at hm
    obtain ⟨v, hv, he⟩ := (mem_faceImage_iff f u.val.property _).mp hm
    exact (mem_faceImage_iff f top.property _).mpr ⟨v, hle _ hu hv, he⟩
  exact (Q.isRelLowerSet_faces (hf _ top.property)).2 (Finset.union_subset left right)
    ((hs.1.attach.image _).mono Finset.subset_union_left)

private theorem identity_simplicial (P : PreAbstractSimplicialComplex X) :
    Simplicial (id : Vertex P → Vertex P) := by
  intro s hs
  change s.attach.image (fun x => x.val) ∈ P
  simpa only [Finset.attach_image_val] using hs

/-- The composite of the first `m` selector steps, with its simplicial proof. -/
def selectorIterate (A : PreAbstractSimplicialComplex X)
    (σ : ∀ r, SelectorStep A r) :
    (m : ℕ) →
      {f : Vertex (iteratedAmbient A m).2 → Vertex A // Simplicial f}
  | 0 => ⟨id, identity_simplicial A⟩
  | m + 1 =>
      let p := selectorIterate A σ m
      let q := σ m
      ⟨p.1 ∘ q.map, Simplicial.comp p.2 q.simplicial⟩

/-- Every composed selector remains in the original support of its input. -/
theorem selectorIterate_carrier
    (A : PreAbstractSimplicialComplex X) (σ : ∀ r, SelectorStep A r) :
    ∀ m, CarrierPreserving A m 0 (selectorIterate A σ m).1 := by
  intro m
  induction m with
  | zero =>
      intro u
      exact Finset.Subset.rfl
  | succ m ih =>
      change CarrierPreserving A (m + 1) 0 ((selectorIterate A σ m).1 ∘ (σ m).map)
      exact CarrierPreserving.comp A (c := 0) (f := (σ m).map)
        (g := (selectorIterate A σ m).1) ih
        (selector_preserves_carrier A m (σ m).map (σ m).member)

/-- The composed selector meets the membership hypothesis of the fixed-target
geometric contraction. -/
theorem selectorIterate_mem (A : PreAbstractSimplicialComplex X)
    (σ : ∀ r, SelectorStep A r) (m : ℕ) (u : Vertex (iteratedAmbient A m).2) :
    ((selectorIterate A σ m).1 u).val ∈ originalSupport A m {u.val} :=
  selectorIterate_carrier A σ m u (Finset.mem_singleton_self _)

/-- Transport a carrier map along equalities of the ambient Sigma objects. -/
def castCarrierMap {J J' K K' : Σ V : Type, PreAbstractSimplicialComplex V}
    (hs : J = J') (ht : K = K')
    (f : Vertex J.2 → Vertex K.2) : Vertex J'.2 → Vertex K'.2 :=
  fun u => cast (congrArg (fun T : Σ V : Type, PreAbstractSimplicialComplex V =>
      Vertex T.2) ht) (f (cast (congrArg (fun T : Σ V : Type,
      PreAbstractSimplicialComplex V => Vertex T.2) hs.symm) u))

theorem castCarrierMap_simplicial
    {J J' K K' : Σ V : Type, PreAbstractSimplicialComplex V}
    (hs : J = J') (ht : K = K') (f : Vertex J.2 → Vertex K.2)
    (hf : Simplicial f) :
    Simplicial (castCarrierMap hs ht f) := by
  cases hs
  cases ht
  exact hf

/-- Carrier support is invariant under a change of depth indices. -/
theorem castCarrierMap_preserves_carrier (A : PreAbstractSimplicialComplex X)
    {a a' c c' : ℕ} (ha : a = a') (hc : c = c')
    (f : Vertex (iteratedAmbient A a).2 → Vertex (iteratedAmbient A c).2)
    (hf : CarrierPreserving A a c f) :
    CarrierPreserving A a' c'
      (castCarrierMap (congrArg (iteratedAmbient A) ha) (congrArg (iteratedAmbient A) hc) f) := by
  cases ha
  cases hc
  exact hf

/-- The parameter map obtained by three simultaneous subdivisions
and one extra backward selector at each round. -/
def acceleratedCarrier (A : PreAbstractSimplicialComplex X)
    (select : ∀ k, SelectorStep A (4 * k + 3)) :
    (m : ℕ) →
      {f : Vertex (iteratedAmbient A (4 * m)).2 →
        Vertex (iteratedAmbient A (3 * m)).2 // Simplicial f}
  | 0 => ⟨id, identity_simplicial A⟩
  | m + 1 =>
      let old := acceleratedCarrier A select m
      let lift := iteratedCarrierMap A (4 * m) (3 * m) old.1 old.2 3
      let step := select m
      let hs := congrArg (iteratedAmbient A) (show 4 * m + 3 + 1 = 4 * (m + 1) from (Nat.mul_succ 4 m).symm)
      let ht := congrArg (iteratedAmbient A) (show 3 * m + 3 = 3 * (m + 1) from (Nat.mul_succ 3 m).symm)
      ⟨castCarrierMap hs ht (lift.1 ∘ step.map),
        castCarrierMap_simplicial hs ht _ (lift.2.comp step.simplicial)⟩

/-- The simultaneous parameter map keeps every final vertex within its
original carrier, even when selectors are chosen independently by round. -/
theorem accelerated_carrier_preserving (A : PreAbstractSimplicialComplex X)
    (select : ∀ k, SelectorStep A (4 * k + 3)) (m : ℕ) :
    CarrierPreserving A (4 * m) (3 * m) (acceleratedCarrier A select m).1 := by
  induction m with
  | zero => exact fun _ => Finset.Subset.rfl
  | succ m ih =>
      let old := acceleratedCarrier A select m
      let lift := iteratedCarrierMap A (4 * m) (3 * m) old.1 old.2 3
      let step := select m
      have hLift : CarrierPreserving A (4 * m + 3) (3 * m + 3) lift.1 :=
        iteratedCarrierMap_preserves_carrier A (4 * m) (3 * m) old.1 old.2 ih 3
      have hStep : CarrierPreserving A (4 * m + 3 + 1) (4 * m + 3) step.map :=
        selector_preserves_carrier A (4 * m + 3) step.map step.member
      exact castCarrierMap_preserves_carrier A
        (show 4 * m + 3 + 1 = 4 * (m + 1) from (Nat.mul_succ 4 m).symm)
        (show 3 * m + 3 = 3 * (m + 1) from (Nat.mul_succ 3 m).symm)
        (lift.1 ∘ step.map) (CarrierPreserving.comp A hLift hStep)

private theorem constant_iterate {U V : Type} {P : PreAbstractSimplicialComplex U}
    {Q : PreAbstractSimplicialComplex V} (b : Vertex Q)
    (hb : ∀ s ∈ P, image s (fun _ => b.val) ∈ Q) (n : ℕ) :
    ofTotal (iterate (fun _ => b.val) hb n).val (iterate (fun _ => b.val) hb n).property =
      (fun _ => retainedVertex n b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let t := iterate (fun _ => b.val) hb n
      change ofTotal (iterate t.val t.property 1).val (iterate t.val t.property 1).property = _
      rw [← subdivide_of_total]
      funext v
      apply Subtype.ext
      apply Subtype.ext
      change faceImage (ofTotal t.val t.property) v.val.property = {(retainedVertex n b).val}
      rw [ih, constant_face_image]

private theorem transport_postcomposition
    {J J' L M : Σ V : Type, PreAbstractSimplicialComplex V}
    (h : J = J') (pre : Vertex J.2 → Vertex L.2) (post : Vertex L.2 → Vertex M.2)
    (b : Vertex M.2) (hc : ReflTransGen Contiguous (post ∘ pre) (fun _ => b)) :
    ReflTransGen Contiguous (post ∘ castCarrierMap h rfl pre) (fun _ => b) := by
  cases h
  exact hc

/-- A fixed-target contraction at source depth `m` induces a contraction
in the `r`-fold ambient subdivision for any carrier map from source
depth `m + r` to parameter depth `r`. -/
theorem contraction_after_synchronous_subdivision [Finite X]
    (A : PreAbstractSimplicialComplex X) (K : PreAbstractSimplicialComplex Y)
    (hdim : ∀ s ∈ A, (s : Finset X).card ≤ 2)
    (q : X → ℕ) (hq : ∀ s ∈ A, s.image q ∈ intervalComplex 1)
    (left right : {e : Face A // e.val.val.card = 2} → Vertex A)
    (orient : ∀ e, e.val.val = {(left e).val, (right e).val} ∧
      left e ≠ right e ∧ q (left e).val = 0 ∧ q (right e).val = 1)
    (m r : ℕ) (g : X → Y) (hg : ∀ s ∈ A, image s g ∈ K)
    (sel : (iteratedAmbient A m).1 → X)
    (hsel : ∀ s ∈ (iteratedAmbient A m).2, image s sel ∈ A)
    (hselSupport : CarrierPreserving A m 0 (ofTotal sel hsel))
    (b : Vertex K)
    (hcontract : ReflTransGen Contiguous
      (ofTotal (g ∘ sel) (comp_image sel hsel g hg)) (fun _ => b))
    (f : Vertex (iteratedAmbient A (m + r)).2 → Vertex (iteratedAmbient A r).2)
    (hf : Simplicial f) (hfSupport : CarrierPreserving A (m + r) r f) :
    ReflTransGen Contiguous
      (ofTotal (iterate g hg r).val (iterate g hg r).property ∘ f)
      (fun _ => retainedVertex r b) := by
  have finite (k : ℕ) : Finite (iteratedAmbient A k).1 := by
    induction k with
    | zero => exact ‹Finite X›
    | succ k hk =>
        letI := hk
        change Finite (Face (iteratedAmbient A k).2)
        infer_instance
  letI : Finite (iteratedAmbient A m).1 := finite m
  letI : Finite (iteratedAmbient A (m + r)).1 := finite (m + r)
  let h : iteratedAmbient (iteratedAmbient A m).2 r = iteratedAmbient A (m + r) :=
    OrdinaryContiguityLift.iterated_ambient_add A m r
  let S := iterate sel hsel r
  let lifted := ofTotal S.val S.property
  let terminal := castCarrierMap h rfl lifted
  have hterminal : Simplicial terminal :=
    castCarrierMap_simplicial h rfl lifted (of_total_simplicial _ _)
  have hterminalSupport : CarrierPreserving A (m + r) r terminal := by
    intro u
    let v : Vertex (iteratedAmbient (iteratedAmbient A m).2 r).2 :=
      cast (congrArg (fun T : Σ V : Type, PreAbstractSimplicialComplex V => Vertex T.2) h.symm) u
    have transport_singleton :
        rebracketFinset A m r {v.val} = {u.val} := by
      have eq (J J' : Σ V : Type, PreAbstractSimplicialComplex V)
          (e : J = J') (u' : Vertex J'.2) :
          cast (congrArg (fun T : Σ V : Type, PreAbstractSimplicialComplex V => Finset T.1) e)
            {((cast (congrArg (fun T : Σ V : Type, PreAbstractSimplicialComplex V =>
              Vertex T.2) e.symm) u').val)} = {u'.val} := by
        cases e
        rfl
      exact eq _ _ h u
    have hs := originalSupport_iterate_image_subset A m 0 sel hsel hselSupport r {v.val} v.property
    have hzero (t : Finset (iteratedAmbient A r).1) :
        originalSupport A (0 + r) (rebracketFinset A 0 r t) = originalSupport A r t := by
      rw [originalSupport_rebracket]
      rfl
    have himage : image {v.val} S.val = {S.val v.val} := Finset.image_singleton _ _
    change originalSupport A (0 + r) (rebracketFinset A 0 r (image {v.val} S.val)) ⊆
      originalSupport A (m + r) (rebracketFinset A m r {v.val}) at hs
    rw [transport_singleton, himage, hzero] at hs
    exact hs
  have hc := GraphCarrierContiguity.supported_maps_contiguous A hdim q hq left right orient
    (m + r) r f terminal hf hterminal hfSupport hterminalSupport
  let post := ofTotal (iterate g hg r).val (iterate g hg r).property
  have comparison := comp_chains (id : Vertex (iteratedAmbient A (m + r)).2 → _)
    post (identity_simplicial _) (of_total_simplicial _ _) hc
  have hconst : ∀ s ∈ (iteratedAmbient A m).2, image s (fun _ => b.val) ∈ K := by
    intro s hs
    have he : image s (fun _ => b.val) = {b.val} :=
      Finset.image_const ((iteratedAmbient A m).2.isRelLowerSet_faces hs).1 _
    rw [he]
    exact b.property
  have contraction := lift_iterates (g ∘ sel) (fun _ => b.val)
    (comp_image sel hsel g hg) hconst hcontract r
  have hstart :
      ofTotal (iterate (g ∘ sel) (comp_image sel hsel g hg) r).val
        (iterate (g ∘ sel) (comp_image sel hsel g hg) r).property = post ∘ lifted := by
    funext v
    apply Subtype.ext
    exact congrFun (iterate_comp sel hsel g hg r) v.val
  rw [hstart, constant_iterate b hconst r] at contraction
  exact comparison.trans (transport_postcomposition h lifted post _ contraction)

end

end D5.S3.Topology.StableCategory.TerminalCarrierIteration
