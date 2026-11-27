/- GID: D5/S3/Topology/RelativeDerivedContiguity
   generality: G
   mirror-B: D5/B/S3/Topology/RelativeDerivedContiguity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic, mathlib/module/Mathlib.Data.Finset.Sum]
   utility: none
   digest: Relative derived subdivisions preserve contiguity classes under full-base and vertex-membership preservation hypotheses. -/

module

public import D5.S3.Topology.DescendingClosureContiguity
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Sum

/-! Relative face flags keep vertices of a full base and replace outside
faces by their barycenters. Comparable outside-face maps can be interpolated
while the old base is held fixed. -/

@[expose] public section
set_option autoImplicit false

namespace D5.S3.Topology.RelativeDerivedContiguity

open D5.S3.Topology.DescendingClosureContiguity (exists_relative_contiguity_of_le)

variable {V W P Q : Type*} [DecidableEq W]
variable [PartialOrder P] [PartialOrder Q]

/-- The mixed-simplex condition for old base vertices and a flag of outside
faces. The right vertices are indexed by the carriers of their barycenters. -/
def mixedSimplex (base : PreAbstractSimplicialComplex V) (carrier : P → Finset V)
    (old : Finset V) (flag : Set P) : Prop :=
  (old.Nonempty → old ∈ base) ∧ IsChain (· ≤ ·) flag ∧
    ∀ a ∈ flag, old ⊆ carrier a

/-- Contiguity of two maps preserving the old/exterior decomposition of
a relative derived subdivision, expressed on the mixed simplices. -/
def mixedContiguous
    (sourceBase : PreAbstractSimplicialComplex V) (sourceCarrier : P → Finset V)
    (targetBase : PreAbstractSimplicialComplex W) (targetCarrier : Q → Finset W)
    (f g : V → W) (F G : P →o Q) : Prop :=
  ∀ old flag, mixedSimplex sourceBase sourceCarrier old flag →
    mixedSimplex targetBase targetCarrier
      (old.image f ∪ old.image g) (F '' flag ∪ G '' flag)

/-- A change of the exterior face map through pointwise containment gives
contiguity in the relative subdivision while the old base map stays fixed. -/
theorem fixedBase_interpolation
    (sourceBase : PreAbstractSimplicialComplex V) (sourceCarrier : P → Finset V)
    (targetBase : PreAbstractSimplicialComplex W) (targetCarrier : Q → Finset W)
    (hmon : Monotone targetCarrier)
    (rank : P → ℕ) (hrank : StrictMono rank) (bound : ℕ) (hb : ∀ x, rank x ≤ bound)
    (f : V → W) (big small : P →o Q) (hle : ∀ x, small x ≤ big x)
    (hbase : ∀ old ∈ sourceBase, old.image f ∈ targetBase)
    (hinside : ∀ old flag, mixedSimplex sourceBase sourceCarrier old flag →
      ∀ a ∈ flag, old.image f ⊆ targetCarrier (small a)) :
    ∃ H : ℕ → P →o Q,
      H 0 = big ∧ H (bound + 1) = small ∧
      ∀ k, mixedContiguous sourceBase sourceCarrier targetBase targetCarrier f f
        (H k) (H (k + 1)) := by
  obtain ⟨H, h0, ht, _, hbound, hflag⟩ :=
    exists_relative_contiguity_of_le rank hrank big small hle bound hb
  refine ⟨H, h0, ht, ?_⟩
  intro k old C hC
  simp only [Finset.union_self]
  refine ⟨fun hn => hbase old (hC.1 (Finset.image_nonempty.mp hn)), hflag k C hC.2.1, ?_⟩
  intro a ha
  rcases ha with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · exact (hinside old C hC x hx).trans (hmon (hbound k x))
  · exact (hinside old C hC x hx).trans (hmon (hbound (k + 1) x))

/-- Once all exterior carriers contain both old images, a contiguous change
of the old base maps is contiguous in the relative subdivision. -/
theorem changeBase
    (sourceBase : PreAbstractSimplicialComplex V) (sourceCarrier : P → Finset V)
    (targetBase : PreAbstractSimplicialComplex W) (targetCarrier : Q → Finset W)
    (f g : V → W) (big : P →o Q)
    (hbase : ∀ old ∈ sourceBase, old.image f ∪ old.image g ∈ targetBase)
    (hinside : ∀ old flag, mixedSimplex sourceBase sourceCarrier old flag →
      ∀ a ∈ flag, old.image f ∪ old.image g ⊆ targetCarrier (big a)) :
    mixedContiguous sourceBase sourceCarrier targetBase targetCarrier f g big big := by
  intro old C hC
  simp only [Set.union_self]
  refine ⟨fun hn => hbase old (hC.1 ?_), hC.2.1.image big, ?_⟩
  · by_contra he
    simp only [Finset.not_nonempty_iff_eq_empty.mp he, Finset.image_empty,
      Finset.empty_union] at hn
    exact Finset.not_nonempty_empty hn
  · rintro _ ⟨x, hx, rfl⟩
    exact hinside old C hC x hx

/-- A common containing exterior face map and one contiguous base step
give a finite contiguity chain preserving the relative subdivision. -/
theorem interpolateMixedMaps
    (sourceBase : PreAbstractSimplicialComplex V) (sourceCarrier : P → Finset V)
    (targetBase : PreAbstractSimplicialComplex W) (targetCarrier : Q → Finset W)
    (hmon : Monotone targetCarrier)
    (rank : P → ℕ) (hrank : StrictMono rank) (bound : ℕ) (hb : ∀ x, rank x ≤ bound)
    (f g : V → W) (F G U : P →o Q)
    (hF : ∀ x, F x ≤ U x) (hG : ∀ x, G x ≤ U x)
    (hbaseF : ∀ old ∈ sourceBase, old.image f ∈ targetBase)
    (hbaseG : ∀ old ∈ sourceBase, old.image g ∈ targetBase)
    (hbaseUnion : ∀ old ∈ sourceBase, old.image f ∪ old.image g ∈ targetBase)
    (hinsideF : ∀ old flag, mixedSimplex sourceBase sourceCarrier old flag →
      ∀ a ∈ flag, old.image f ⊆ targetCarrier (F a))
    (hinsideG : ∀ old flag, mixedSimplex sourceBase sourceCarrier old flag →
      ∀ a ∈ flag, old.image g ⊆ targetCarrier (G a)) :
    Relation.ReflTransGen
      (fun a b : (V → W) × (P →o Q) =>
        mixedContiguous sourceBase sourceCarrier targetBase targetCarrier a.1 b.1 a.2 b.2)
      (f, F) (g, G) := by
  let R (a b : (V → W) × (P →o Q)) :=
    mixedContiguous sourceBase sourceCarrier targetBase targetCarrier a.1 b.1 a.2 b.2
  have hsymm (a b : (V → W) × (P →o Q)) (h : R a b) : R b a := by
    intro old C hC
    simpa only [Finset.union_comm, Set.union_comm] using h old C hC
  have chain (a : V → W) (T : P →o Q) (hT : ∀ x, T x ≤ U x)
      (hBase : ∀ old ∈ sourceBase, old.image a ∈ targetBase)
      (hIn : ∀ old C, mixedSimplex sourceBase sourceCarrier old C →
        ∀ x ∈ C, old.image a ⊆ targetCarrier (T x)) :
      Relation.ReflTransGen R (a, U) (a, T) ∧
        Relation.ReflTransGen R (a, T) (a, U) := by
    obtain ⟨H, h0, hlast, hstep⟩ := fixedBase_interpolation sourceBase sourceCarrier
      targetBase targetCarrier hmon rank hrank bound hb a U T hT hBase hIn
    have reach (k : ℕ) :
        Relation.ReflTransGen R (a, H 0) (a, H k) ∧
          Relation.ReflTransGen R (a, H k) (a, H 0) := by
      induction k with
      | zero => exact ⟨.refl, .refl⟩
      | succ k ih =>
        exact ⟨ih.1.tail (hstep k),
          (Relation.ReflTransGen.single (hsymm _ _ (hstep k))).trans ih.2⟩
    simpa only [h0, hlast] using reach (bound + 1)
  have middle : R (f, U) (g, U) := by
    apply changeBase sourceBase sourceCarrier targetBase targetCarrier f g U hbaseUnion
    intro old C hC a ha
    exact Finset.union_subset
      ((hinsideF old C hC a ha).trans (hmon (hF a)))
      ((hinsideG old C hC a ha).trans (hmon (hG a)))
  exact ((chain f F hF hbaseF hinsideF).2.tail middle).trans
    (chain g G hG hbaseG hinsideG).1

section ActualFaces

variable [Finite V]
variable {K A : PreAbstractSimplicialComplex V} {L B : PreAbstractSimplicialComplex W}

/-- Nonempty faces outside the fixed subcomplex are the exterior vertices. -/
abbrev OutsideFace {X : Type*} (M Base : PreAbstractSimplicialComplex X) :=
  {s : Finset X // s ∈ M ∧ s ∉ Base}

instance : Finite (OutsideFace K A) := by
  let inst := Fintype.ofFinite V
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- The exterior part of the relative subdivision of a simplicial map. -/
def outsideFaceImage (f : V → W) (hf : ∀ s ∈ K, s.image f ∈ L)
    (hfout : ∀ s ∈ K, s ∉ A → s.image f ∉ B) :
    OutsideFace K A →o OutsideFace L B where
  toFun s := ⟨s.val.image f, hf _ s.property.1, hfout _ s.property.1 s.property.2⟩
  monotone' := fun _ _ h => Finset.image_subset_image h

/-- A contiguous pair respecting the base and exterior conditions induces
maps in a common contiguity class for the relative derived mixed simplices. -/
theorem relative_face_contiguity (f g : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) (hg : ∀ s ∈ K, s.image g ∈ L)
    (hfout : ∀ s ∈ K, s ∉ A → s.image f ∉ B)
    (hgout : ∀ s ∈ K, s ∉ A → s.image g ∉ B)
    (hbaseF : ∀ s ∈ A, s.image f ∈ B) (hbaseG : ∀ s ∈ A, s.image g ∈ B)
    (hbaseUnion : ∀ s ∈ A, s.image f ∪ s.image g ∈ B)
    (hunion : ∀ s ∈ K, s.image f ∪ s.image g ∈ L) :
    Relation.ReflTransGen
      (fun a b : (V → W) × (OutsideFace K A →o OutsideFace L B) =>
        mixedContiguous A Subtype.val B Subtype.val a.1 b.1 a.2 b.2)
      (f, outsideFaceImage f hf hfout) (g, outsideFaceImage g hg hgout) := by
  let inst := Fintype.ofFinite V
  let unionMap : OutsideFace K A →o OutsideFace L B :=
    { toFun := fun s => ⟨s.val.image f ∪ s.val.image g, hunion _ s.property.1, by
      intro hm
      have hn := (K.isRelLowerSet_faces s.property.1).1
      exact hfout _ s.property.1 s.property.2 ((B.isRelLowerSet_faces hm).2
        Finset.subset_union_left (Finset.image_nonempty.mpr hn))⟩
      monotone' := fun _ _ h =>
        Finset.union_subset_union (Finset.image_subset_image h) (Finset.image_subset_image h) }
  let rank : OutsideFace K A → ℕ := fun s => s.val.card
  exact interpolateMixedMaps A Subtype.val B Subtype.val (fun _ _ h => h) rank
    (fun _ _ h => Finset.card_lt_card h) (Fintype.card V) (fun _ => Finset.card_le_univ _)
    f g (outsideFaceImage f hf hfout) (outsideFaceImage g hg hgout) unionMap
    (fun _ => Finset.subset_union_left) (fun _ => Finset.subset_union_right)
    hbaseF hbaseG hbaseUnion (fun _ _ hC a ha => Finset.image_subset_image (hC.2.2 a ha))
    (fun _ _ hC a ha => Finset.image_subset_image (hC.2.2 a ha))

end ActualFaces

section Complex

variable {K A : PreAbstractSimplicialComplex V} {L B : PreAbstractSimplicialComplex W}

/-- The relative derived complex on the old vertices and the barycenters of
the outside faces, with the base retaining its original simplices. -/
def relativeDerived (K A : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (V ⊕ OutsideFace K A) where
  faces := {s : Finset (V ⊕ OutsideFace K A) |
    s.Nonempty ∧ mixedSimplex A Subtype.val s.toLeft (s.toRight : Set (OutsideFace K A))}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    have hleft := Finset.toLeft_subset_toLeft hts
    have hright : (t.toRight : Set (OutsideFace K A)) ⊆ s.toRight :=
      Finset.toRight_subset_toRight hts
    refine ⟨ht, ?_, hs.2.2.1.mono hright, ?_⟩
    · intro htn
      obtain ⟨a, ha⟩ := htn
      exact (A.isRelLowerSet_faces (hs.2.1 ⟨a, hleft ha⟩)).2 hleft ⟨a, ha⟩
    · intro x hx
      exact hleft.trans (hs.2.2.2 x (hright hx))

/-- The original base embedded into the left summand of the subdivision. -/
noncomputable def retainedBase (K A : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (V ⊕ OutsideFace K A) := by
  classical
  exact A.map Sum.inl

private theorem mem_retainedBase_iff {s : Finset (V ⊕ OutsideFace K A)} :
    s ∈ retainedBase K A ↔ s.toLeft ∈ A ∧ s.toRight = ∅ := by
  classical
  change (∃ t ∈ A, t.image (Sum.inl : V → V ⊕ OutsideFace K A) = s) ↔ _
  have himage (t : Finset V) :
      t.image (Sum.inl : V → V ⊕ OutsideFace K A) = t.disjSum ∅ :=
    (Finset.map_eq_image Function.Embedding.inl t).symm.trans (Finset.disjSum_empty t).symm
  simp only [himage, Finset.disjSum_eq_iff]
  exact ⟨fun ⟨t, ht, hleft, hright⟩ => ⟨hleft ▸ ht, hright.symm⟩,
    fun ⟨hleft, hright⟩ => ⟨s.toLeft, hleft, rfl, hright.symm⟩⟩

/-- The retained base is a subcomplex of the relative derived subdivision. -/
theorem retainedBase_le (K A : PreAbstractSimplicialComplex V) :
    retainedBase K A ≤ relativeDerived K A := by
  intro s hs
  obtain ⟨hleft, hright⟩ := mem_retainedBase_iff.mp hs
  refine ⟨((retainedBase K A).isRelLowerSet_faces hs).1, fun _ => hleft, ?_⟩
  simp [hright]

private theorem mem_retainedBase_iff_of_mem {s : Finset (V ⊕ OutsideFace K A)}
    (hs : s ∈ relativeDerived K A) : s ∈ retainedBase K A ↔ s.toRight = ∅ := by
  refine ⟨fun h => (mem_retainedBase_iff.mp h).2, fun hright => ?_⟩
  have hne : s.toLeft.Nonempty := by
    have hne := ((relativeDerived K A).isRelLowerSet_faces hs).1
    rwa [← Finset.toLeft_disjSum_toRight (u := s), hright, Finset.disjSum_empty,
      Finset.map_nonempty] at hne
  exact mem_retainedBase_iff.mpr ⟨hs.2.1 hne, hright⟩

/-- Any face whose vertices belong to the retained base belongs to that base. -/
theorem retainedBase_full (K A : PreAbstractSimplicialComplex V)
    (s : Finset (V ⊕ OutsideFace K A)) (hs : s ∈ relativeDerived K A)
    (hv : ∀ x ∈ s, ({x} : Finset (V ⊕ OutsideFace K A)) ∈ retainedBase K A) :
    s ∈ retainedBase K A := by
  apply (mem_retainedBase_iff_of_mem hs).mpr
  refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hright := (mem_retainedBase_iff.mp (hv (.inr x) (Finset.mem_toRight.mp hx))).2
  exact Finset.eq_empty_iff_forall_notMem.mp hright x
    (Finset.mem_toRight.mpr (Finset.mem_singleton_self _))

/-- Contiguity with both maps preserving and reflecting base membership on vertices. -/
def relativeContiguous (K A : PreAbstractSimplicialComplex V)
    (L B : PreAbstractSimplicialComplex W) (f g : V → W) : Prop :=
  (∀ x, ({x} : Finset V) ∈ K → (({f x} : Finset W) ∈ B ↔ ({x} : Finset V) ∈ A)) ∧
  (∀ x, ({x} : Finset V) ∈ K → (({g x} : Finset W) ∈ B ↔ ({x} : Finset V) ∈ A)) ∧
  ∀ s ∈ K, s.image f ∪ s.image g ∈ L

omit [DecidableEq W] in
private theorem sumMap_vertex (f : V → W) (F : OutsideFace K A →o OutsideFace L B)
    (x : V ⊕ OutsideFace K A) (hx : {x} ∈ relativeDerived K A)
    (hy : {Sum.map f F x} ∈ relativeDerived L B) :
    {Sum.map f F x} ∈ retainedBase L B ↔ {x} ∈ retainedBase K A := by
  rw [mem_retainedBase_iff_of_mem hy, mem_retainedBase_iff_of_mem hx]
  cases x <;> simp [Finset.eq_empty_iff_forall_notMem]

private theorem toLeft_image_sumMap
    (s : Finset (V ⊕ OutsideFace K A)) (f : V → W) (F : OutsideFace K A →o OutsideFace L B) :
    (s.image (Sum.map f F)).toLeft = s.toLeft.image f := by
  ext w
  simp only [Finset.mem_toLeft, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, h⟩
    cases x with
    | inl v => exact ⟨v, hx, Sum.inl.inj h⟩
    | inr a => cases h
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Sum.inl v, hv, rfl⟩

private theorem toRight_image_sumMap
    (s : Finset (V ⊕ OutsideFace K A)) (f : V → W) (F : OutsideFace K A →o OutsideFace L B) :
    (s.image (Sum.map f F)).toRight = s.toRight.image F := by
  ext w
  simp only [Finset.mem_toRight, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, h⟩
    cases x with
    | inl v => cases h
    | inr a => exact ⟨a, hx, Sum.inr.inj h⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Sum.inr a, ha, rfl⟩

private theorem sumMap_contiguous
    (f g : V → W) (F G : OutsideFace K A →o OutsideFace L B)
    (h : mixedContiguous A Subtype.val B Subtype.val f g F G)
    (s : Finset (V ⊕ OutsideFace K A)) (hs : s ∈ relativeDerived K A) :
    s.image (Sum.map f F) ∪ s.image (Sum.map g G) ∈ relativeDerived L B := by
  have hs' : s.Nonempty ∧ mixedSimplex A Subtype.val s.toLeft
      (s.toRight : Set (OutsideFace K A)) := hs
  change (s.image (Sum.map f F) ∪ s.image (Sum.map g G)).Nonempty ∧ _
  refine ⟨Finset.Nonempty.mono Finset.subset_union_left (hs'.1.image _), ?_⟩
  change mixedSimplex B (fun x : OutsideFace L B => x.val)
    (s.image (Sum.map f F) ∪ s.image (Sum.map g G)).toLeft
    ((s.image (Sum.map f F) ∪
      s.image (Sum.map g G)).toRight : Set (OutsideFace L B))
  rw [Finset.toLeft_union, Finset.toRight_union, toLeft_image_sumMap, toLeft_image_sumMap,
    toRight_image_sumMap, toRight_image_sumMap, Finset.coe_union, Finset.coe_image,
    Finset.coe_image]
  exact h s.toLeft s.toRight hs'.2

private theorem singleton_face {X : Type*} {M : PreAbstractSimplicialComplex X}
    {s : Finset X} (hs : s ∈ M) {a : X} (ha : a ∈ s) : ({a} : Finset X) ∈ M :=
  (M.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty _)

/-- Relative derived subdivision carries a contiguous base-preserving and
exterior-preserving pair to simplicial maps in one contiguity class. -/
private theorem induced_relative_maps_contiguous [Finite V] (f g : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) (hg : ∀ s ∈ K, s.image g ∈ L)
    (hfout : ∀ s ∈ K, s ∉ A → s.image f ∉ B)
    (hgout : ∀ s ∈ K, s ∉ A → s.image g ∉ B)
    (hbaseF : ∀ s ∈ A, s.image f ∈ B) (hbaseG : ∀ s ∈ A, s.image g ∈ B)
    (hbaseUnion : ∀ s ∈ A, s.image f ∪ s.image g ∈ B)
    (hunion : ∀ s ∈ K, s.image f ∪ s.image g ∈ L) :
    Relation.ReflTransGen
      (relativeContiguous (relativeDerived K A) (retainedBase K A)
        (relativeDerived L B) (retainedBase L B))
      (Sum.map f (outsideFaceImage f hf hfout)) (Sum.map g (outsideFaceImage g hg hgout)) := by
  let Pair := (V → W) × (OutsideFace K A →o OutsideFace L B)
  let VertexMap := (V ⊕ OutsideFace K A) → (W ⊕ OutsideFace L B)
  let combine (a : Pair) : VertexMap := Sum.map a.1 a.2
  let R (a b : Pair) : Prop :=
    mixedContiguous A Subtype.val B Subtype.val a.1 b.1 a.2 b.2
  let S := relativeContiguous (relativeDerived K A) (retainedBase K A)
    (relativeDerived L B) (retainedBase L B)
  have hstep (a b : Pair) (h : R a b) : S (combine a) (combine b) := by
    have hc := sumMap_contiguous a.1 b.1 a.2 b.2 h
    refine ⟨?_, ?_, hc⟩
    · intro x hx
      exact sumMap_vertex a.1 a.2 x hx (singleton_face (hc {x} hx)
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_singleton_self x))))
    · intro x hx
      exact sumMap_vertex b.1 b.2 x hx (singleton_face (hc {x} hx)
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_singleton_self x))))
  have chain : Relation.ReflTransGen R
      (f, outsideFaceImage f hf hfout) (g, outsideFaceImage g hg hgout) :=
    relative_face_contiguity f g hf hg hfout hgout hbaseF hbaseG hbaseUnion hunion
  exact Relation.ReflTransGen.lift (r := R) (p := S) combine hstep _ _ chain

/-- A contiguous pair on full relative bases lifts through relative derived
subdivision, and each step preserves and reflects membership in the retained bases. -/
theorem relative_subdivision_preserves_contiguity [Finite V]
    (hAK : A ≤ K)
    (hfullA : ∀ s ∈ K, (∀ a ∈ s, ({a} : Finset V) ∈ A) → s ∈ A)
    (hfullB : ∀ t ∈ L, (∀ b ∈ t, ({b} : Finset W) ∈ B) → t ∈ B)
    (f g : V → W)
    (hvertexF : ∀ a, ({a} : Finset V) ∈ K → (({f a} : Finset W) ∈ B ↔ ({a} : Finset V) ∈ A))
    (hvertexG : ∀ a, ({a} : Finset V) ∈ K → (({g a} : Finset W) ∈ B ↔ ({a} : Finset V) ∈ A))
    (hunion : ∀ s ∈ K, s.image f ∪ s.image g ∈ L) :
    ∃ (hf : ∀ s ∈ K, s.image f ∈ L) (hg : ∀ s ∈ K, s.image g ∈ L)
      (hfout : ∀ s ∈ K, s ∉ A → s.image f ∉ B)
      (hgout : ∀ s ∈ K, s ∉ A → s.image g ∉ B),
      Relation.ReflTransGen
        (relativeContiguous (relativeDerived K A) (retainedBase K A)
          (relativeDerived L B) (retainedBase L B))
        (Sum.map f (outsideFaceImage f hf hfout)) (Sum.map g (outsideFaceImage g hg hgout)) := by
  have hf (s) (hs : s ∈ K) : s.image f ∈ L :=
    (L.isRelLowerSet_faces (hunion s hs)).2 Finset.subset_union_left
      (Finset.image_nonempty.mpr (K.isRelLowerSet_faces hs).1)
  have hg (s) (hs : s ∈ K) : s.image g ∈ L :=
    (L.isRelLowerSet_faces (hunion s hs)).2 Finset.subset_union_right
      (Finset.image_nonempty.mpr (K.isRelLowerSet_faces hs).1)
  have outside (u : V → W)
      (hu : ∀ a, ({a} : Finset V) ∈ K → (({u a} : Finset W) ∈ B ↔ ({a} : Finset V) ∈ A))
      (s) (hs : s ∈ K) (hnot : s ∉ A) : s.image u ∉ B := by
    intro himg
    apply hnot (hfullA s hs ?_)
    intro a ha
    exact (hu a (singleton_face hs ha)).mp (singleton_face himg (Finset.mem_image_of_mem _ ha))
  have hbaseUnion (s) (hs : s ∈ A) : s.image f ∪ s.image g ∈ B := by
    apply hfullB _ (hunion s (hAK hs))
    intro b hb
    rcases Finset.mem_union.mp hb with h | h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      exact (hvertexF a (singleton_face (hAK hs) ha)).mpr (singleton_face hs ha)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      exact (hvertexG a (singleton_face (hAK hs) ha)).mpr (singleton_face hs ha)
  have hbaseF (s) (hs : s ∈ A) : s.image f ∈ B :=
    (B.isRelLowerSet_faces (hbaseUnion s hs)).2 Finset.subset_union_left
      (Finset.image_nonempty.mpr (A.isRelLowerSet_faces hs).1)
  have hbaseG (s) (hs : s ∈ A) : s.image g ∈ B :=
    (B.isRelLowerSet_faces (hbaseUnion s hs)).2 Finset.subset_union_right
      (Finset.image_nonempty.mpr (A.isRelLowerSet_faces hs).1)
  exact ⟨hf, hg, outside f hvertexF, outside g hvertexG,
    induced_relative_maps_contiguous f g hf hg (outside f hvertexF) (outside g hvertexG)
      hbaseF hbaseG hbaseUnion hunion⟩

#print axioms relative_subdivision_preserves_contiguity

end Complex

end D5.S3.Topology.RelativeDerivedContiguity
