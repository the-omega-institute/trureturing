/- GID: D5/S3/Topology/GraphSubdivisionIntervals
   generality: G
   mirror-B: D5/B/S3/Topology/GraphSubdivisionIntervals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Every edge of a graph becomes an interval of length two to the subdivision depth. -/

import D5.S3.Topology.PathContiguity
import D5.S3.Geometry.FiniteAlexanderDualCollapse
import Mathlib.Data.Finset.Union
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import OmegaBuild.Commands

/-!
# Edge intervals in ordinary barycentric subdivision

The interval charts are used by the graph gluing argument for
Mosquera-Lois–Tanaka Q6.3. At each step even coordinates are singleton faces
and odd coordinates are consecutive pairs. Following the greatest members of
the nested chains gives the original face that controls subcomplex membership.

The coverage witnesses allow endpoint-relative contiguity to be glued across
adjacent subdivided intervals.
-/

compile_only_with_mathlib


namespace D5.S3.Topology.GraphSubdivisionIntervals

open BarycentricGraphDistance (Face Vertex oneSkeleton)
open BarycentricNeighborhoodIteration (iteratedAmbient iteratedSubcomplex subdivision subdivision_full)
open BarycentricBaseRigidity (faceImage retainedVertex sd subdividedVertex vertexOfFace)
open PathContiguity (intervalComplex)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)

set_option autoImplicit false

noncomputable section

local instance (X : Type*) : DecidableEq X := Classical.decEq X

variable {X : Type} {A B : PreAbstractSimplicialComplex X}

private theorem singleton_of_face {s : Finset X} (hs : s ∈ A) {x : X} (hx : x ∈ s) :
    ({x} : Finset X) ∈ A :=
  (A.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty _)

private def intervalVertex {n : ℕ} (i : ℕ) (hi : i ≤ n) : Vertex (intervalComplex n) := by
  refine ⟨i, Finset.singleton_nonempty i, ?_, ?_⟩
  · intro a ha
    rwa [Finset.mem_singleton.mp ha]
  · intro a ha b hb
    rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact Nat.le_succ _

private theorem interval_bound {n : ℕ} (i : Vertex (intervalComplex n)) : i.val ≤ n :=
  i.property.2.1 _ (Finset.mem_singleton_self _)

-- At index 2k this is {k}. At index 2k+1 this is {k,k+1}.
private def parityFace {n : ℕ} (i : Vertex (intervalComplex (2 * n))) :
    Face (intervalComplex n) := by
  let lo := i.val / 2
  let hi := (i.val + 1) / 2
  have hb := interval_bound i
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; omega
  refine ⟨Finset.Icc lo hi, ⟨lo, Finset.mem_Icc.mpr ⟨le_rfl, hlohi⟩⟩, ?_, ?_⟩
  · intro x hx
    have hx' := (Finset.mem_Icc.mp hx).2
    dsimp [hi] at hx'
    omega
  · intro x hx y hy
    have hx' := (Finset.mem_Icc.mp hx).2
    have hy' := (Finset.mem_Icc.mp hy).1
    dsimp [lo, hi] at hx' hy'
    omega

private theorem parityFace_even {n : ℕ} (i : Vertex (intervalComplex (2 * n))) {k : ℕ}
    (hk : i.val = 2 * k) : (parityFace i).val = {k} := by
  ext x
  change x ∈ Finset.Icc (i.val / 2) ((i.val + 1) / 2) ↔ x ∈ ({k} : Finset ℕ)
  rw [Finset.mem_Icc, Finset.mem_singleton]
  omega

private theorem parityFace_surjective (n : ℕ) :
    Function.Surjective (parityFace (n := n)) := by
  intro f
  have hne : f.val.Nonempty := f.property.1
  let lo := f.val.min' hne
  let hi := f.val.max' hne
  have hl : lo ∈ f.val := Finset.min'_mem _ _
  have hh : hi ∈ f.val := Finset.max'_mem _ _
  have hle : lo ≤ hi := Finset.min'_le _ _ hh
  have hnear : hi ≤ lo + 1 := f.property.2.2 _ hh _ hl
  have hbound : hi ≤ n := f.property.2.1 _ hh
  refine ⟨intervalVertex (lo + hi) (by omega), Subtype.ext ?_⟩
  have hlo : (lo + hi) / 2 = lo := by omega
  have hhi : (lo + hi + 1) / 2 = hi := by omega
  ext x
  change x ∈ Finset.Icc ((lo + hi) / 2) ((lo + hi + 1) / 2) ↔ x ∈ f.val
  rw [Finset.mem_Icc, hlo, hhi]
  constructor
  · intro hx
    have hx' : x = lo ∨ x = hi := by omega
    rcases hx' with rfl | rfl
    · exact hl
    · exact hh
  · intro hx
    exact ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩

private theorem parityFace_le_iff {n : ℕ} (i j : Vertex (intervalComplex (2 * n))) :
    parityFace i ≤ parityFace j ↔
      j.val / 2 ≤ i.val / 2 ∧ (i.val + 1) / 2 ≤ (j.val + 1) / 2 := by
  change Finset.Icc (i.val / 2) ((i.val + 1) / 2) ⊆
    Finset.Icc (j.val / 2) ((j.val + 1) / 2) ↔ _
  constructor
  · intro h
    have hb : i.val / 2 ≤ (i.val + 1) / 2 := by omega
    exact ⟨(Finset.mem_Icc.mp (h (Finset.mem_Icc.mpr ⟨le_rfl, hb⟩))).1,
      (Finset.mem_Icc.mp (h (Finset.mem_Icc.mpr ⟨hb, le_rfl⟩))).2⟩
  · rintro ⟨hlo, hhi⟩ x hx
    obtain ⟨hl, hh⟩ := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨hlo.trans hl, hh.trans hhi⟩

private theorem parityFace_adj_iff {n : ℕ} (i j : Vertex (intervalComplex (2 * n))) :
    (parityFace i < parityFace j ∨ parityFace j < parityFace i) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [lt_iff_le_not_ge, parityFace_le_iff]
  omega

private theorem mem_faceImage_iff {Y : Type} {C : PreAbstractSimplicialComplex Y}
    (f : Vertex A → Vertex C) {s : Finset X} (hs : s ∈ A) (y : Y) :
    y ∈ faceImage f hs ↔ ∃ x : Vertex A, x.val ∈ s ∧ (f x).val = y := by
  unfold faceImage
  constructor
  · intro hy
    obtain ⟨x, _, he⟩ := Finset.mem_image.mp hy
    exact ⟨⟨x.val, singleton_of_face hs x.property⟩, x.property, he⟩
  · rintro ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨x.val, hx⟩, Finset.mem_attach _ _, rfl⟩

theorem faceImage_singleton {Y : Type} {C : PreAbstractSimplicialComplex Y}
    (f : Vertex A → Vertex C) (i : Vertex A) :
    faceImage f i.property = {(f i).val} := by
  ext y
  simp only [mem_faceImage_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hij, rfl⟩
    exact congrArg (fun x => (f x).val) (Subtype.ext hij)
  · intro hy
    exact ⟨i, rfl, hy.symm⟩

private theorem faceImage_subset_iff {Y : Type} {C : PreAbstractSimplicialComplex Y}
    {f : Vertex A → Vertex C} (hf : Function.Injective f)
    {s t : Finset X} (hs : s ∈ A) (ht : t ∈ A) :
    faceImage f hs ⊆ faceImage f ht ↔ s ⊆ t := by
  constructor
  · intro h x hx
    let i : Vertex A := ⟨x, singleton_of_face hs hx⟩
    have hi : (f i).val ∈ faceImage f hs := (mem_faceImage_iff f hs _).2 ⟨i, hx, rfl⟩
    obtain ⟨j, hj, he⟩ := (mem_faceImage_iff f ht _).1 (h hi)
    have hji : j = i := hf (Subtype.ext he)
    simpa only [hji] using hj
  · intro h y hy
    obtain ⟨i, hi, rfl⟩ := (mem_faceImage_iff f hs _).1 hy
    exact (mem_faceImage_iff f ht _).2 ⟨i, h hi, rfl⟩

-- Pull a face back along an interval chart once its indices are known to be consecutive.
private theorem exists_interval_preimage {n : ℕ} (f : Vertex (intervalComplex n) → Vertex A)
    {s : Finset X} (hs : s.Nonempty)
    (hr : ∀ x ∈ s, ∃ i, (f i).val = x)
    (hspan : ∀ i j, (f i).val ∈ s → (f j).val ∈ s → i.val ≤ j.val + 1) :
    ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex n), faceImage f ht = s := by
  let index (x : {x // x ∈ s}) : Vertex (intervalComplex n) :=
    (hr x.val x.property).choose
  have hindex (x : {x // x ∈ s}) : (f (index x)).val = x.val :=
    (hr x.val x.property).choose_spec
  let t := s.attach.image fun x => (index x).val
  have ht : t ∈ intervalComplex n := by
    refine ⟨Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr hs), ?_, ?_⟩
    · intro i hi
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
      exact interval_bound (index x)
    · intro i hi j hj
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hj
      exact hspan (index x) (index y) (by rw [hindex]; exact x.property)
        (by rw [hindex]; exact y.property)
  refine ⟨t, ht, ?_⟩
  ext x
  rw [mem_faceImage_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hi
    rw [← (Subtype.ext hy : index y = i), hindex]
    exact y.property
  · intro hx
    let y : {y // y ∈ s} := ⟨x, hx⟩
    exact ⟨index y, Finset.mem_image.mpr ⟨y, Finset.mem_attach _ _, rfl⟩, hindex y⟩

/-- Subdivision doubles an interval chart and takes even indices to singleton faces. -/
private theorem double_interval_chart {n : ℕ} (hBA : B ≤ A)
    {f : Vertex (intervalComplex n) → Vertex A} (hf : Function.Injective f)
    (hfaces : ∀ s : Finset X, s ∈ B ↔
      ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex n), faceImage f ht = s) :
    ∃ g : Vertex (intervalComplex (2 * n)) → Vertex (sd A),
      Function.Injective g ∧
      (∀ i j, i.val = 2 * j.val → g i = subdividedVertex (f j)) ∧
      (∀ s : Finset (Face A), s ∈ subdivision A B ↔
        ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex (2 * n)), faceImage g ht = s) := by
  have himage (i : Vertex (intervalComplex (2 * n))) : faceImage f (parityFace i).property ∈ B :=
    (hfaces _).2 ⟨_, _, rfl⟩
  let g (i : Vertex (intervalComplex (2 * n))) : Vertex (sd A) :=
    vertexOfFace A ⟨faceImage f (parityFace i).property, hBA (himage i)⟩
  have hle (i j : Vertex (intervalComplex (2 * n))) :
      (g i).val ≤ (g j).val ↔ parityFace i ≤ parityFace j :=
    faceImage_subset_iff hf (parityFace i).property (parityFace j).property
  have hlt (i j : Vertex (intervalComplex (2 * n))) :
      (g i).val < (g j).val ↔ parityFace i < parityFace j := by
    simp only [lt_iff_le_not_ge, hle]
  have hinj : Function.Injective g := by
    intro i j hij
    have h₁ := (parityFace_le_iff i j).1 ((hle i j).1 (by rw [hij]))
    have h₂ := (parityFace_le_iff j i).1 ((hle j i).1 (by rw [hij]))
    exact Subtype.ext (by omega)
  refine ⟨g, hinj, ?_, ?_⟩
  · intro i j hij
    have hpar : parityFace i = (⟨{j.val}, j.property⟩ : Face (intervalComplex n)) :=
      Subtype.ext (parityFace_even i hij)
    apply Subtype.ext
    apply Subtype.ext
    change faceImage f (parityFace i).property = {(f j).val}
    exact (congrArg (fun q : Face (intervalComplex n) => faceImage f q.property) hpar).trans
      (faceImage_singleton f j)
  · intro s
    constructor
    · intro hs
      apply exists_interval_preimage g hs.1
      · intro x hx
        obtain ⟨t, ht, he⟩ := (hfaces _).1 (hs.2.2 x hx)
        obtain ⟨i, hi⟩ := parityFace_surjective n ⟨t, ht⟩
        refine ⟨i, Subtype.ext ?_⟩
        change faceImage f (parityFace i).property = x.val
        exact (congrArg (fun q : Face (intervalComplex n) => faceImage f q.property) hi).trans he
      · intro i j hi hj
        by_cases hij : i = j
        · subst j
          exact Nat.le_succ _
        · have hne : (g i).val ≠ (g j).val := fun h => hij (hinj (Subtype.ext h))
          have hc := hs.2.1 hi hj hne
          have h := (parityFace_adj_iff i j).1 (hc.imp (hlt i j).1 (hlt j i).1)
          omega
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨x, hx⟩ := ht.1
        let i : Vertex (intervalComplex (2 * n)) := ⟨x, singleton_of_face ht hx⟩
        exact ⟨(g i).val, (mem_faceImage_iff g ht _).2 ⟨i, hx, rfl⟩⟩
      · intro x hx y hy hne
        obtain ⟨i, hi, rfl⟩ := (mem_faceImage_iff g ht _).1 hx
        obtain ⟨j, hj, rfl⟩ := (mem_faceImage_iff g ht _).1 hy
        have hne' : i.val ≠ j.val := fun h => hne (congrArg (fun k => (g k).val) (Subtype.ext h))
        have h₁ := ht.2.2 i.val hi j.val hj
        have h₂ := ht.2.2 j.val hj i.val hi
        have h := (parityFace_adj_iff i j).2 (by omega)
        exact h.imp (hlt i j).2 (hlt j i).2
      · intro x hx
        obtain ⟨i, _, rfl⟩ := (mem_faceImage_iff g ht _).1 hx
        exact himage i

private theorem simplex_le {e : Finset X} (he : e ∈ A) :
    simplex e ≤ A := by
  intro s hs
  exact (A.isRelLowerSet_faces he).2 hs.2 hs.1

private theorem iterated_le_ambient (hBA : B ≤ A) (m : ℕ) :
    iteratedSubcomplex A B m ≤ (iteratedAmbient A m).2 := by
  cases m with
  | zero => exact hBA
  | succ m => exact (subdivision_full _ _).1

private theorem edge_chart (x y : Vertex A) (hne : x ≠ y)
    (hxy : ({x.val, y.val} : Finset X) ∈ A) (m : ℕ) :
    ∃ f : Vertex (intervalComplex (2 ^ m)) → Vertex (iteratedAmbient A m).2,
      Function.Injective f ∧
      (∀ i, (i.val = 0 → f i = retainedVertex m x) ∧
        (i.val = 2 ^ m → f i = retainedVertex m y)) ∧
      (∀ s : Finset (iteratedAmbient A m).1,
        s ∈ iteratedSubcomplex A (simplex {x.val, y.val}) m ↔
          ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex (2 ^ m)), faceImage f ht = s) := by
  induction m with
  | zero =>
    change ∃ f : Vertex (intervalComplex 1) → Vertex A, Function.Injective f ∧
      (∀ i, (i.val = 0 → f i = x) ∧ (i.val = 1 → f i = y)) ∧
      (∀ s : Finset X, s ∈ simplex {x.val, y.val} ↔
        ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex 1), faceImage f ht = s)
    let f (i : Vertex (intervalComplex 1)) : Vertex A := if i.val = 0 then x else y
    have hleft (i : Vertex (intervalComplex 1)) (hi : i.val = 0) : f i = x := if_pos hi
    have hright (i : Vertex (intervalComplex 1)) (hi : i.val = 1) : f i = y :=
      if_neg (by omega)
    refine ⟨f, ?_, fun i => ⟨hleft i, hright i⟩, ?_⟩
    · intro i j hij
      have hi := interval_bound i
      have hj := interval_bound j
      apply Subtype.ext
      by_contra h
      have hcases : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) := by omega
      rcases hcases with ⟨hi₀, hj₁⟩ | ⟨hi₁, hj₀⟩
      · exact hne ((hleft i hi₀).symm.trans (hij.trans (hright j hj₁)))
      · exact hne ((hleft j hj₀).symm.trans (hij.symm.trans (hright i hi₁)))
    · intro s
      constructor
      · intro hs
        apply exists_interval_preimage f hs.1
        · intro z hz
          rcases Finset.mem_insert.mp (hs.2 hz) with rfl | hz'
          · exact ⟨intervalVertex 0 (by decide), congrArg Subtype.val (hleft _ rfl)⟩
          · rw [Finset.mem_singleton.mp hz']
            exact ⟨intervalVertex 1 (by decide), congrArg Subtype.val (hright _ rfl)⟩
        · intro i j _ _
          have hi := interval_bound i
          omega
      · rintro ⟨t, ht, rfl⟩
        refine ⟨Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr ht.1), ?_⟩
        intro z hz
        obtain ⟨i, _, rfl⟩ := (mem_faceImage_iff f ht _).1 hz
        by_cases hi : i.val = 0
        · rw [hleft i hi]
          exact Finset.mem_insert_self _ _
        · have hb := interval_bound i
          rw [hright i (by omega)]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  | succ m ih =>
    obtain ⟨f, hf, hend, hfaces⟩ := ih
    obtain ⟨g, hg, heven, hnew⟩ :=
      double_interval_chart (iterated_le_ambient (simplex_le hxy) m) hf hfaces
    rw [pow_succ']
    refine ⟨g, hg, ?_, hnew⟩
    intro i
    constructor
    · intro hi
      let j := intervalVertex (n := 2 ^ m) 0 (Nat.zero_le _)
      exact (heven i j (by simpa [j, intervalVertex] using hi)).trans
        (congrArg subdividedVertex ((hend j).1 rfl))
    · intro hi
      let j := intervalVertex (n := 2 ^ m) (2 ^ m) le_rfl
      exact (heven i j hi).trans (congrArg subdividedVertex ((hend j).2 rfl))

-- The union of a nonempty chain of faces is its greatest member.
private theorem chain_union_eq {s : Finset (Face A)} (hs : s ∈ sd A) :
    ∃ t ∈ s, s.biUnion Subtype.val = t.val := by
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image s (fun q => q.val.card) hs.1
  refine ⟨t, ht, le_antisymm ?_ (Finset.subset_biUnion_of_mem Subtype.val ht)⟩
  apply Finset.biUnion_subset.mpr
  intro q hq
  by_cases he : q = t
  · exact he.le
  · rcases hs.2.1 hq ht he with hqt | htq
    · exact hqt.le
    · exact ((not_lt_of_ge (hmax q hq)) (Finset.card_lt_card htq)).elim

/-- The original vertices supporting a simplex of the subdivided complex. -/
def originalSupport (A : PreAbstractSimplicialComplex X) :
    (m : ℕ) → Finset (iteratedAmbient A m).1 → Finset X
  | 0, s => s
  | m + 1, s => originalSupport A m (s.biUnion Subtype.val)

/-- A face belongs to a subdivided subcomplex precisely when its original
support belongs to that subcomplex. -/
theorem mem_iteratedSubcomplex_iff (m : ℕ) {s : Finset (iteratedAmbient A m).1}
    (hs : s ∈ (iteratedAmbient A m).2) :
    s ∈ iteratedSubcomplex A B m ↔ originalSupport A m s ∈ B := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Finset (Face (iteratedAmbient A m).2) at s
    change s ∈ sd (iteratedAmbient A m).2 at hs
    obtain ⟨t, ht, hu⟩ := chain_union_eq hs
    change s ∈ subdivision (iteratedAmbient A m).2 (iteratedSubcomplex A B m) ↔
      originalSupport A m (s.biUnion Subtype.val) ∈ B
    have hsupport : originalSupport A m (s.biUnion Subtype.val) ∈ B ↔
        t.val ∈ iteratedSubcomplex A B m := by
      rw [hu, ← ih t.property]
    refine Iff.trans ?_ hsupport.symm
    constructor
    · intro h
      exact h.2.2 t ht
    · intro h
      refine ⟨hs.1, hs.2.1, fun q hq => ?_⟩
      have hsub : q.val ⊆ t.val := by
        rw [← hu]
        exact Finset.subset_biUnion_of_mem Subtype.val hq
      exact ((iteratedSubcomplex A B m).isRelLowerSet_faces h).2 hsub
        ((iteratedAmbient A m).2.isRelLowerSet_faces q.property).1

theorem originalSupport_mem (m : ℕ) {s : Finset (iteratedAmbient A m).1}
    (hs : s ∈ (iteratedAmbient A m).2) : originalSupport A m s ∈ A := by
  apply (mem_iteratedSubcomplex_iff (B := A) m hs).1
  have h : ∀ k, iteratedSubcomplex A A k = (iteratedAmbient A k).2 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change subdivision _ (iteratedSubcomplex A A k) = sd (iteratedAmbient A k).2
      rw [ih]
  rwa [h m]

theorem originalSupport_retained (m : ℕ) (x : Vertex A) :
    originalSupport A m {(retainedVertex m x).val} = {x.val} := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change originalSupport A m
      (({(subdividedVertex (retainedVertex m x)).val} : Finset _).biUnion Subtype.val) = {x.val}
    rw [Finset.singleton_biUnion]
    exact ih

private theorem iterated_point_face (m : ℕ) (x : Vertex A)
    {s : Finset (iteratedAmbient A m).1}
    (hs : s ∈ iteratedSubcomplex A (simplex {x.val}) m) :
    s = {(retainedVertex m x).val} := by
  induction m with
  | zero =>
    exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hs.1, fun _ hz => Finset.mem_singleton.mp (hs.2 hz)⟩
  | succ m ih =>
    change s ∈ subdivision _ _ at hs
    apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    exact ⟨hs.1, fun q hq => Subtype.ext (ih (hs.2.2 q hq))⟩

/-- Every original edge has a literal interval chart after ordinary subdivision.
The face-image equivalence identifies its entire subdivided subcomplex.
An interior index cannot agree with any index of a different chart, and every
ambient face is an edge-chart image or a retained isolated vertex. -/
theorem graph_subdivision_intervals_oriented (A : PreAbstractSimplicialComplex X)
    (hdim : ∀ s ∈ A, (s : Finset X).card ≤ 2) (m : ℕ)
    (left right : {e : Face A // e.val.val.card = 2} → Vertex A)
    (horient : ∀ e, e.val.val = {(left e).val, (right e).val} ∧ left e ≠ right e) :
    let E := {e : Face A // e.val.val.card = 2}
    let P := (iteratedAmbient A m).2
    ∃ chart : E → Vertex (intervalComplex (2 ^ m)) → Vertex P,
      (∀ e, Function.Injective (chart e)) ∧
      (∀ e i, (i.val = 0 → chart e i = retainedVertex m (left e)) ∧
        (i.val = 2 ^ m → chart e i = retainedVertex m (right e))) ∧
      (∀ (e : E) (s : Finset (iteratedAmbient A m).1),
        s ∈ iteratedSubcomplex A (simplex e.val.val) m ↔
          ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex (2 ^ m)), faceImage (chart e) ht = s) ∧
      (∀ (e d : E) (i j : Vertex (intervalComplex (2 ^ m))),
        i.val ≠ 0 → i.val ≠ 2 ^ m → chart e i = chart d j → e = d) ∧
      (∀ (s : Finset (iteratedAmbient A m).1), s ∈ P →
        (∃ x : Vertex A, (∀ y : Vertex A, ¬ (oneSkeleton A).Adj x y) ∧
          s = {(retainedVertex m x).val} ∧
          ¬ ∃ (e : E) (i : Vertex (intervalComplex (2 ^ m))),
            i.val ≠ 0 ∧ i.val ≠ 2 ^ m ∧ chart e i = retainedVertex m x) ∨
        ∃ (e : E) (t : Finset ℕ) (ht : t ∈ intervalComplex (2 ^ m)),
          faceImage (chart e) ht = s ∧
          ∀ x : Vertex P, x.val ∈ s →
            ∃ i : Vertex (intervalComplex (2 ^ m)), i.val ∈ t ∧ chart e i = x) := by
  let E := {e : Face A // e.val.val.card = 2}
  have charts (e : E) := edge_chart (left e) (right e) (horient e).2
    (show ({(left e).val, (right e).val} : Finset X) ∈ A by
      rw [← (horient e).1]
      exact e.val.property) m
  choose chart hinj hend hfaces using charts
  have hfaces' (e : E) (s : Finset (iteratedAmbient A m).1) :
      s ∈ iteratedSubcomplex A (simplex e.val.val) m ↔
        ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex (2 ^ m)), faceImage (chart e) ht = s := by
    rw [(horient e).1]
    exact hfaces e s
  have covered (e : E) {s : Finset (iteratedAmbient A m).1}
      (hs : s ∈ iteratedSubcomplex A (simplex e.val.val) m) :
      ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex (2 ^ m)), faceImage (chart e) ht = s ∧
        ∀ x : Vertex (iteratedAmbient A m).2, x.val ∈ s →
          ∃ i : Vertex (intervalComplex (2 ^ m)), i.val ∈ t ∧ chart e i = x := by
    obtain ⟨t, ht, heq⟩ := (hfaces' e s).1 hs
    refine ⟨t, ht, heq, ?_⟩
    intro x hx
    rw [← heq] at hx
    obtain ⟨i, hi, hx'⟩ := (mem_faceImage_iff (chart e) ht x.val).1 hx
    exact ⟨i, hi, Subtype.ext hx'⟩
  have chart_mem (e : E) (i : Vertex (intervalComplex (2 ^ m))) :
      ({(chart e i).val} : Finset (iteratedAmbient A m).1) ∈
        iteratedSubcomplex A (simplex e.val.val) m :=
    (hfaces' e _).2 ⟨_, i.property, faceImage_singleton (chart e) i⟩
  have on_edge (e : E) (i : Vertex (intervalComplex (2 ^ m))) :
      originalSupport A m {(chart e i).val} ⊆ e.val.val :=
    ((mem_iteratedSubcomplex_iff m (chart e i).property).1 (chart_mem e i)).2
  have retained_at_end (e : E) (i : Vertex (intervalComplex (2 ^ m))) (x : Vertex A)
      (he : chart e i = retainedVertex m x) : i.val = 0 ∨ i.val = 2 ^ m := by
    have hx : x.val ∈ e.val.val := by
      have h := on_edge e i
      rw [he, originalSupport_retained] at h
      exact Finset.singleton_subset_iff.mp h
    rw [(horient e).1, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · have hx' : x = left e := Subtype.ext hx
      let j := intervalVertex (n := 2 ^ m) 0 (Nat.zero_le _)
      have he' : chart e i = chart e j := by rw [he, hx', (hend e j).1 rfl]
      exact Or.inl (congrArg Subtype.val (hinj e he'))
    · have hx' : x = right e := Subtype.ext hx
      let j := intervalVertex (n := 2 ^ m) (2 ^ m) le_rfl
      have he' : chart e i = chart e j := by rw [he, hx', (hend e j).2 rfl]
      exact Or.inr (congrArg Subtype.val (hinj e he'))
  refine ⟨chart, hinj, hend, hfaces', ?_, ?_⟩
  · intro e d i j hi₀ hiN h
    let s := originalSupport A m {(chart e i).val}
    have hs : s ∈ A := originalSupport_mem m (chart e i).property
    have hsube : s ⊆ e.val.val := on_edge e i
    have hsubd : s ⊆ d.val.val := by simpa only [s, h] using on_edge d j
    by_cases htwo : s.card = 2
    · have he := Finset.eq_of_subset_of_card_le hsube (show e.val.val.card ≤ s.card from e.property.trans htwo.symm |>.le)
      have hd := Finset.eq_of_subset_of_card_le hsubd (show d.val.val.card ≤ s.card from d.property.trans htwo.symm |>.le)
      exact Subtype.ext (Subtype.ext (he.symm.trans hd))
    · have hpos := Finset.card_pos.mpr (A.isRelLowerSet_faces hs).1
      have hb := hdim s hs
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
      let x : Vertex A := ⟨v, hv ▸ hs⟩
      have hp : ({(chart e i).val} : Finset _) ∈ iteratedSubcomplex A (simplex {v}) m :=
        (mem_iteratedSubcomplex_iff m (chart e i).property).2
          ⟨(A.isRelLowerSet_faces hs).1, by
            change s ⊆ {v}
            exact hv.symm ▸ Finset.Subset.refl _⟩
      have he : chart e i = retainedVertex m x := Subtype.ext
        (Finset.singleton_injective (iterated_point_face m x hp))
      exact (retained_at_end e i x he).elim (fun h₀ => (hi₀ h₀).elim) (fun hN => (hiN hN).elim)
  · intro s hs
    let t := originalSupport A m s
    have ht : t ∈ A := originalSupport_mem m hs
    have hne := (A.isRelLowerSet_faces ht).1
    by_cases htwo : t.card = 2
    · let e : E := ⟨⟨t, ht⟩, htwo⟩
      have he := (mem_iteratedSubcomplex_iff (B := simplex e.val.val) m hs).2
        ⟨hne, Finset.Subset.refl _⟩
      exact Or.inr ⟨e, covered e he⟩
    · have hpos := Finset.card_pos.mpr hne
      have hb := hdim t ht
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
      let x : Vertex A := ⟨v, hv ▸ ht⟩
      by_cases hincident : ∃ e : E, v ∈ e.val.val
      · obtain ⟨e, he⟩ := hincident
        have hsub : t ⊆ e.val.val := hv.symm ▸ Finset.singleton_subset_iff.mpr he
        have hs' := (mem_iteratedSubcomplex_iff (B := simplex e.val.val) m hs).2
          ⟨hne, hsub⟩
        exact Or.inr ⟨e, covered e hs'⟩
      · have hs' := (mem_iteratedSubcomplex_iff (B := simplex {v}) m hs).2
          ⟨hne, by
            change t ⊆ {v}
            exact hv.symm ▸ Finset.Subset.refl _⟩
        refine Or.inl ⟨x, ?_, iterated_point_face m x hs', ?_⟩
        · intro y hxy
          have hdistinct : x.val ≠ y.val := fun h => hxy.1 (Subtype.ext h)
          let e : E := ⟨⟨{x.val, y.val}, hxy.2⟩, Finset.card_pair hdistinct⟩
          exact hincident ⟨e, Finset.mem_insert_self _ _⟩
        · rintro ⟨e, i, hi₀, hiN, hi⟩
          exact (retained_at_end e i x hi).elim hi₀ hiN

/-- Choose one orientation for every original edge and construct the interval charts. -/
theorem graph_subdivision_intervals (A : PreAbstractSimplicialComplex X)
    (hdim : ∀ s ∈ A, (s : Finset X).card ≤ 2) (m : ℕ) :
    let E := {e : Face A // e.val.val.card = 2}
    let P := (iteratedAmbient A m).2
    ∃ (left right : E → Vertex A) (chart : E → Vertex (intervalComplex (2 ^ m)) → Vertex P),
      (∀ e, e.val.val = { (left e).val, (right e).val } ∧ left e ≠ right e) ∧
      (∀ e, Function.Injective (chart e)) ∧
      (∀ e i, (i.val = 0 → chart e i = retainedVertex m (left e)) ∧
        (i.val = 2 ^ m → chart e i = retainedVertex m (right e))) ∧
      (∀ (e : E) (s : Finset (iteratedAmbient A m).1),
        s ∈ iteratedSubcomplex A (simplex e.val.val) m ↔
          ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex (2 ^ m)), faceImage (chart e) ht = s) ∧
      (∀ (e d : E) (i j : Vertex (intervalComplex (2 ^ m))),
        i.val ≠ 0 → i.val ≠ 2 ^ m → chart e i = chart d j → e = d) ∧
      (∀ (s : Finset (iteratedAmbient A m).1), s ∈ P →
        (∃ x : Vertex A, (∀ y : Vertex A, ¬ (oneSkeleton A).Adj x y) ∧
          s = {(retainedVertex m x).val} ∧
          ¬ ∃ (e : E) (i : Vertex (intervalComplex (2 ^ m))),
            i.val ≠ 0 ∧ i.val ≠ 2 ^ m ∧ chart e i = retainedVertex m x) ∨
        ∃ (e : E) (t : Finset ℕ) (ht : t ∈ intervalComplex (2 ^ m)),
          faceImage (chart e) ht = s ∧
          ∀ x : Vertex P, x.val ∈ s →
            ∃ i : Vertex (intervalComplex (2 ^ m)), i.val ∈ t ∧ chart e i = x) := by
  let E := {e : Face A // e.val.val.card = 2}
  have orient (e : E) : ∃ x y : Vertex A, e.val.val = {x.val, y.val} ∧ x ≠ y := by
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp e.property
    have ha : a ∈ e.val.val := by rw [he]; exact Finset.mem_insert_self _ _
    have hb : b ∈ e.val.val := by
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact ⟨⟨a, singleton_of_face e.val.property ha⟩, ⟨b, singleton_of_face e.val.property hb⟩,
      he, fun h => hab (congrArg Subtype.val h)⟩
  choose left right horient using orient
  obtain ⟨chart, hc⟩ := graph_subdivision_intervals_oriented A hdim m left right horient
  exact ⟨left, right, chart, horient, hc⟩

end

end D5.S3.Topology.GraphSubdivisionIntervals
