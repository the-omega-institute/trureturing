/- GID: D5/S3/Topology/CoveringDimension/FiniteFrontier
   generality: G
   mirror-B: D5/B/S3/Topology/CoveringDimension/FiniteFrontier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite frontiers and finite fibers give bounds on covering dimension. -/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Set.Card

/-!
# Covering dimension bounds

Finite frontiers give refinements of multiplicity at most two. Closed maps with
finite fibers preserve the upper bound under pullback.
-/

open Set

namespace D5.S3.Topology.CoveringDimension

/-- The finite-cover definition of Lebesgue covering dimension, as in
`FormalConjecturesForMathlib.Topology.LebesgueCoveringDimension`. -/
def AtMost (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ U : Set (Set X), U.Finite → (∀ u ∈ U, IsOpen u) → ⋃₀ U = univ →
    ∃ V : Set (Set X), V.Finite ∧ (∀ v ∈ V, IsOpen v) ∧ ⋃₀ V = univ ∧
      (∀ v ∈ V, ∃ u ∈ U, v ⊆ u) ∧ ∀ x : X, {v ∈ V | x ∈ v}.encard ≤ (n + 1 : ℕ)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem exists_cover_member {U : Set (Set X)} (h : ⋃₀ U = univ) (x : X) :
    ∃ u ∈ U, x ∈ u :=
  mem_sUnion.mp (h.symm ▸ mem_univ x)

/-- A finite family of open sets with finite frontiers partitions the complement
of those frontiers into open cells. Disjoint neighborhoods of the finitely many
remaining points provide the second family in a refinement of multiplicity two. -/
theorem atMost_one_of_finiteFrontier [CompactSpace X] [T2Space X]
    (hBasis : ∀ (x : X) (u : Set X), IsOpen u → x ∈ u →
      ∃ v : Set X, IsOpen v ∧ x ∈ v ∧ v ⊆ u ∧ (frontier v).Finite) :
    AtMost X 1 := by
  classical
  intro U _ hOpen hCover
  choose u hu hxu using exists_cover_member hCover
  choose v hvOpen hxv hvu hvFin using fun x => hBasis x (u x) (hOpen _ (hu x)) (hxu x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover v hvOpen
    (fun x _ => mem_iUnion.mpr ⟨x, hxv x⟩)
  have hChoice (x : X) : ∃ i : s, x ∈ v i := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (mem_univ x))
    obtain ⟨his, hix⟩ := mem_iUnion.mp hi
    exact ⟨⟨i, his⟩, hix⟩
  let boundary : Set X := ⋃ i : s, frontier (v i)
  have hBoundary : boundary.Finite := finite_iUnion fun i => hvFin i
  let cell (t : s → Bool) : Set X :=
    ⋂ i : s, if t i = true then v i else (closure (v i))ᶜ
  let cells : Set (Set X) := cell '' {t | ∃ i, t i = true}
  obtain ⟨o, ho, hSep⟩ := hBoundary.t2_separation
  let nearby (x : X) : Set X := o x ∩ u x
  let around : Set (Set X) := nearby '' boundary
  have hCellOpen (t : s → Bool) : IsOpen (cell t) := by
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact hvOpen i
    · exact isClosed_closure.isOpen_compl
  have hCellCode {t : s → Bool} {x : X} (hx : x ∈ cell t) (i : s) :
      t i = true ↔ x ∈ v i := by
    have hx' := mem_iInter.mp hx i
    constructor
    · intro hi
      simpa [hi] using hx'
    · intro hi
      by_contra hne
      have hn : x ∉ closure (v i) := by simpa [hne] using hx'
      exact hn (subset_closure hi)
  refine ⟨cells ∪ around, (toFinite _).image _ |>.union (hBoundary.image _), ?_, ?_, ?_, ?_⟩
  · rintro W (⟨t, _, rfl⟩ | ⟨x, _, rfl⟩)
    · exact hCellOpen t
    · exact (ho x).2.inter (hOpen _ (hu x))
  · apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ boundary
    · exact mem_sUnion.mpr ⟨nearby x, Or.inr ⟨x, hx, rfl⟩, (ho x).1, hxu x⟩
    · let t (i : s) : Bool := if x ∈ v i then true else false
      have ht : ∃ i, t i = true := by
        obtain ⟨i, hi⟩ := hChoice x
        exact ⟨i, by simp [t, hi]⟩
      refine mem_sUnion.mpr ⟨cell t, Or.inl ⟨t, ht, rfl⟩, mem_iInter.mpr fun i => ?_⟩
      by_cases hi : x ∈ v i
      · simpa [t, hi] using hi
      · have hOut : x ∉ closure (v i) := by
          intro hCl
          apply hx
          refine mem_iUnion.mpr ⟨i, ?_⟩
          rw [(hvOpen i).frontier_eq]
          exact ⟨hCl, hi⟩
        simpa [t, hi] using hOut
  · rintro W (⟨t, ⟨i, hi⟩, rfl⟩ | ⟨x, _, rfl⟩)
    · exact ⟨u i, hu i, fun _ hw => hvu i ((hCellCode hw i).mp hi)⟩
    · exact ⟨u x, hu x, inter_subset_right⟩
  · intro x
    have hOneCell : {W ∈ cells | x ∈ W}.encard ≤ 1 := encard_le_one_iff.mpr (by
      rintro _ _ ⟨⟨t, _, rfl⟩, ht⟩ ⟨⟨t', _, rfl⟩, ht'⟩
      congr 1
      funext i
      exact Bool.eq_iff_iff.mpr ((hCellCode ht i).trans (hCellCode ht' i).symm))
    have hOneAround : {W ∈ around | x ∈ W}.encard ≤ 1 := encard_le_one_iff.mpr (by
      rintro _ _ ⟨⟨y, hy, rfl⟩, hxy⟩ ⟨⟨z, hz, rfl⟩, hxz⟩
      by_cases he : y = z
      · rw [he]
      · exact False.elim (disjoint_left.mp (hSep hy hz he) hxy.1 hxz.1))
    have hUnion : {W ∈ cells ∪ around | x ∈ W} =
        {W ∈ cells | x ∈ W} ∪ {W ∈ around | x ∈ W} := by
      ext W
      simp only [mem_setOf_eq, mem_union]
      tauto
    rw [hUnion]
    calc
      _ ≤ _ + _ := encard_union_le _ _
      _ ≤ (1 : ℕ∞) + 1 := add_le_add hOneCell hOneAround
      _ = _ := by decide

/-- A nontrivial preconnected space with closed points cannot have covering
dimension zero. -/
theorem not_atMost_zero [T1Space X] [PreconnectedSpace X] [Nontrivial X] :
    ¬ AtMost X 0 := by
  classical
  intro hdim
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  let U : Set (Set X) := {{x}ᶜ, {y}ᶜ}
  have hOpen : ∀ u ∈ U, IsOpen u := by
    intro u hu
    rcases (show u = {x}ᶜ ∨ u = {y}ᶜ by simpa [U] using hu) with rfl | rfl
    all_goals exact isClosed_singleton.isOpen_compl
  have hCover : ⋃₀ U = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z = x
    · exact mem_sUnion.mpr ⟨{y}ᶜ, by simp [U], by simpa [hz] using hxy⟩
    · exact mem_sUnion.mpr ⟨{x}ᶜ, by simp [U], by simpa using hz⟩
  obtain ⟨V, _, hvOpen, hvCover, hvRef, hvCard⟩ :=
    hdim U (Finite.insert _ (finite_singleton _)) hOpen hCover
  obtain ⟨v, hv, hx⟩ := exists_cover_member hvCover x
  have hComp : vᶜ = ⋃₀ {w ∈ V | w ≠ v} := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hzw⟩ := exists_cover_member hvCover z
      exact mem_sUnion.mpr ⟨w, ⟨hw, fun he => hz (he ▸ hzw)⟩, hzw⟩
    · intro hz hzv
      obtain ⟨w, hw, hzw⟩ := mem_sUnion.mp hz
      have hOne : {w ∈ V | z ∈ w}.encard ≤ 1 := by simpa using hvCard z
      exact hw.2 (encard_le_one_iff.mp hOne _ _ ⟨hw.1, hzw⟩ ⟨hv, hzv⟩)
  have hvClopen : IsClopen v :=
    ⟨isOpen_compl_iff.mp (hComp ▸ isOpen_sUnion (fun _ hw => hvOpen _ hw.1)), hvOpen _ hv⟩
  have hvAll := hvClopen.eq_univ ⟨x, hx⟩
  obtain ⟨u, hu, hSub⟩ := hvRef v hv
  rcases (show u = {x}ᶜ ∨ u = {y}ᶜ by simpa [U] using hu) with rfl | rfl
  · simpa using hSub hx
  · have hy : y ∈ v := hvAll.symm ▸ mem_univ y
    simpa using hSub hy

/-- A continuous closed map with finite fibers pulls finite open refinements back
without increasing multiplicity. The pullback of each base set is split into
disjoint pieces subordinate to the original cover. -/
theorem atMost_of_closedMap_finiteFibers [T2Space X] [CompactSpace Y]
    {f : X → Y} (hf : Continuous f) (hClosed : IsClosedMap f)
    (hFinite : ∀ y : Y, (f ⁻¹' {y}).Finite) {n : ℕ} (hDim : AtMost Y n) :
    AtMost X n := by
  classical
  intro U _ hOpen hCover
  choose u hu hxu using exists_cover_member hCover
  let fiber (y : Y) : Set X := f ⁻¹' {y}
  choose o ho hSep using fun y => (hFinite y).t2_separation
  let piece (y : Y) (x : X) : Set X := o y x ∩ u x
  let covered (y : Y) : Set X := ⋃ x : fiber y, piece y x
  let near (y : Y) : Set Y := (f '' (covered y)ᶜ)ᶜ
  have hCoveredOpen (y : Y) : IsOpen (covered y) :=
    isOpen_iUnion fun x => (ho y x).2.inter (hOpen _ (hu x))
  have hNearOpen (y : Y) : IsOpen (near y) :=
    (hClosed _ (hCoveredOpen y).isClosed_compl).isOpen_compl
  have hNearMem (y : Y) : y ∈ near y := by
    rintro ⟨x, hx, hfx⟩
    exact hx (mem_iUnion.mpr ⟨⟨x, hfx⟩, (ho y x).1, hxu x⟩)
  have hNearSub (y : Y) : f ⁻¹' near y ⊆ covered y := by
    intro x hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover near hNearOpen
    (fun y _ => mem_iUnion.mpr ⟨y, hNearMem y⟩)
  let base : Set (Set Y) := near '' (s : Set Y)
  have hBaseCover : ⋃₀ base = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (mem_univ y))
    obtain ⟨his, hy⟩ := mem_iUnion.mp hi
    exact mem_sUnion.mpr ⟨near i, ⟨i, his, rfl⟩, hy⟩
  obtain ⟨V, hVF, hVO, hVC, hVR, hVM⟩ :=
    hDim base (s.finite_toSet.image _) (by rintro _ ⟨i, _, rfl⟩; exact hNearOpen i) hBaseCover
  have hSelect (v : V) : ∃ y, v.val ⊆ near y := by
    obtain ⟨b, ⟨y, _, rfl⟩, hSub⟩ := hVR v.val v.property
    exact ⟨y, hSub⟩
  choose origin hOrigin using hSelect
  let Index := Σ v : V, fiber (origin v)
  letI : Fintype V := hVF.fintype
  letI (v : V) : Fintype (fiber (origin v)) := (hFinite (origin v)).fintype
  letI : Finite Index := inferInstanceAs (Finite (Σ v : V, fiber (origin v)))
  let refineSet (i : Index) : Set X :=
    f ⁻¹' i.1.val ∩ piece (origin i.1) i.2
  refine ⟨range refineSet, finite_range _, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact ((hVO _ i.1.property).preimage hf).inter
      ((ho _ i.2).2.inter (hOpen _ (hu i.2)))
  · apply eq_univ_of_forall
    intro x
    obtain ⟨v, hv, hx⟩ := exists_cover_member hVC (f x)
    let j : V := ⟨v, hv⟩
    have hx' := hNearSub (origin j) (hOrigin j hx)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
    exact mem_sUnion.mpr ⟨refineSet ⟨j, i⟩, mem_range_self _, hx, hi⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨u i.2, hu i.2, fun _ h => h.2.2⟩
  · intro x
    let occurring : Set Index := {i | x ∈ refineSet i}
    let project (i : Index) : Set Y := i.1.val
    have hProject : InjOn project occurring := by
      rintro ⟨v, i⟩ hi ⟨w, j⟩ hj he
      have hvw : v = w := Subtype.ext he
      subst w
      congr 1
      apply Subtype.ext
      by_contra hn
      exact disjoint_left.mp (hSep _ i.property j.property hn) hi.2.1 hj.2.1
    have hImage : project '' occurring ⊆ {v ∈ V | f x ∈ v} := by
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨i.1.property, hi.1⟩
    have hRefImage : {w ∈ range refineSet | x ∈ w} ⊆ refineSet '' occurring := by
      rintro _ ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
    exact (encard_mono hRefImage).trans ((encard_image_le _ _).trans
      (hProject.encard_image.ge.trans ((encard_mono hImage).trans (hVM (f x)))))

end D5.S3.Topology.CoveringDimension
