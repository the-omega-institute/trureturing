/- GID: D5/S3/Topology/Separation/AlexandroffDuplicate
   generality: G
   mirror-B: D5/B/S3/Topology/Separation/AlexandroffDuplicate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Hausdorff duplicates have an exact dense upper clopen locus. -/

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Perfect
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.InductiveDimension.Classes

/-! The two-layer topology uses the actual punctured upper copy of each base
neighborhood. No product topology or discrete replacement of the bottom is used.
The compactness proof constructs a finite subcover with a finite upper remainder.
The connected bottom copy then excludes every bottom point from the clopen locus.
-/

set_option autoImplicit false

open Set Function Topology

namespace D5.S3.Topology.Separation.AlexandroffDuplicate

universe u

/-- The actual two-copy carrier, with its duplicate topology defined below. -/
structure Duplicate (K : Type u) where
  base : K
  upper : Bool

variable {K : Type u} [TopologicalSpace K]

def lower (x : K) : Duplicate K := ⟨x, false⟩
def upper (x : K) : Duplicate K := ⟨x, true⟩

instance : TopologicalSpace (Duplicate K) where
  IsOpen s := ∀ x, lower x ∈ s → ∃ V : Set K, IsOpen V ∧ x ∈ V ∧
    ∀ y ∈ V, lower y ∈ s ∧ (y ≠ x → upper y ∈ s)
  isOpen_univ := fun x _ => ⟨univ, isOpen_univ, trivial, fun _ _ => ⟨trivial, fun _ => trivial⟩⟩
  isOpen_inter := by
    intro s t hs ht x hx
    obtain ⟨V, hV, hxV, hVs⟩ := hs x hx.1
    obtain ⟨W, hW, hxW, hWt⟩ := ht x hx.2
    exact ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW⟩, fun y hy =>
      ⟨⟨(hVs y hy.1).1, (hWt y hy.2).1⟩,
        fun h => ⟨(hVs y hy.1).2 h, (hWt y hy.2).2 h⟩⟩⟩
  isOpen_sUnion := by
    intro S hS x hx
    obtain ⟨s, hsS, hxs⟩ := hx
    obtain ⟨V, hV, hxV, hVs⟩ := hS s hsS x hxs
    exact ⟨V, hV, hxV, fun y hy =>
      ⟨⟨s, hsS, (hVs y hy).1⟩, fun h => ⟨s, hsS, (hVs y hy).2 h⟩⟩⟩

/-- A point has arbitrarily small actual ambient clopen neighborhoods. -/
def HasClopenBasis {X : Type u} [TopologicalSpace X] (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ C ⊆ U

private theorem upper_open (x : K) : IsOpen ({upper x} : Set (Duplicate K)) := by
  intro y hy
  have h := congrArg Duplicate.upper (show lower y = upper x from hy)
  cases h

private theorem projection_continuous : Continuous (Duplicate.base : Duplicate K → K) := by
  apply continuous_def.mpr
  intro V hV x hx
  exact ⟨V, hV, hx, fun _ hy => ⟨hy, fun _ => hy⟩⟩

private theorem lower_continuous : Continuous (lower : K → Duplicate K) := by
  apply continuous_def.mpr
  intro s hs
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨V, hV, hxV, hVs⟩ := hs x hx
  exact Filter.mem_of_superset (hV.mem_nhds hxV) (fun y hy => (hVs y hy).1)

private theorem upper_compl_open [T1Space K] (p : K) :
    IsOpen ({upper p}ᶜ : Set (Duplicate K)) := by
  intro x _
  by_cases hxp : x = p
  · subst x
    refine ⟨univ, isOpen_univ, trivial, fun y _ => ⟨?_, ?_⟩⟩
    · simp [lower, upper]
    · intro hyp heq
      exact hyp (congrArg Duplicate.base heq)
  · refine ⟨{p}ᶜ, isClosed_singleton.isOpen_compl, hxp, fun y hy => ⟨?_, ?_⟩⟩
    · simp [lower, upper]
    · intro _ heq
      exact hy (congrArg Duplicate.base heq)

private theorem lower_upper_separation [T1Space K] (x : K) :
    ∃ U V : Set (Duplicate K), IsOpen U ∧ IsOpen V ∧ lower x ∈ U ∧ upper x ∈ V ∧
      Disjoint U V := by
  refine ⟨{upper x}ᶜ, {upper x}, upper_compl_open x, upper_open x, ?_, rfl, ?_⟩
  · simp [lower, upper]
  · exact disjoint_compl_left

private instance duplicate_t2 [T2Space K] : T2Space (Duplicate K) where
  t2 := by
    rintro ⟨x, b⟩ ⟨y, c⟩ hne
    by_cases hxy : x = y
    · subst y
      cases b <;> cases c
      · exact False.elim (hne rfl)
      · exact lower_upper_separation x
      · obtain ⟨U, V, hU, hV, hxU, hxV, hd⟩ := lower_upper_separation x
        exact ⟨V, U, hV, hU, hxV, hxU, hd.symm⟩
      · exact False.elim (hne rfl)
    · obtain ⟨U, V, hU, hV, hxU, hyV, hd⟩ := t2_separation hxy
      exact ⟨Duplicate.base ⁻¹' U, Duplicate.base ⁻¹' V,
        hU.preimage projection_continuous, hV.preimage projection_continuous,
        hxU, hyV, hd.preimage Duplicate.base⟩

private instance duplicate_compact [CompactSpace K] : CompactSpace (Duplicate K) where
  isCompact_univ := by
    classical
    apply isCompact_of_finite_subcover
    intro ι U hU hcover
    have hlow : ∀ x : K, ∃ i, lower x ∈ U i := by
      intro x
      exact mem_iUnion.mp (hcover (mem_univ (lower x)))
    choose j hj using hlow
    have hlocal := fun x : K => hU (j x) x (hj x)
    choose V hV hxV hVs using hlocal
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV (by
      intro x _
      exact mem_iUnion.mpr ⟨x, hxV x⟩)
    have hup : ∀ x : K, ∃ i, upper x ∈ U i := by
      intro x
      exact mem_iUnion.mp (hcover (mem_univ (upper x)))
    choose k hk using hup
    refine ⟨s.image j ∪ s.image k, ?_⟩
    rintro ⟨x, b⟩ _
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    cases b
    · exact mem_iUnion₂.mpr ⟨j p, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩),
        (hVs p x hxp).1⟩
    · by_cases h : x = p
      · subst x
        exact mem_iUnion₂.mpr ⟨k p,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩), hk p⟩
      · exact mem_iUnion₂.mpr ⟨j p, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩),
          (hVs p x hxp).2 h⟩

private theorem upper_dense [PerfectSpace K] : Dense (range (upper : K → Duplicate K)) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨⟨x, b⟩, hx⟩
  cases b
  · obtain ⟨V, hV, hxV, hVs⟩ := hU x hx
    obtain ⟨y, hy, hyx⟩ := (preperfect_iff_nhds.mp PerfectSpace.univ_preperfect) x
      (mem_univ x) V (hV.mem_nhds hxV)
    exact ⟨upper y, (hVs y hy.1).2 hyx, ⟨y, rfl⟩⟩
  · exact ⟨upper x, hx, ⟨x, rfl⟩⟩

private theorem lower_not_clopen_based [T2Space K] [PreconnectedSpace K] [Nontrivial K]
    (x : K) : ¬ HasClopenBasis (lower x) := by
  intro h
  obtain ⟨y, hy⟩ := exists_ne x
  let U : Set (Duplicate K) := Duplicate.base ⁻¹' ({y}ᶜ : Set K)
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage projection_continuous
  obtain ⟨C, hC, hxC, hCU⟩ := h U hU (by exact Ne.symm hy)
  have htrace : lower ⁻¹' C = (univ : Set K) :=
    (hC.preimage lower_continuous).eq_univ ⟨x, hxC⟩
  have hyC : lower y ∈ C := by rw [← mem_preimage, htrace]; trivial
  exact (hCU hyC) rfl

/-- The full duplicate-space topology, including the exact dense clopen locus.
The statement applies in particular to the two-sphere and retains its closed
bottom copy rather than replacing the base by a finite or zero-dimensional one. -/
theorem topological_frontier [CompactSpace K] [T2Space K] [ConnectedSpace K] [Nontrivial K] :
    CompactSpace (Duplicate K) ∧ T2Space (Duplicate K) ∧
    Continuous (Duplicate.base : Duplicate K → K) ∧
    LeftInverse (Duplicate.base : Duplicate K → K) lower ∧
    IsClosedEmbedding (lower : K → Duplicate K) ∧
    Dense (range (upper : K → Duplicate K)) ∧
    (∀ z : Duplicate K, HasClopenBasis z ↔ z ∈ range upper) ∧
    ¬ ZeroDimensionalSpace (Duplicate K) := by
  have hlocus : ∀ z : Duplicate K, HasClopenBasis z ↔ z ∈ range upper := by
    rintro ⟨x, b⟩
    cases b
    · exact iff_of_false (lower_not_clopen_based x) (by simp [upper])
    · constructor
      · intro _; exact ⟨x, rfl⟩
      · intro _ U _ hxU
        exact ⟨{upper x}, ⟨isClosed_singleton, upper_open x⟩, rfl,
          singleton_subset_iff.mpr hxU⟩
  refine ⟨inferInstance, inferInstance, projection_continuous, fun _ => rfl,
    lower_continuous.isClosedEmbedding (fun x y h => congrArg Duplicate.base h),
    upper_dense, hlocus, ?_⟩
  intro hz
  haveI := hz
  obtain ⟨x⟩ := (inferInstance : Nonempty K)
  apply lower_not_clopen_based x
  intro U hU hxU
  obtain ⟨C, hC, hxC, hCU⟩ := isTopologicalBasis_isClopen.exists_subset_of_mem_open hxU hU
  exact ⟨C, hC, hxC, hCU⟩

end D5.S3.Topology.Separation.AlexandroffDuplicate
