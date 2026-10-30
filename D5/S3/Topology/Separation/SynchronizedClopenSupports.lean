/- GID: D5/S3/Topology/Separation/SynchronizedClopenSupports
   generality: G
   mirror-B: D5/B/S3/Topology/Separation/SynchronizedClopenSupports
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous infinite-image maps admit disjoint ambient supports for source-image pairs. -/

import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.NatEmbedding

/-!
# Synchronized ambient clopen supports

A continuous map from a closed subset of a compact zero-dimensional Hausdorff
space, with infinite image disjoint from its domain, admits countably many
literally disjoint ambient clopens containing corresponding source-image pairs.
A single ambient clopen separates the entire domain from the entire image.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Topology

namespace D5.S3.Topology.Separation.SynchronizedClopenSupports

universe u

/-- Both marked points survive finite-difference disjointization of paired
clopen neighborhoods; relative disjointness is used only to exclude markers. -/
theorem exists_synchronized_clopen_supports {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [ZeroDimensionalSpace X]
    (F : Set X) (hF : IsClosed F) (f : F → X) (hf : Continuous f)
    (hinf : (range f).Infinite) (hdisj : Disjoint F (range f)) :
    ∃ P : Set X, IsClopen P ∧ F ⊆ P ∧ range f ⊆ Pᶜ ∧
      ∃ a : ℕ → F, ∃ W : ℕ → Set X,
        (∀ n, IsClopen (W n)) ∧ Pairwise (Disjoint on W) ∧
        (∀ n, (a n).val ∈ W n ∧ f (a n) ∈ W n) := by
  classical
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  have hclosed : IsClosed (range f) := (isCompact_range hf).isClosed
  obtain ⟨P, hP, hFP, hPrange⟩ := exists_clopen_of_closed_subset_open hF
    hclosed.isOpen_compl (Set.disjoint_left.mp hdisj)
  have hrangeP : range f ⊆ Pᶜ := by
    intro x hx hxP
    exact hPrange hxP hx
  let R : Set X := range f
  letI : Infinite R := hinf.to_subtype
  obtain ⟨U, hUinf, hUopen, hUdisj⟩ :=
    exists_seq_infinite_isOpen_pairwise_disjoint R
  choose y hy using fun n => (hUinf n).nonempty
  choose a ha using fun n => (y n).property
  have ambient (n : ℕ) : ∃ O : Set X, IsOpen O ∧
      (Subtype.val : R → X) ⁻¹' O = U n :=
    Topology.IsInducing.subtypeVal.isOpen_iff.mp (hUopen n)
  choose O hO hOtrace using ambient
  have hyO (n : ℕ) : (y n).val ∈ O n := by
    change y n ∈ (Subtype.val : R → X) ⁻¹' O n
    rw [hOtrace n]
    exact hy n
  have sourceOpen (n : ℕ) : ∃ S : Set X, IsOpen S ∧
      (Subtype.val : F → X) ⁻¹' S = f ⁻¹' O n :=
    Topology.IsInducing.subtypeVal.isOpen_iff.mp ((hO n).preimage hf)
  choose S hS hStrace using sourceOpen
  have haS (n : ℕ) : (a n).val ∈ S n := by
    change a n ∈ (Subtype.val : F → X) ⁻¹' S n
    rw [hStrace n]
    change f (a n) ∈ O n
    rw [ha n]
    exact hyO n
  have sourceClopen (n : ℕ) : ∃ C : Set X,
      IsClopen C ∧ (a n).val ∈ C ∧ C ⊆ P ∩ S n :=
    exists_isClopen_mem_of_isOpen (hP.isOpen.inter (hS n))
      ⟨hFP (a n).property, haS n⟩
  have targetClopen (n : ℕ) : ∃ D : Set X,
      IsClopen D ∧ (y n).val ∈ D ∧ D ⊆ Pᶜ ∩ O n :=
    exists_isClopen_mem_of_isOpen (hP.compl.isOpen.inter (hO n))
      ⟨hrangeP (y n).property, hyO n⟩
  choose C hC haC hCsub using sourceClopen
  choose D hD hyD hDsub using targetClopen
  have sourceTrace (n m : ℕ) (hmem : (a n).val ∈ C m) : y n ∈ U m := by
    have hs : a n ∈ (Subtype.val : F → X) ⁻¹' S m := (hCsub m hmem).2
    rw [hStrace m] at hs
    have ho : (y n).val ∈ O m := by
      change f (a n) ∈ O m at hs
      rwa [ha n] at hs
    rw [← hOtrace m]
    exact ho
  have targetTrace (n m : ℕ) (hmem : f (a n) ∈ D m) : y n ∈ U m := by
    rw [← hOtrace m]
    have ho := (hDsub m hmem).2
    rwa [ha n] at ho
  let E : ℕ → Set X := fun n => C n ∪ D n
  have hE (n : ℕ) : IsClopen (E n) := (hC n).union (hD n)
  have haE (n : ℕ) : (a n).val ∈ E n := Or.inl (haC n)
  have hfE (n : ℕ) : f (a n) ∈ E n := Or.inr (ha n ▸ hyD n)
  have haMiss (n m : ℕ) (hnm : n ≠ m) : (a n).val ∉ E m := by
    rintro (hc | hd)
    · exact Set.disjoint_left.mp (hUdisj hnm) (hy n) (sourceTrace n m hc)
    · exact (hDsub m hd).1 (hFP (a n).property)
  have hfMiss (n m : ℕ) (hnm : n ≠ m) : f (a n) ∉ E m := by
    rintro (hc | hd)
    · exact hrangeP (mem_range_self (a n)) (hCsub m hc).1
    · exact Set.disjoint_left.mp (hUdisj hnm) (hy n) (targetTrace n m hd)
  let W : ℕ → Set X := fun n => E n \ ⋃ m ∈ Finset.range n, E m
  have hW (n : ℕ) : IsClopen (W n) :=
    (hE n).diff (isClopen_biUnion_finset fun m _ => hE m)
  have survives (n : ℕ) {x : X} (hx : x ∈ E n)
      (hmiss : ∀ m, n ≠ m → x ∉ E m) : x ∈ W n := by
    refine ⟨hx, ?_⟩
    intro hu
    obtain ⟨m, hm⟩ := mem_iUnion.mp hu
    obtain ⟨hmn, hxm⟩ := mem_iUnion.mp hm
    exact hmiss m (Nat.ne_of_gt (Finset.mem_range.mp hmn)) hxm
  have disjoint_lt {n m : ℕ} (hnm : n < m) : Disjoint (W n) (W m) := by
    apply Set.disjoint_left.mpr
    intro x hxn hxm
    exact hxm.2 (mem_iUnion.mpr ⟨n,
      mem_iUnion.mpr ⟨Finset.mem_range.mpr hnm, hxn.1⟩⟩)
  refine ⟨P, hP, hFP, hrangeP, a, W, hW, ?_, ?_⟩
  · intro n m hnm
    rcases lt_or_gt_of_ne hnm with h | h
    · exact disjoint_lt h
    · exact (disjoint_lt h).symm
  · intro n
    exact ⟨survives n (haE n) (haMiss n), survives n (hfE n) (hfMiss n)⟩

end D5.S3.Topology.Separation.SynchronizedClopenSupports
