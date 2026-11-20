/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverPacking
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverPacking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Disjoint 32-vertex shells bound the number of eightfold exterior edges. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverSeparation
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal

/-! The packing bound from §§1–2 of `q9-pair-global-collision-pro.txt`. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverPacking

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced IsSwitching)
open Q9EightfoldCoverLocal (selectedCorners card_selected_corners)
open Q9EightfoldCoverSeparation (EightfoldCover firstShell eightfold_cover_shells_disjoint)
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private flip_at_other from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
open private corner_disagreements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal
open private mem_firstShell firstShell_subset from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverSeparation

local notation "flip" => BalancedCriticalSpectrum.flip

variable {C : Finset (Q 9)} {x : Q 9} {k : Fin 9}

open Classical in
/-- The unordered exterior edges covered by the support along all eight transverse axes. -/
def eightfoldCoverEdges (C : Finset (Q 9)) : Finset (Finset (Q 9)) :=
  ((Finset.univ : Finset (Q 9 × Fin 9)).filter fun e => EightfoldCover C e.1 e.2).image
    fun e => {e.1, flip e.1 e.2}

attribute [local irreducible] eightfoldCoverEdges

/-- Membership is witnessed by an endpoint and the axis of an eightfold cover. -/
theorem mem_eightfoldCoverEdges {e : Finset (Q 9)} :
    e ∈ eightfoldCoverEdges C ↔ ∃ x k, EightfoldCover C x k ∧ {x, flip x k} = e := by
  classical
  simp only [eightfoldCoverEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨x, k⟩, h, he⟩
    exact ⟨x, k, h, he⟩
  · rintro ⟨x, k, h, he⟩
    exact ⟨(x, k), h, he⟩

private theorem card_firstShell (x : Q 9) (k : Fin 9) : (firstShell x k).card = 16 := by
  classical
  let axes := Finset.univ.erase k
  have haxes : axes.card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hdisjoint : Disjoint (axes.image (flip x)) (axes.image (flip (flip x k))) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hq
    have h := congrFun he k
    rw [flip_at_other _ (Finset.mem_erase.mp hj).1,
      flip_at_other _ (Finset.mem_erase.mp hi).1] at h
    cases hx : x k <;> simp [BalancedCriticalSpectrum.flip, hx] at h
  rw [firstShell, Finset.biUnion_insert, Finset.singleton_biUnion]
  change ((axes.image (flip x)) ∪ (axes.image (flip (flip x k)))).card = 16
  rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_image_of_injective _ (flip_injective x),
    Finset.card_image_of_injective _ (flip_injective (flip x k)), haxes]

private theorem firstShell_disagreements {p : Q 9} (hp : p ∈ firstShell x k) :
    ((Finset.univ.erase k).filter fun t => x t ≠ p t).card = 1 := by
  classical
  obtain ⟨u, hu, i, hi, rfl⟩ := mem_firstShell.mp hp
  have hlayer (t : Fin 9) (ht : t ≠ k) : u t = x t := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · rfl
    · exact flip_at_other _ ht.symm
  have hsingle : ((Finset.univ.erase k).filter fun t => x t ≠ flip u i t) = {i} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_singleton]
    constructor
    · rintro ⟨ht, hd⟩
      by_contra hti
      exact hd (by rw [flip_at_other _ (Ne.symm hti), hlayer _ ht])
    · intro hti
      subst t
      refine ⟨hi, ?_⟩
      rw [← hlayer i hi]
      cases h : u i <;> simp [BalancedCriticalSpectrum.flip, h]
  rw [hsingle, Finset.card_singleton]

private theorem firstShell_disjoint_selectedCorners :
    Disjoint (firstShell x k) (selectedCorners C x k) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨_, i, j, hik, hjk, hij, hcorner⟩ :=
    Finset.mem_filter.mp (show p ∈ C.filter _ from hq)
  have h := firstShell_disagreements hp
  rw [corner_disagreements hik hjk hij hcorner, Finset.card_pair hij] at h
  exact (by decide : (2 : ℕ) ≠ 1) h

open Classical in
private theorem card_shell_union {sigma : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) :
    (firstShell x k ∪ selectedCorners C x k).card = 32 := by
  rw [Finset.card_union_of_disjoint firstShell_disjoint_selectedCorners, card_firstShell,
    card_selected_corners hr hs hx.1 hx.2.1 hx.2.2]

open Classical in
/-- Each unordered eightfold exterior edge uses 32 vertices of an induced balanced
cubic support in Q9, with disjoint sets of vertices for distinct edges. -/
theorem thirtyTwo_mul_card_eightfoldCoverEdges_le
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : 32 * (eightfoldCoverEdges C).card ≤ C.card := by
  classical
  obtain ⟨sigma, hs⟩ := hb
  let edges := eightfoldCoverEdges C
  have hrepresentative (e : {e // e ∈ edges}) :
      ∃ x k, EightfoldCover C x k ∧ ({x, flip x k} : Finset (Q 9)) = e.val :=
    (mem_eightfoldCoverEdges (C := C) (e := e.val)).mp e.property
  choose endpoint axis hcover hendpoints using hrepresentative
  let shell (e : {e // e ∈ edges}) := firstShell (endpoint e) (axis e) ∪
    selectedCorners C (endpoint e) (axis e)
  have hdisjoint : (edges.attach : Set {e // e ∈ edges}).PairwiseDisjoint shell := by
    intro e _ f _ hef
    apply eightfold_cover_shells_disjoint hr hs (hcover e) (hcover f)
    rw [hendpoints e, hendpoints f]
    exact fun h => hef (Subtype.ext h)
  have hcard (e : {e // e ∈ edges}) (_ : e ∈ edges.attach) : (shell e).card = 32 :=
    card_shell_union hr hs (hcover e)
  have hsubset : edges.attach.biUnion shell ⊆ C := by
    rw [Finset.biUnion_subset]
    intro e _
    exact Finset.union_subset (firstShell_subset (hcover e)) (Finset.filter_subset _ _)
  calc
    32 * (eightfoldCoverEdges C).card = (edges.attach.biUnion shell).card := by
      rw [Finset.card_biUnion hdisjoint, Finset.sum_const_nat hcard, Finset.card_attach,
        Nat.mul_comm]
    _ ≤ C.card := Finset.card_le_card hsubset

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverPacking
