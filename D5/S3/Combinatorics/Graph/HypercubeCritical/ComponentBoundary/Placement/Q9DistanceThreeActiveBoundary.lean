/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeActiveBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeActiveBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Unshared distance-three contacts constrain the degrees of active exterior rows. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorEdgeLiftCount
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeUnsharedDirections

/-! Active exterior vertices at unshared distance-three contacts. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeActiveBoundary

open Finset
open Classical
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions exterior_even)
open BalancedCubeGirth (flip_comm no_selected_square three_step_first_direction_eq)
open Q9ExteriorEdgeLiftCount (exterior)
open private directions_subset_agreement from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance
open private differingAxes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private differingAxes_symm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
open private diff_pair diff_flip_left from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open private directions_eq_agreement_complement from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeUnsharedDirections

/-- Exterior vertices of C with an exterior neighbor of D. -/
def active (C D : Finset (Q 9)) : Finset (Q 9) :=
  (exterior C).filter fun z => (directions (exterior D) z).Nonempty

private theorem mem_exterior {C : Finset (Q 9)} {z : Q 9} :
    z ∈ exterior C ↔ z ∉ C ∧ (directions C z).Nonempty := by
  simp only [exterior, mem_filter, mem_sdiff, mem_univ, true_and]

private theorem contact_directions_across_edge
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y)
    (hdis : ∀ x ∈ C, ∀ y ∈ D, hammingDist x y = 3 →
      Disjoint (directions C x) (directions D y))
    {z : Q 9} {i t a : Fin 9}
    (hy : flip (flip z i) t ∈ D) (hx : flip z a ∈ C) :
    a ≠ i ∧ a ≠ t ∧ a ∉ directions D (flip (flip z i) t) ∧
      directions C (flip z a) =
        univ \ (directions D (flip (flip z i) t) ∪ insert a {i, t}) := by
  have hai : a ≠ i := by
    intro h
    subst a
    have hd : hammingDist (flip z i) (flip (flip z i) t) = 1 := flip_adj _ _
    have h := hsep _ hx _ hy
    omega
  have hit : i ≠ t := by
    intro h
    subst t
    have hd : hammingDist (flip z a) z = 1 := by
      rw [hammingDist_comm]
      exact flip_adj _ _
    have h := hsep _ hx _ hy
    rw [BalancedCriticalSpectrum.flip_flip] at h
    omega
  have hat : a ≠ t := by
    intro h
    subst t
    have hd : hammingDist (flip z a) (flip (flip z a) i) = 1 := flip_adj _ _
    have h := hsep _ hx _ hy
    rw [flip_comm z i a] at h
    omega
  have haxes : differingAxes (flip z a) (flip (flip z i) t) =
      insert a ({i, t} : Finset (Fin 9)) := by
    rw [diff_flip_left, diff_pair z hit, ite_eq_right (by simp [hai, hat])]
  have hd : hammingDist (flip z a) (flip (flip z i) t) = 3 := by
    change (differingAxes (flip z a) (flip (flip z i) t)).card = 3
    rw [haxes, card_insert_of_notMem (by simp [hai, hat]), card_pair hit]
  have hsep' : ∀ y ∈ D, ∀ x ∈ C, 3 ≤ hammingDist y x := by
    intro y hy x hx
    rw [hammingDist_comm y x]
    exact hsep x hx y hy
  have hd' : hammingDist (flip (flip z i) t) (flip z a) = 3 := by
    rw [hammingDist_comm, hd]
  have h := directions_eq_agreement_complement hrD hrC hsep' hy hx hd'
    (hdis _ hx _ hy hd).symm
  rw [differingAxes_symm (flip (flip z i) t) (flip z a), haxes] at h
  refine ⟨hai, hat, ?_, h⟩
  intro haD
  have hagrees := directions_subset_agreement hx (x := flip (flip z i) t)
    (fun u hu v hv => hd'.le.trans (hsep' u hu v hv))
  have heq := (mem_filter.mp (hagrees haD)).2
  have hdiff : a ∈ differingAxes (flip z a) (flip (flip z i) t) := by
    rw [haxes]
    exact mem_insert_self _ _
  exact (mem_filter.mp hdiff).2 heq.symm

/-- Two occupied neighbors of the same exterior row meet at the other midpoint.
The remaining occupied directions at the first neighbor also occur at the second. -/
private theorem pair_across_exterior_edge
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y)
    (hdis : ∀ x ∈ C, ∀ y ∈ D, hammingDist x y = 3 →
      Disjoint (directions C x) (directions D y))
    {z : Q 9} {i t a b : Fin 9}
    (hy : flip (flip z i) t ∈ D) (ha : flip z a ∈ C) (hb : flip z b ∈ C)
    (hab : a ≠ b) :
    flip (flip z a) b ∈ C ∧
      (directions C (flip z a)).erase b ⊆ directions C (flip z b) := by
  obtain ⟨_, _, _, hA⟩ := contact_directions_across_edge hrC hrD hsep hdis
    (z := z) (i := i) (t := t) hy ha
  obtain ⟨hbi, hbt, hbD, hB⟩ := contact_directions_across_edge hrC hrD hsep hdis
    (z := z) (i := i) (t := t) hy hb
  constructor
  · apply (mem_directions C (flip z a) b).mp
    rw [hA]
    exact mem_sdiff.mpr ⟨mem_univ _, by
      simp only [mem_union, mem_insert, mem_singleton, hbD, Ne.symm hab, hbi, hbt,
        or_self, not_false_eq_true]⟩
  · intro k hk
    obtain ⟨hkb, hk⟩ := mem_erase.mp hk
    rw [hA] at hk
    rw [hB]
    refine mem_sdiff.mpr ⟨mem_univ _, fun hu => (mem_sdiff.mp hk).2 ?_⟩
    rcases mem_union.mp hu with hd | hi
    · exact mem_union_left _ hd
    · exact mem_union_right _ (mem_insert_of_mem ((mem_insert.mp hi).resolve_left hkb))

/-- An active exterior vertex has exactly two occupied neighbors and at least two
exterior neighbors with no direction into the other exterior. -/
theorem active_boundary_degrees
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y)
    (hdis : ∀ x ∈ C, ∀ y ∈ D, hammingDist x y = 3 →
      Disjoint (directions C x) (directions D y))
    {z : Q 9} (hz : z ∈ active C D) :
    (directions C z).card = 2 ∧
      2 ≤ (directions (exterior C \ active C D) z).card := by
  rw [active, mem_filter] at hz
  obtain ⟨hz, i, hi⟩ := hz
  obtain ⟨hzC, hzne⟩ := mem_exterior.mp hz
  obtain ⟨_, t, ht⟩ := mem_exterior.mp ((mem_directions (exterior D) z i).mp hi)
  have hy := (mem_directions D (flip z i) t).mp ht
  have hpair {a b : Fin 9} (ha : flip z a ∈ C) (hb : flip z b ∈ C) (hab : a ≠ b) :
      flip (flip z a) b ∈ C ∧
        (directions C (flip z a)).erase b ⊆ directions C (flip z b) :=
    pair_across_exterior_edge hrC hrD hsep hdis (z := z) (i := i) (t := t) hy ha hb hab
  have hle : (directions C z).card ≤ 2 := by
    by_contra! hgt
    obtain ⟨a, ha⟩ := hzne
    have hcard := card_erase_add_one ha
    obtain ⟨b, hb, c, hc, hbc⟩ := one_lt_card.mp
      (show 1 < ((directions C z).erase a).card by omega)
    obtain ⟨hba, hb⟩ := mem_erase.mp hb
    obtain ⟨hca, hc⟩ := mem_erase.mp hc
    have hxa := (mem_directions C z a).mp ha
    have hxb := (mem_directions C z b).mp hb
    have hxc := (mem_directions C z c).mp hc
    have hxab := (hpair hxa hxb (Ne.symm hba)).1
    have hxac := (hpair hxa hxc (Ne.symm hca)).1
    have hxbc := (hpair hxb hxc hbc).1
    have haback : flip (flip (flip z a) b) a = flip z b := by
      rw [flip_comm z a b, BalancedCriticalSpectrum.flip_flip]
    have hacback : flip (flip (flip z a) c) a = flip z c := by
      rw [flip_comm z a c, BalancedCriticalSpectrum.flip_flip]
    -- The two three-step paths to the same occupied vertex form a six-cycle.
    refine hbc (three_step_first_direction_eq hbC (x := flip z a)
      (i := b) (j := a) (k := c) (a := c) (b := a) (c := b)
      hba (Ne.symm hca) hca (Ne.symm hba) hxa hxab ?_ ?_ hxac ?_ ?_ ?_)
    · simpa only [haback] using hxb
    · simpa only [haback] using hxbc
    · simpa only [hacback] using hxc
    · simpa only [hacback, flip_comm z c b] using hxbc
    · rw [haback, hacback, flip_comm z b c]
  have hdegree : (directions C z).card = 2 := by
    have hpos := card_pos.mpr hzne
    obtain ⟨n, hn⟩ := exterior_even C hrC hbC z hzC
    omega
  refine ⟨hdegree, ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp
    (show 1 < (directions C z).card by omega)
  have hdirs : ({a, b} : Finset (Fin 9)) = directions C z := by
    apply eq_of_subset_of_card_le
    · exact insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩
    · simp only [hdegree, card_pair hab, le_refl]
  have hxa := (mem_directions C z a).mp ha
  have hxb := (mem_directions C z b).mp hb
  obtain ⟨habC, hcommon⟩ := hpair hxa hxb hab
  have hsub : (directions C (flip z a)).erase b ⊆
      directions (exterior C \ active C D) z := by
    intro c hc
    have hcb := ne_of_mem_erase hc
    have hzac := (mem_directions C (flip z a) c).mp (mem_of_mem_erase hc)
    have hzbc := (mem_directions C (flip z b) c).mp (hcommon hc)
    have hca : c ≠ a := by
      intro h
      subst c
      exact hzC (by simpa only [BalancedCriticalSpectrum.flip_flip] using hzac)
    have hcz : c ∉ directions C z := by
      rw [← hdirs]
      simp [hca, hcb]
    have hwa : flip (flip z c) a ∈ C := by
      rw [flip_comm z c a]
      exact hzac
    have hwb : flip (flip z c) b ∈ C := by
      rw [flip_comm z c b]
      exact hzbc
    have hw : flip z c ∈ exterior C := mem_exterior.mpr
      ⟨fun hcC => hcz ((mem_directions C z c).mpr hcC),
        ⟨a, (mem_directions C (flip z c) a).mpr hwa⟩⟩
    have hinactive : flip z c ∉ active C D := by
      intro hh
      rw [active, mem_filter] at hh
      obtain ⟨j, hj⟩ := hh.2
      obtain ⟨_, s, hs⟩ :=
        mem_exterior.mp ((mem_directions (exterior D) (flip z c) j).mp hj)
      have hys := (mem_directions D (flip (flip z c) j) s).mp hs
      have hmid := (pair_across_exterior_edge hrC hrD hsep hdis
        (z := flip z c) (i := j) (t := s) hys hwa hwb hab).1
      have htriple : flip (flip (flip z a) b) c ∈ C := by
        rw [flip_comm (flip z a) b c, flip_comm z a c]
        exact hmid
      exact no_selected_square hbC (Ne.symm hcb) hxa habC hzac htriple
    exact (mem_directions (exterior C \ active C D) z c).mpr (mem_sdiff.mpr ⟨hw, hinactive⟩)
  have hcount := card_le_card hsub
  rw [card_erase_of_mem ((mem_directions C (flip z a) b).mpr habC),
    regular_directions C hrC hxa] at hcount
  exact hcount

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeActiveBoundary
