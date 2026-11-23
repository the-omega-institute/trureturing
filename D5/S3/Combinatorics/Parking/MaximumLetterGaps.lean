/- GID: D5/S3/Combinatorics/Parking/MaximumLetterGaps
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Parking/MaximumLetterGaps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered gap profiles for bounded parking words with a fixed maximum-letter multiplicity. -/

import D5.S1.Words.UnaryGapWords
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Parking.DescentRefinement

open D5.S1.Words.UnaryGapWords

local notation "sorted" => List.insertionSort (· ≤ ·)

/-- Zero-based index i represents the one-based parking position i + 1. -/
def RankBound (s : List Nat) : Prop :=
  ∀ i (hi : i < s.length), s[i] ≤ i + 1

def BoundedParking (n m : Nat) (w : List Nat) : Prop :=
  w.length = n ∧ (∀ x ∈ w, 1 ≤ x ∧ x ≤ m) ∧ RankBound (sorted w)

def Original (n m r : Nat) :=
  {w : List Nat // BoundedParking n m w ∧ w.count m = r}

def Retained (n m r : Nat) :=
  {p : List Nat × List Nat //
    BoundedParking (n - r) (m - 1) p.1 ∧ p.2.length = n - r + 1 ∧ p.2.sum = r}

private theorem gap_perm (m : Nat) (cs : List Nat) (h : List Nat)
    (hh : h.length = cs.length + 1) :
    (gap m cs h).Perm (cs ++ List.replicate h.sum m) := by
  induction cs generalizing h with
  | nil =>
    cases h with
    | nil => simp at hh
    | cons j hs =>
      have hz : hs = [] := List.length_eq_zero_iff.mp (by simpa using hh)
      subst hs
      simp [gap]
  | cons c cs ih =>
    cases h with
    | nil => simp at hh
    | cons j hs =>
      have ht : hs.length = cs.length + 1 := by simpa using hh
      have hp := (ih hs ht).cons c
      have hstep : (gap m (c :: cs) (j :: hs)).Perm
          ((List.replicate j m ++ (c :: cs)) ++ List.replicate hs.sum m) := by
        simpa [gap, List.append_assoc] using hp.append_left (List.replicate j m)
      apply hstep.trans
      rw [List.sum_cons, List.replicate_add]
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := List.replicate j m) (l₂ := c :: cs)).append_right
          (List.replicate hs.sum m)

theorem gap_counts (m : Nat) (cs h : List Nat)
    (hh : h.length = cs.length + 1) (x : Nat) :
    (gap m cs h).count x = cs.count x + (List.replicate h.sum m).count x := by
  rw [(gap_perm m cs h hh).count_eq x, List.count_append]

theorem sorted_gap_reconstruction (m : Nat) (cs h : List Nat)
    (hh : h.length = cs.length + 1) (hmax : ∀ x ∈ cs, x ≤ m) :
    sorted (gap m cs h) = sorted cs ++ List.replicate h.sum m := by
  have hp : (sorted (gap m cs h)).Perm (sorted cs ++ List.replicate h.sum m) :=
    (List.perm_insertionSort _ _).trans
      ((gap_perm m cs h hh).trans ((List.perm_insertionSort _ _).symm.append_right _))
  apply hp.eq_of_pairwise' (List.pairwise_insertionSort _ _)
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_insertionSort _ _, List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩
  intro x hx y hy
  have he : y = m := List.eq_of_mem_replicate hy
  rw [he]
  exact hmax x ((List.perm_insertionSort _ cs).mem_iff.mp hx)

theorem rank_append_replicate (s : List Nat) (m r : Nat) (hr : 0 < r) :
    RankBound (s ++ List.replicate r m) ↔ RankBound s ∧ m ≤ s.length + 1 := by
  constructor
  · intro hb
    constructor
    · intro i hi
      have hi' : i < (s ++ List.replicate r m).length := by
        simp only [List.length_append]
        omega
      simpa only [List.getElem_append_left hi] using hb i hi'
    · have hi : s.length < (s ++ List.replicate r m).length := by simpa using hr
      have he := hb s.length hi
      rw [List.getElem_append_right (Nat.le_refl _), List.getElem_replicate] at he
      exact he
  · rintro ⟨hb, hm⟩ i hi
    by_cases hprefix : i < s.length
    · rw [List.getElem_append_left hprefix]
      exact hb i hprefix
    · have hindex : s.length ≤ i := Nat.le_of_not_gt hprefix
      rw [List.getElem_append_right hindex, List.getElem_replicate]
      omega

/-- The sorted parking condition transports through the literal retained prefix. -/
theorem sorted_prefix_membership {n m r : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hr : 1 ≤ r) (hcut : r ≤ n - m + 1) (cs h : List Nat)
    (hlen : cs.length = n - r) (hh : h.length = n - r + 1) (hs : h.sum = r)
    (hmax : ∀ x ∈ cs, x < m) :
    BoundedParking n m (gap m cs h) ↔ BoundedParking (n - r) (m - 1) cs := by
  have hshape : h.length = cs.length + 1 := by omega
  have hperm := gap_perm m cs h hshape
  have hl : (gap m cs h).length = n := by
    have he := hperm.length_eq
    simp only [List.length_append, List.length_replicate, hlen, hs] at he
    omega
  have hsort := sorted_gap_reconstruction m cs h hshape
    (fun x hx => Nat.le_of_lt (hmax x hx))
  have hsortlen : (sorted cs).length = cs.length := List.length_insertionSort _ _
  have hlast : m ≤ (sorted cs).length + 1 := by omega
  have hrank : RankBound (sorted (gap m cs h)) ↔ RankBound (sorted cs) := by
    rw [hsort, hs, rank_append_replicate _ _ _ hr]
    exact and_iff_left hlast
  constructor
  · rintro ⟨_, hb, hp⟩
    refine ⟨hlen, ?_, hrank.mp hp⟩
    intro x hx
    have hxgap := hperm.mem_iff.mpr (List.mem_append_left _ hx)
    exact ⟨(hb x hxgap).1, by have := hmax x hx; omega⟩
  · rintro ⟨_, hb, hp⟩
    refine ⟨hl, ?_, hrank.mpr hp⟩
    intro x hx
    rcases List.mem_append.mp (hperm.mem_iff.mp hx) with hc | hc
    · exact ⟨(hb x hc).1, Nat.le_of_lt (hmax x hc)⟩
    · have he : x = m := List.eq_of_mem_replicate hc
      subst x
      exact ⟨by omega, le_rfl⟩

private theorem count_gap_max (m : Nat) (cs h : List Nat)
    (hh : h.length = cs.length + 1) (hne : ∀ x ∈ cs, x ≠ m) :
    (gap m cs h).count m = h.sum := by
  rw [gap_counts m cs h hh m, List.count_eq_zero_of_not_mem (fun hx => hne m hx rfl)]
  simp

private theorem canonical_gap (m : Nat) (w : List Nat) :
    (∀ x ∈ spine m w, x ≠ m) ∧ (sizes m w).length = (spine m w).length + 1 ∧
      w = gap m (spine m w) (sizes m w) := by
  obtain ⟨cs, h, hne, hh, he⟩ := gap_exists m w
  have hp := profile_gap m cs h hne hh
  have hc : spine m w = cs := (congrArg (spine m) he).trans hp.1
  have hs : sizes m w = h := (congrArg (sizes m) he).trans hp.2
  rw [hc, hs]
  exact ⟨hne, hh, he⟩

noncomputable def delete {n m r : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hr : 1 ≤ r) (hcut : r ≤ n - m + 1) (w : Original n m r) : Retained n m r := by
  let cs := spine m w.val
  let h := sizes m w.val
  obtain ⟨hne, hh, he⟩ := canonical_gap m w.val
  change (∀ x ∈ cs, x ≠ m) at hne
  change h.length = cs.length + 1 at hh
  change w.val = gap m cs h at he
  have hs : h.sum = r := (count_gap_max m cs h hh hne).symm.trans
    ((congrArg (List.count m) he).symm.trans w.property.2)
  have hperm := gap_perm m cs h hh
  have hlen : cs.length = n - r := by
    have heq := hperm.length_eq
    rw [← he, w.property.1.1] at heq
    simp only [List.length_append, List.length_replicate, hs] at heq
    omega
  have hmax : ∀ x ∈ cs, x < m := by
    intro x hx
    have hxw : x ∈ w.val := by
      rw [he]
      exact hperm.mem_iff.mpr (List.mem_append_left _ hx)
    exact lt_of_le_of_ne (w.property.1.2.1 x hxw).2 (hne x hx)
  have hlen' : h.length = n - r + 1 := by omega
  refine ⟨(cs, h), (sorted_prefix_membership hm hmn hr hcut cs h hlen hlen' hs hmax).mp ?_,
    hlen', hs⟩
  rw [← he]
  exact w.property.1

def insert {n m r : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hr : 1 ≤ r) (hcut : r ≤ n - m + 1) (p : Retained n m r) : Original n m r := by
  obtain ⟨⟨cs, h⟩, hp, hh, hs⟩ := p
  have hlen : cs.length = n - r := hp.1
  change h.length = n - r + 1 at hh
  have hmax : ∀ x ∈ cs, x < m := by
    intro x hx
    have := (hp.2.1 x hx).2
    omega
  exact ⟨gap m cs h, (sorted_prefix_membership hm hmn hr hcut cs h hlen hh hs hmax).mpr hp,
    (count_gap_max m cs h (by omega) (fun x hx => (hmax x hx).ne)).trans hs⟩

private theorem insert_delete {n m r : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hr : 1 ≤ r) (hcut : r ≤ n - m + 1) (w : Original n m r) :
    insert hm hmn hr hcut (delete hm hmn hr hcut w) = w := by
  apply Subtype.ext
  change gap m (spine m w.val) (sizes m w.val) = w.val
  exact (canonical_gap m w.val).2.2.symm

private theorem delete_insert {n m r : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hr : 1 ≤ r) (hcut : r ≤ n - m + 1) (p : Retained n m r) :
    delete hm hmn hr hcut (insert hm hmn hr hcut p) = p := by
  obtain ⟨⟨cs, h⟩, hp, hh, _⟩ := p
  apply Subtype.ext
  change (spine m (gap m cs h), sizes m (gap m cs h)) = (cs, h)
  have hne : ∀ x ∈ cs, x ≠ m := by
    intro x hx he
    have := (hp.2.1 x hx).2
    omega
  have hlen : cs.length = n - r := hp.1
  change h.length = n - r + 1 at hh
  have hshape : h.length = cs.length + 1 := by omega
  obtain ⟨hs, hm⟩ := profile_gap m cs h hne hshape
  exact Prod.ext hs hm

noncomputable def parkingGapEquiv {n m r : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hr : 1 ≤ r) (hcut : r ≤ n - m + 1) : Original n m r ≃ Retained n m r where
  toFun := delete hm hmn hr hcut
  invFun := insert hm hmn hr hcut
  left_inv := insert_delete hm hmn hr hcut
  right_inv := delete_insert hm hmn hr hcut

end D5.S3.Combinatorics.Parking.DescentRefinement
