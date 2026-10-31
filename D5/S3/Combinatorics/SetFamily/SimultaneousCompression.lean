/- GID: D5/S3/Combinatorics/SetFamily/SimultaneousCompression
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SetFamily/SimultaneousCompression
   mirror-E: none(waiver:general-structural-theorem)
   anchors: []
   utility: none
   digest: A simultaneous local compression preserves cross-intersection after coordinate deletion. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

open Finset

namespace D5.S3.Combinatorics.SetFamily.SimultaneousCompression

variable {α : Type*} [DecidableEq α]

/-- Each member of the first family meets every member of the second. -/
def CrossIntersecting (A B : Finset (Finset α)) : Prop :=
  ∀ X ∈ A, ∀ Y ∈ B, ¬ Disjoint X Y

/-- Replace a distinguished coordinate by another one. -/
def shift (s t : α) (X : Finset α) : Finset α := insert s (X.erase t)

private def moved (A : Finset (Finset α)) (s t : α) : Finset (Finset α) :=
  A.filter fun X => t ∈ X ∧ shift s t X ∉ A

/-- Move selected t-traces to their s-trace and its feasible u-extension. -/
def compressedFamily (Ω A : Finset (Finset α)) (s t u : α) : Finset (Finset α) :=
  (A \ moved A s t) ∪ (moved A s t).image (shift s t) ∪
    (((moved A s t).image fun X => insert u (shift s t X)).filter (· ∈ Ω))

private lemma moved_mem {A : Finset (Finset α)} {s t : α} {X : Finset α}
    (hX : X ∈ moved A s t) : X ∈ A ∧ t ∈ X ∧ shift s t X ∉ A := by
  simpa only [moved, mem_filter] using hX

private lemma compressed_cases {Ω A : Finset (Finset α)} {s t u : α}
    {X : Finset α} (hX : X ∈ compressedFamily Ω A s t u) :
    (X ∈ A ∧ (t ∈ X → shift s t X ∈ A)) ∨
      (s ∈ X ∧ ∃ Z ∈ A, t ∈ Z ∧ ∀ a ∈ Z.erase t, a ∈ X) := by
  rcases mem_union.mp hX with hX | hX
  · rcases mem_union.mp hX with hX | hX
    · rcases mem_sdiff.mp hX with ⟨hXA, hXm⟩
      left
      refine ⟨hXA, ?_⟩
      intro ht
      by_contra hs
      exact hXm (mem_filter.mpr ⟨hXA, ht, hs⟩)
    · obtain ⟨Z, hZ, rfl⟩ := mem_image.mp hX
      obtain ⟨hZA, htZ, _⟩ := moved_mem hZ
      right
      refine ⟨by simp [shift], Z, hZA, htZ, ?_⟩
      intro a ha
      exact mem_insert_of_mem ha
  · obtain ⟨hX, _⟩ := mem_filter.mp hX
    obtain ⟨Z, hZ, rfl⟩ := mem_image.mp hX
    obtain ⟨hZA, htZ, _⟩ := moved_mem hZ
    right
    refine ⟨by simp [shift], Z, hZA, htZ, ?_⟩
    intro a ha
    exact mem_insert_of_mem (mem_insert_of_mem ha)

private lemma compressed_subset {Ω A : Finset (Finset α)} {s t u : α}
    (hA : A ⊆ Ω)
    (hshift : ∀ X ∈ Ω, t ∈ X → shift s t X ∈ Ω) :
    compressedFamily Ω A s t u ⊆ Ω := by
  intro X hX
  rcases mem_union.mp hX with hX | hX
  · rcases mem_union.mp hX with hX | hX
    · exact hA (mem_sdiff.mp hX).1
    · obtain ⟨Z, hZ, rfl⟩ := mem_image.mp hX
      obtain ⟨hZA, htZ, _⟩ := moved_mem hZ
      exact hshift Z (hA hZA) htZ
  · exact (mem_filter.mp hX).2

private lemma compressed_cross_one_sided {Ω A B : Finset (Finset α)} {s t u : α}
    (hA : A ⊆ Ω) (hB : B ⊆ Ω) (hst : s ≠ t)
    (hexcludes : ∀ Z ∈ Ω, t ∈ Z → s ∉ Z ∧ u ∉ Z)
    (hcross : CrossIntersecting A B)
    {X Y : Finset α}
    (hX : X ∈ compressedFamily Ω A s t u)
    (hY : Y ∈ compressedFamily Ω B s t u) (hsY : s ∉ Y) :
    ¬ Disjoint (X.erase t) (Y.erase t) := by
  intro hd
  have meet_eq : ∀ {a}, a ∈ X → a ∈ Y → a = t := by
    intro a haX haY
    by_contra hat
    exact (disjoint_left.mp hd) (mem_erase.mpr ⟨hat, haX⟩)
      (mem_erase.mpr ⟨hat, haY⟩)
  have hYold : Y ∈ B ∧ (t ∈ Y → shift s t Y ∈ B) := by
    rcases compressed_cases hY with h | h
    · exact h
    · exact False.elim (hsY h.1)
  rcases compressed_cases hX with hXold | hXnew
  · by_cases htX : t ∈ X
    · obtain ⟨a, haShift, haY⟩ := not_disjoint_iff.mp
        (hcross (shift s t X) (hXold.2 htX) Y hYold.1)
      rcases mem_insert.mp haShift with has | haR
      · exact hsY (has ▸ haY)
      · exact (mem_erase.mp haR).1 (meet_eq (mem_erase.mp haR).2 haY)
    · obtain ⟨a, haX, haY⟩ := not_disjoint_iff.mp (hcross X hXold.1 Y hYold.1)
      exact htX (meet_eq haX haY ▸ haX)
  · obtain ⟨_, Z, hZA, htZ, hRest⟩ := hXnew
    have htY : t ∈ Y := by
      obtain ⟨a, haZ, haY⟩ := not_disjoint_iff.mp (hcross Z hZA Y hYold.1)
      by_cases hat : a = t
      · exact hat ▸ haY
      · exact False.elim (hat (meet_eq (hRest a (mem_erase.mpr ⟨hat, haZ⟩)) haY))
    obtain ⟨a, haZ, haShift⟩ := not_disjoint_iff.mp
      (hcross Z hZA (shift s t Y) (hYold.2 htY))
    rcases mem_insert.mp haShift with has | haR
    · exact (hexcludes Z (hA hZA) htZ).1 (has ▸ haZ)
    · have hat := (mem_erase.mp haR).1
      exact hat (meet_eq (hRest a (mem_erase.mpr ⟨hat, haZ⟩)) (mem_erase.mp haR).2)

private lemma compressed_cross {Ω A B : Finset (Finset α)} {s t u : α}
    (hA : A ⊆ Ω) (hB : B ⊆ Ω) (hst : s ≠ t)
    (hexcludes : ∀ Z ∈ Ω, t ∈ Z → s ∉ Z ∧ u ∉ Z)
    (hcross : CrossIntersecting A B) :
    CrossIntersecting
      ((compressedFamily Ω A s t u).image (fun X => X.erase t))
      ((compressedFamily Ω B s t u).image (fun X => X.erase t)) := by
  intro X hX Y hY
  obtain ⟨X, hX, rfl⟩ := mem_image.mp hX
  obtain ⟨Y, hY, rfl⟩ := mem_image.mp hY
  by_cases hsY : s ∈ Y
  · by_cases hsX : s ∈ X
    · intro hd
      exact (disjoint_left.mp hd) (mem_erase.mpr ⟨hst, hsX⟩)
        (mem_erase.mpr ⟨hst, hsY⟩)
    · have hc : CrossIntersecting B A := by
        intro V hV W hW
        exact (hcross W hW V hV).symm
      exact (compressed_cross_one_sided hB hA hst hexcludes hc hY hX hsX).symm
  · exact compressed_cross_one_sided hA hB hst hexcludes hcross hX hY hsY

private lemma augmented_not_mem {Ω A B : Finset (Finset α)} {s t u : α}
    (hA : A ⊆ Ω) (hB : B ⊆ Ω)
    (hexcludes : ∀ Z ∈ Ω, t ∈ Z → s ∉ Z ∧ u ∉ Z)
    (hshift : ∀ Z ∈ Ω, t ∈ Z → shift s t Z ∈ Ω)
    (hcross : CrossIntersecting A B)
    (hmaxA : ∀ Z ∈ Ω, (∀ Y ∈ B, ¬ Disjoint Z Y) → Z ∈ A)
    {X : Finset α} (hX : X ∈ moved A s t) :
    insert u (shift s t X) ∉ A := by
  obtain ⟨hXA, htX, hsXA⟩ := moved_mem hX
  intro hAug
  apply hsXA
  apply hmaxA _ (hshift X (hA hXA) htX)
  intro Y hY hd
  have htY : t ∈ Y := by
    obtain ⟨a, haX, haY⟩ := not_disjoint_iff.mp (hcross X hXA Y hY)
    by_cases hat : a = t
    · exact hat ▸ haY
    · exact False.elim ((disjoint_left.mp hd)
        (mem_insert_of_mem (mem_erase.mpr ⟨hat, haX⟩)) haY)
  obtain ⟨a, haAug, haY⟩ := not_disjoint_iff.mp
    (hcross (insert u (shift s t X)) hAug Y hY)
  rcases mem_insert.mp haAug with hau | haShift
  · exact (hexcludes Y (hB hY) htY).2 (hau ▸ haY)
  · exact (disjoint_left.mp hd) haShift haY

end D5.S3.Combinatorics.SetFamily.SimultaneousCompression
