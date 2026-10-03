/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanRotation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanRotation
   mirror-E: none(waiver:circular-subsequence-transfer-for-padovan-proof)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Every rotation of a subword embeds in a rotation of the containing word. -/

import D5.S3.Combinatorics.ArcherCyclicDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanRotation

theorem rotate_sublist_of_sublist {u w : List ℕ} (hu : u.Sublist w)
    (r : ℕ) (hr : r < u.length) :
    ∃ s < w.length, (u.rotate r).Sublist (w.rotate s) := by
  let u₁ := u.take r
  let u₂ := u.drop r
  have huSplit : u = u₁ ++ u₂ := by simp [u₁, u₂]
  have hlen : u₁.length = r := by simp [u₁, Nat.min_eq_left (by omega : r ≤ u.length)]
  have hsub : (u₁ ++ u₂).Sublist w := by simpa [← huSplit] using hu
  obtain ⟨w₁, w₂, hw, h₁, h₂⟩ := List.append_sublist_iff.mp hsub
  have hu₂pos : 0 < u₂.length := by simp [u₂]; omega
  have hw₂pos : 0 < w₂.length := by have := h₂.length_le; omega
  refine ⟨w₁.length, ?_, ?_⟩
  · rw [hw]
    simp only [List.length_append]
    omega
  · have hrotu : u.rotate r = u₂ ++ u₁ := by
      calc
        u.rotate r = (u₁ ++ u₂).rotate u₁.length := by rw [← huSplit, hlen]
        _ = u₂ ++ u₁ := List.rotate_append_length_eq u₁ u₂
    rw [hw, hrotu, List.rotate_append_length_eq]
    exact h₂.append h₁

theorem rotate_quadruple_to_first (w : List ℕ) (a b c d : ℕ)
    (h : ∃ r < w.length, [a, b, c, d].Sublist (w.rotate r)) :
    ∃ s < w.length, ∃ t, w.rotate s = a :: t ∧ [b, c, d].Sublist t := by
  obtain ⟨r, hr, hsub⟩ := h
  obtain ⟨pre, post, hsplit, ha, htail⟩ := List.cons_sublist_iff.mp hsub
  obtain ⟨left, right, hpre⟩ := List.mem_iff_append.mp ha
  have hlength : 0 < w.length := by omega
  let s := (r + left.length) % w.length
  have hs : s < w.length := Nat.mod_lt _ hlength
  refine ⟨s, hs, right ++ post ++ left, ?_, ?_⟩
  · have hrot : w.rotate s = (w.rotate r).rotate left.length := by
      simp only [s, List.rotate_mod, List.rotate_rotate]
    rw [hrot, hsplit, hpre]
    have hdecomp : (left ++ a :: right) ++ post =
        left ++ (a :: right ++ post) := by simp [List.append_assoc]
    rw [hdecomp, List.rotate_append_length_eq]
    simp [List.append_assoc]
  · exact List.sublist_append_of_sublist_left
      (List.sublist_append_of_sublist_right (l₁ := right) htail)

end D5.S3.Combinatorics.ArcherCyclicPadovanRotation

namespace D5.S3.Combinatorics.ArcherCyclicPadovanSubwords

open ArcherCyclicDefs ArcherCyclicPadovanRotation

theorem circular_avoidance_sublist (ν u w : List ℕ) (hu : u.Sublist w)
    (havoid : ∀ s < w.length, ¬ ArrowWilfDefs.Contains ν [] ν.length (w.rotate s)) :
    ∀ r < u.length, ¬ ArrowWilfDefs.Contains ν [] ν.length (u.rotate r) := by
  intro r hr hocc
  obtain ⟨s, hs, hsub⟩ := rotate_sublist_of_sublist hu r hr
  apply havoid s hs
  rcases hocc with ⟨x, hx, hm, hp, ha⟩
  refine ⟨x, hx, ?_, hp.trans hsub, by simp⟩
  intro i hi hik
  exact hsub.subset (hm i hi hik)

end D5.S3.Combinatorics.ArcherCyclicPadovanSubwords

namespace D5.S3.Combinatorics.ArcherCyclicPadovanMinimumRooted

open ArcherCyclicDefs ArcherCyclicPadovanRotation

theorem circular_1324_iff_minimum_rooted (w : List ℕ) :
    (∃ r < w.length, ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r)) ↔
      ∃ r < w.length, ∃ a b c d t,
        w.rotate r = a :: t ∧ a < b ∧ b < c ∧ c < d ∧
          [c, b, d].Sublist t := by
  constructor
  · rintro ⟨r, hr, x, hx, hm, hs, ht⟩
    have h12 : x 1 < x 2 := hx 1 (by omega) (by simp)
    have h23 : x 2 < x 3 := hx 2 (by omega) (by simp)
    have h34 : x 3 < x 4 := hx 3 (by omega) (by simp)
    change [x 1, x 3, x 2, x 4].Sublist (w.rotate r) at hs
    obtain ⟨s, hslt, t, hroot, htail⟩ :=
      rotate_quadruple_to_first w (x 1) (x 3) (x 2) (x 4) ⟨r, hr, hs⟩
    exact ⟨s, hslt, x 1, x 2, x 3, x 4, t,
      hroot, h12, h23, h34, htail⟩
  · rintro ⟨r, hr, a, b, c, d, t, hroot, hab, hbc, hcd, htail⟩
    let x : ℕ → ℕ := fun i =>
      if i = 1 then a else if i = 2 then b else if i = 3 then c else d
    have hsub : [a, c, b, d].Sublist (w.rotate r) := by
      rw [hroot]
      exact htail.cons_cons a
    refine ⟨r, hr, x, ?_, ?_, ?_, by simp⟩
    · intro i hi hik
      have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by
        have hik' : i < 4 := by simpa using hik
        omega
      rcases hi' with rfl | rfl | rfl <;> simp [x] <;> omega
    · intro i hi hik
      apply hsub.subset
      have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        have hik' : i ≤ 4 := by simpa using hik
        omega
      rcases hi' with rfl | rfl | rfl | rfl <;> simp [x]
    · simpa [x] using hsub

end D5.S3.Combinatorics.ArcherCyclicPadovanMinimumRooted
