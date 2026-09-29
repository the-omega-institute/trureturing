/- GID: D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicTetranacciPatterns
   mirror-E: none(waiver:cyclic-pattern-structure-has-no-independent-empirical-mirror)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Circular 1324 avoidance orders the rooted arcs around 2. -/

import D5.S3.Combinatorics.ArcherCyclicDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicTetranacciPatterns

open D5.S3.Combinatorics.ArcherCyclicDefs

/-- A 213 triple after the root 1 creates a 1324 pattern. -/
theorem rooted_suffix_avoids_213 (s : List ℕ)
    (hsmall : ∀ b ∈ s, 1 < b)
    (havoid : ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (1 :: s))
    (a b c : ℕ) (hba : b < a) (hac : a < c) :
    ¬ [a, b, c].Sublist s := by
  intro hsub
  have ha : a ∈ s := hsub.subset (by simp)
  have hb : b ∈ s := hsub.subset (by simp)
  have hc : c ∈ s := hsub.subset (by simp)
  have h1b : 1 < b := hsmall b hb
  apply havoid
  let x : ℕ → ℕ := fun i =>
    if i = 1 then 1 else if i = 2 then b else if i = 3 then a else c
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro i hi hik
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl <;> simp [x] <;> omega
  · intro i hi hik
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;> simp [x, ha, hb, hc]
  · simpa [x] using hsub.cons_cons 1
  · simp

/-- In a rooted 1324-avoiding word split at 2, every entry before 2 exceeds
every entry after 2. The duplicate-free condition makes the inequality strict. -/
theorem high_arc_above_low_arc (p s : List ℕ)
    (hnd : (p ++ 2 :: s).Nodup)
    (hp : ∀ a ∈ p, 2 < a)
    (havoid : ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (1 :: (p ++ 2 :: s)))
    (a b : ℕ) (ha : a ∈ p) (hb : b ∈ s) : b < a := by
  have hne : a ≠ b := by
    intro heq
    have hdis := (List.nodup_append'.mp hnd).2.2
    exact hdis ha (by simp [heq, hb])
  have hab : ¬ a < b := by
    intro hab
    have hpa : [a].Sublist p := List.singleton_sublist.mpr ha
    have hsb : [b].Sublist s := List.singleton_sublist.mpr hb
    have htail : [a, 2, b].Sublist (p ++ 2 :: s) := by
      simpa using hpa.append (hsb.cons_cons 2)
    have hroot : [1, a, 2, b].Sublist (1 :: (p ++ 2 :: s)) := htail.cons_cons 1
    have h2a : 2 < a := hp a ha
    apply havoid
    let x : ℕ → ℕ := fun i =>
      if i = 1 then 1 else if i = 2 then 2 else if i = 3 then a else b
    refine ⟨x, ?_, ?_, ?_, ?_⟩
    · intro i hi hik
      have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hcases with rfl | rfl | rfl <;> simp [x] <;> omega
    · intro i hi hik
      have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;> simp [x, ha, hb]
    · simpa [x] using hroot
    · simp
  omega

/-- After rotating a word to begin at 2, a descent in its low arc and a
high-arc entry make a circular 1324. -/
theorem low_arc_has_no_descent (p s : List ℕ)
    (hrot : ∀ r < (1 :: (p ++ 2 :: s)).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: (p ++ 2 :: s)).rotate r))
    (hsmall : ∀ a ∈ s, 2 < a)
    (hsep : ∀ c ∈ p, ∀ b ∈ s, b < c)
    (c : ℕ) (hc : c ∈ p)
    (a b : ℕ) (hba : a < b) :
    ¬ [b, a].Sublist s := by
  intro hsub
  have ha : a ∈ s := hsub.subset (by simp)
  have hb : b ∈ s := hsub.subset (by simp)
  have h2a : 2 < a := hsmall a ha
  have hbc : b < c := hsep c hc b hb
  have hr : 1 + p.length < (1 :: (p ++ 2 :: s)).length := by
    simp only [List.length_cons, List.length_append]
    omega
  have hrotate :
      (1 :: (p ++ 2 :: s)).rotate (1 + p.length) = (2 :: s) ++ (1 :: p) := by
    have hn : 1 + p.length = (1 :: p).length := by simp [Nat.add_comm]
    rw [hn]
    simpa only [List.cons_append] using
      List.rotate_append_length_eq (1 :: p) (2 :: s)
  have hfirst : [2, b, a].Sublist (2 :: s) := hsub.cons_cons 2
  have hlast : [c].Sublist (1 :: p) :=
    List.singleton_sublist.mpr (by simp [hc])
  have hfull : [2, b, a, c].Sublist ((2 :: s) ++ (1 :: p)) := by
    simpa using hfirst.append hlast
  have havoid := hrot (1 + p.length) hr
  rw [hrotate] at havoid
  apply havoid
  let x : ℕ → ℕ := fun i =>
    if i = 1 then 2 else if i = 2 then a else if i = 3 then b else c
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro i hi hik
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl <;> simp [x] <;> omega
  · intro i hi hik
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;> simp [x, ha, hb, hc]
  · simpa [x] using hfull
  · simp

end D5.S3.Combinatorics.ArcherCyclicTetranacciPatterns
