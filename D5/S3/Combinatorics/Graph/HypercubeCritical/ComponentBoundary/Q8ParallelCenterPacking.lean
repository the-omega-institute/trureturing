/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q8ParallelCenterPacking
   generality: I
   mirror-B: none(waiver:standalone-research-source)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: A Hamming distance sum rules out five centers for parallel eightfold covers. -/

import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Linarith

/-! Parallel eightfold covers of a balanced cubic support project to words at
distance at least four. Two distance-four neighbors of the same word must be
antipodal. The distance-sum argument uses this extra restriction on the code. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8ParallelCenterPacking

open Finset
open scoped BigOperators

private def sumPairs (d : Fin 5 → Fin 5 → ℕ) : ℕ :=
  d 0 1 + d 0 2 + d 0 3 + d 0 4 + d 1 2 + d 1 3 + d 1 4 + d 2 3 + d 2 4 + d 3 4

private theorem bitPairSum_le (a b c d e : Bool) :
    (if a ≠ b then 1 else 0) + (if a ≠ c then 1 else 0) + (if a ≠ d then 1 else 0) +
      (if a ≠ e then 1 else 0) + (if b ≠ c then 1 else 0) + (if b ≠ d then 1 else 0) +
      (if b ≠ e then 1 else 0) + (if c ≠ d then 1 else 0) + (if c ≠ e then 1 else 0) +
      (if d ≠ e then 1 else 0) ≤ (6 : ℕ) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private theorem hammingSum_le (word : Fin 5 → Fin 8 → Bool) :
    sumPairs (fun i j => hammingDist (word i) (word j)) ≤ 48 := by
  unfold sumPairs
  simp only [hammingDist, card_eq_sum_ones, sum_filter, ← sum_add_distrib]
  calc
    _ ≤ ∑ _ : Fin 8, (6 : ℕ) := by
      apply sum_le_sum
      intro coordinate _
      exact bitPairSum_le (word 0 coordinate) (word 1 coordinate) (word 2 coordinate)
        (word 3 coordinate) (word 4 coordinate)
    _ = 48 := by decide

private theorem triangle_lower {a b c : ℕ} (ha : 4 ≤ a) (hb : 4 ≤ b) (hc : 4 ≤ c)
    (ha5 : a ≠ 5) (hb5 : b ≠ 5) (hc5 : c ≠ 5)
    (hab : a = 4 → b = 4 → 8 ≤ c) (hac : a = 4 → c = 4 → 8 ≤ b)
    (hbc : b = 4 → c = 4 → 8 ≤ a) : 16 ≤ a+b+c := by
  by_cases a = 4 <;> by_cases b = 4 <;> by_cases c = 4 <;> omega

private theorem codeSum_ge (d : Fin 5 → Fin 5 → ℕ) (parity : Fin 5 → Bool)
    (hpair : ∀ i j, i ≠ j → 4 ≤ d i j)
    (hcross : ∀ i j, parity i ≠ parity j → 5 ≤ d i j)
    (htriangle : ∀ i j k, i < j → j < k → parity i = parity j → parity j = parity k →
      16 ≤ d i j + d i k + d j k) : 50 ≤ sumPairs d := by
  have p01 := hpair 0 1 (by decide)
  have p02 := hpair 0 2 (by decide)
  have p03 := hpair 0 3 (by decide)
  have p04 := hpair 0 4 (by decide)
  have p12 := hpair 1 2 (by decide)
  have p13 := hpair 1 3 (by decide)
  have p14 := hpair 1 4 (by decide)
  have p23 := hpair 2 3 (by decide)
  have p24 := hpair 2 4 (by decide)
  have p34 := hpair 3 4 (by decide)
  have c01 := hcross 0 1
  have c02 := hcross 0 2
  have c03 := hcross 0 3
  have c04 := hcross 0 4
  have c12 := hcross 1 2
  have c13 := hcross 1 3
  have c14 := hcross 1 4
  have c23 := hcross 2 3
  have c24 := hcross 2 4
  have c34 := hcross 3 4
  have t012 := htriangle 0 1 2 (by decide) (by decide)
  have t013 := htriangle 0 1 3 (by decide) (by decide)
  have t014 := htriangle 0 1 4 (by decide) (by decide)
  have t023 := htriangle 0 2 3 (by decide) (by decide)
  have t024 := htriangle 0 2 4 (by decide) (by decide)
  have t034 := htriangle 0 3 4 (by decide) (by decide)
  have t123 := htriangle 1 2 3 (by decide) (by decide)
  have t124 := htriangle 1 2 4 (by decide) (by decide)
  have t134 := htriangle 1 3 4 (by decide) (by decide)
  have t234 := htriangle 2 3 4 (by decide) (by decide)
  unfold sumPairs
  cases h0 : parity 0 <;> cases h1 : parity 1 <;> cases h2 : parity 2 <;>
    cases h3 : parity 3 <;> cases h4 : parity 4 <;>
    simp [h0, h1, h2, h3, h4] at c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 t012 t013 t014 t023 t024 t034 t123 t124 t134 t234 <;> linarith

/-- Five binary words in eight dimensions cannot have minimum distance four
when their color classes distinguish even from odd distances and two
distance-four neighbors of a word must be antipodal. -/
theorem no_five_parallel_centers (word : Fin 5 → Fin 8 → Bool) (parity : Fin 5 → Bool)
    (hpair : ∀ i j, i ≠ j → 4 ≤ hammingDist (word i) (word j))
    (hsame : ∀ i j, parity i = parity j → hammingDist (word i) (word j) ≠ 5)
    (hcross : ∀ i j, parity i ≠ parity j → 5 ≤ hammingDist (word i) (word j))
    (hantipodal : ∀ i j k, j ≠ k → hammingDist (word i) (word j) = 4 →
      hammingDist (word i) (word k) = 4 → 8 ≤ hammingDist (word j) (word k)) : False := by
  let d := fun i j => hammingDist (word i) (word j)
  have hsum := hammingSum_le word
  have hlower := codeSum_ge d parity hpair hcross (fun i j k hij hjk hijp hjkp => by
    have hik : i < k := hij.trans hjk
    apply triangle_lower (hpair i j (ne_of_lt hij)) (hpair i k (ne_of_lt hik))
      (hpair j k (ne_of_lt hjk)) (hsame i j hijp) (hsame i k (hijp.trans hjkp))
      (hsame j k hjkp)
    · exact hantipodal i j k (ne_of_lt hjk)
    · intro a c
      exact hantipodal j i k (ne_of_lt hik) ((hammingDist_comm _ _).trans a) c
    · intro b c
      exact hantipodal k i j (ne_of_lt hij) ((hammingDist_comm _ _).trans b)
        ((hammingDist_comm _ _).trans c))
  exact (by decide : ¬ 50 ≤ 48) (hlower.trans hsum)

#print axioms no_five_parallel_centers

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8ParallelCenterPacking
