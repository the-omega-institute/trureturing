/- GID: D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two complementary translated fourteen-cycles force ten u-visits. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationAveraging

open Finset

/-- The visits at which the distinguished port is used by the base cycle. -/
def uCount {V : Type*} [Fintype V] (trans : V → V → V)
    (sigma : V → Fin 3) (c : Fin 14 → V) (e : Fin 14 → Fin 3) (h : V) : ℕ :=
  ∑ i, if sigma (trans h (c i)) ≠ e i then 1 else 0

private def localCount (e : Fin 14 → Fin 3) (j : Fin 3) : ℕ :=
  ∑ i, if j ≠ e i then 1 else 0

private theorem complement_count (e : Fin 14 → Fin 3) (j : Fin 3) :
    localCount e j + (∑ i, if e i = j then 1 else 0 : ℕ) = 14 := by
  rw [localCount, ← sum_add_distrib]
  have heach (i : Fin 14) :
      (if j ≠ e i then 1 else 0 : ℕ) + (if e i = j then 1 else 0) = 1 := by
    by_cases h : j = e i
    · simp [h]
    · have hh : e i ≠ j := Ne.symm h
      simp [h, hh]
  simp_rw [heach]
  simp

private theorem translated_sum {V : Type*} [Fintype V]
    (trans : V → V → V) (htrans : ∀ v, Function.Bijective (fun h => trans h v))
    (sigma : V → Fin 3) (c : Fin 14 → V) (e : Fin 14 → Fin 3) :
    (∑ h, uCount trans sigma c e h) = ∑ v, localCount e (sigma v) := by
  unfold uCount localCount
  rw [sum_comm]
  calc
    _ = ∑ i : Fin 14, ∑ v : V, if sigma v ≠ e i then 1 else 0 := by
      apply sum_congr rfl
      intro i hi
      exact Fintype.sum_bijective (fun h => trans h (c i)) (htrans (c i))
        (fun h => if sigma (trans h (c i)) ≠ e i then 1 else 0)
        (fun v => if sigma v ≠ e i then 1 else 0) (fun _ => rfl)
    _ = _ := sum_comm

/-- The unused-edge distributions (6,4,4) and (2,6,6) cannot both have at
most nine distinguished-port visits at every translate. Only bijectivity of
translation in its first coordinate is needed. -/
theorem exists_many_u {V : Type*} [Fintype V]
    (trans : V → V → V) (htrans : ∀ v, Function.Bijective (fun h => trans h v))
    (hpos : 0 < Fintype.card V) (sigma : V → Fin 3)
    (c4 c6 : Fin 14 → V) (e4 e6 : Fin 14 → Fin 3)
    (h4 : ∀ j : Fin 3, (∑ i, if e4 i = j then 1 else 0 : ℕ) =
      if j = 0 then 6 else 4)
    (h6 : ∀ j : Fin 3, (∑ i, if e6 i = j then 1 else 0 : ℕ) =
      if j = 0 then 2 else 6) :
    ∃ h : V, 10 ≤ uCount trans sigma c4 e4 h ∨
      10 ≤ uCount trans sigma c6 e6 h := by
  have hlocal (j : Fin 3) : 2 * localCount e4 j + localCount e6 j = 28 := by
    have hc4 := complement_count e4 j
    have hc6 := complement_count e6 j
    rw [h4] at hc4
    rw [h6] at hc6
    by_cases h : j = 0
    · simp only [if_pos h] at hc4 hc6
      omega
    · simp only [if_neg h] at hc4 hc6
      omega
  have total : 2 * (∑ h, uCount trans sigma c4 e4 h) +
      (∑ h, uCount trans sigma c6 e6 h) = 28 * Fintype.card V := by
    rw [translated_sum trans htrans, translated_sum trans htrans,
      mul_sum, ← sum_add_distrib]
    simp_rw [hlocal]
    simp [Nat.mul_comm]
  by_contra hnone
  push Not at hnone
  have bound4 : (∑ h, uCount trans sigma c4 e4 h) ≤ 9 * Fintype.card V := by
    calc
      _ ≤ ∑ _h : V, 9 := sum_le_sum (fun h _ => by have hh := (hnone h).1; omega)
      _ = _ := by simp [Nat.mul_comm]
  have bound6 : (∑ h, uCount trans sigma c6 e6 h) ≤ 9 * Fintype.card V := by
    calc
      _ ≤ ∑ _h : V, 9 := sum_le_sum (fun h _ => by have hh := (hnone h).2; omega)
      _ = _ := by simp [Nat.mul_comm]
  omega

end D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationAveraging
