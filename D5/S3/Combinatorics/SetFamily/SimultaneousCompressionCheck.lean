import D5.S3.Combinatorics.SetFamily.SimultaneousCompression
import Mathlib.Tactic.NormNum

open Finset D5.S3.Combinatorics.SetFamily.SimultaneousCompression
set_option autoImplicit false

example :
    let Ω : Finset (Finset ℕ) := {∅, {0}, {1}, {2}, {0, 2}}
    let A : Finset (Finset ℕ) := {{1}}
    let w : Finset ℕ → ℝ := fun X =>
      if X = {1} then 7 else if X = {0} then 2 else if X = {0, 2} then 5 else 0
    let v : Finset ℕ → ℝ := fun X =>
      if X = {1} then 30 else if X = {0} then 13 else if X = {0, 2} then 17 else 0
    ∃ C D : Finset (Finset ℕ), CrossIntersecting C D ∧
      7 ≤ mass (marginalWeight Ω w 1) C ∧
      30 ≤ mass (marginalWeight Ω v 1) D ∧ C.Nonempty ∧ D.Nonempty := by
  dsimp only
  let Ω : Finset (Finset ℕ) := {∅, {0}, {1}, {2}, {0, 2}}
  let A : Finset (Finset ℕ) := {{1}}
  let w : Finset ℕ → ℝ := fun X =>
    if X = {1} then 7 else if X = {0} then 2 else if X = {0, 2} then 5 else 0
  let v : Finset ℕ → ℝ := fun X =>
    if X = {1} then 30 else if X = {0} then 13 else if X = {0, 2} then 17 else 0
  have onlyt : ∀ X ∈ Ω, 1 ∈ X → X = {1} := by
    intro X hX ht
    simp only [Ω, mem_insert, mem_singleton] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl <;> simp_all
  have hex : ∀ X ∈ Ω, 1 ∈ X → 0 ∉ X ∧ 2 ∉ X := by
    intro X hX ht
    rw [onlyt X hX ht]
    norm_num
  have hsh : ∀ X ∈ Ω, 1 ∈ X → shift 0 1 X ∈ Ω := by
    intro X hX ht
    rw [onlyt X hX ht]
    norm_num [shift, Ω]
  have hw : ∀ X ∈ Ω, 0 ≤ w X := by
    intro X _
    dsimp [w]
    split_ifs <;> norm_num
  have hv : ∀ X ∈ Ω, 0 ≤ v X := by
    intro X _
    dsimp [v]
    split_ifs <;> norm_num
  have hwlaw : ∀ X ∈ Ω, 1 ∈ X →
      w X = w (shift 0 1 X) + if insert 2 (shift 0 1 X) ∈ Ω then
        w (insert 2 (shift 0 1 X)) else 0 := by
    intro X hX ht
    rw [onlyt X hX ht]
    norm_num [w, shift, Ω]
  have hvlaw : ∀ X ∈ Ω, 1 ∈ X →
      v X = v (shift 0 1 X) + if insert 2 (shift 0 1 X) ∈ Ω then
        v (insert 2 (shift 0 1 X)) else 0 := by
    intro X hX ht
    rw [onlyt X hX ht]
    norm_num [v, shift, Ω]
  have hA : A ⊆ Ω := by simp [A, Ω]
  have hc : CrossIntersecting A A := by
    intro X hX Y hY hd
    have hX' : X = {1} := by simpa [A] using hX
    have hY' : Y = {1} := by simpa [A] using hY
    subst X
    subst Y
    exact (disjoint_left.mp hd) (by simp) (by simp)
  obtain ⟨C, D, _, _, hc', hw', hv', hC, hD⟩ := exists_simultaneous_compression
    Ω A A 0 1 2 hA hA (by decide) (by decide) hex hsh w v hw hv hwlaw hvlaw hc
  refine ⟨C, D, hc', ?_, ?_, hC (by simp [A]), hD (by simp [A])⟩
  · simpa [mass, w, A] using hw'
  · simpa [mass, v, A] using hv'
