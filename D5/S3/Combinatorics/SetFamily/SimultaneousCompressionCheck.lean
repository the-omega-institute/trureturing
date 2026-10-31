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
    norm_num [w, shift, Ω,
      show ({2, 0} : Finset ℕ) = {0, 2} by decide,
      show ({0, 2} : Finset ℕ) ≠ {1} by decide,
      show ({0, 2} : Finset ℕ) ≠ {0} by decide,
      show ({0, 2} : Finset ℕ) ≠ {2} by decide]
  have hvlaw : ∀ X ∈ Ω, 1 ∈ X →
      v X = v (shift 0 1 X) + if insert 2 (shift 0 1 X) ∈ Ω then
        v (insert 2 (shift 0 1 X)) else 0 := by
    intro X hX ht
    rw [onlyt X hX ht]
    norm_num [v, shift, Ω,
      show ({2, 0} : Finset ℕ) = {0, 2} by decide,
      show ({0, 2} : Finset ℕ) ≠ {1} by decide,
      show ({0, 2} : Finset ℕ) ≠ {0} by decide,
      show ({0, 2} : Finset ℕ) ≠ {2} by decide]
  have hA : A ⊆ Ω := by simp [A, Ω]
  have hc : CrossIntersecting A A := by
    intro X hX Y hY hd
    have hX' : X = {1} := by simpa [A] using hX
    have hY' : Y = {1} := by simpa [A] using hY
    subst X
    subst Y
    exact (disjoint_left.mp hd) (a := 1) (by simp) (by simp)
  obtain ⟨C, D, _, _, hc', hw', hv', hC, hD⟩ := exists_simultaneous_compression
    Ω A A 0 1 2 hA hA (by decide) (by decide) hex hsh w v hw hv hwlaw hvlaw hc
  refine ⟨C, D, hc', ?_, ?_, hC (by simp [A]), hD (by simp [A])⟩
  · simpa [mass, w, A] using hw'
  · simpa [mass, v, A] using hv'

#print axioms D5.S3.Combinatorics.SetFamily.SimultaneousCompression.exists_simultaneous_compression

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
    norm_num [w, shift, Ω,
      show ({2, 0} : Finset ℕ) = {0, 2} by decide,
      show ({0, 2} : Finset ℕ) ≠ {1} by decide,
      show ({0, 2} : Finset ℕ) ≠ {0} by decide,
      show ({0, 2} : Finset ℕ) ≠ {2} by decide]
  have hvlaw : ∀ X ∈ Ω, 1 ∈ X →
      v X = v (shift 0 1 X) + if insert 2 (shift 0 1 X) ∈ Ω then
        v (insert 2 (shift 0 1 X)) else 0 := by
    intro X hX ht
    rw [onlyt X hX ht]
    norm_num [v, shift, Ω,
      show ({2, 0} : Finset ℕ) = {0, 2} by decide,
      show ({0, 2} : Finset ℕ) ≠ {1} by decide,
      show ({0, 2} : Finset ℕ) ≠ {0} by decide,
      show ({0, 2} : Finset ℕ) ≠ {2} by decide]
  have hA : A ⊆ Ω := by simp [A, Ω]
  have hc : CrossIntersecting A A := by
    intro X hX Y hY hd
    have hX' : X = {1} := by simpa [A] using hX
    have hY' : Y = {1} := by simpa [A] using hY
    subst X
    subst Y
    exact (disjoint_left.mp hd) (a := 1) (by simp) (by simp)
  have hmall (z : Finset ℕ → ℝ) (hz : ∀ X ∈ Ω, 0 ≤ z X) :
      ∀ R, 0 ≤ marginalWeight Ω z 1 R := by
    intro R
    exact sum_nonneg fun X hX => hz X (mem_filter.mp hX).1
  let S : DeletionSystem ({1} : Finset ℕ) := {
    feasible := fun H => if 1 ∈ H then Ω else Ω.image (fun X => X.erase 1)
    leftWeight := fun H => if 1 ∈ H then w else marginalWeight Ω w 1
    rightWeight := fun H => if 1 ∈ H then v else marginalWeight Ω v 1
    terminal := fun H => 1 ∉ H
    left_nonneg := by
      intro H _ X hX
      by_cases ht : 1 ∈ H
      · simpa [ht] using hw X (by simpa [ht] using hX)
      · simpa [ht] using hmall w hw X
    right_nonneg := by
      intro H _ X hX
      by_cases ht : 1 ∈ H
      · simpa [ht] using hv X (by simpa [ht] using hX)
      · simpa [ht] using hmall v hv X
    projection := by
      intro H hH t ht
      have ht1 : t = 1 := mem_singleton.mp (hH ht)
      subst t
      simp [ht]
    left_marginal := by
      intro H hH t ht R _
      have ht1 : t = 1 := mem_singleton.mp (hH ht)
      subst t
      simp [ht]
    right_marginal := by
      intro H hH t ht R _
      have ht1 : t = 1 := mem_singleton.mp (hH ht)
      subst t
      simp [ht]
    local_move := by
      intro H _ hnt
      have ht : 1 ∈ H := not_not.mp hnt
      refine ⟨0, 1, 2, ht, by decide, by decide, ?_, ?_, ?_, ?_⟩
      · simpa [ht] using hex
      · simpa [ht] using hsh
      · simpa [ht] using hwlaw
      · simpa [ht] using hvlaw }
  obtain ⟨K, C, D, hK, hterm, _, _, hc', _, _, hw', hv', hC, hD⟩ :=
    exists_terminal_compression {1} S A A (by simpa [S] using hA)
      (by simpa [S] using hA) hc
  have hK0 : K = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx1 : x = 1 := mem_singleton.mp (hK hx)
    subst x
    exact hterm hx
  subst K
  refine ⟨C, D, hc', ?_, ?_, hC (by simp [A]), hD (by simp [A])⟩
  · simpa [S, mass, w, A] using hw'
  · simpa [S, mass, v, A] using hv'

#print axioms D5.S3.Combinatorics.SetFamily.SimultaneousCompression.exists_terminal_compression
