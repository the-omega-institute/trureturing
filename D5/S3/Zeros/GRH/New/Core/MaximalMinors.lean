/- GID: D5/S3/Zeros/GRH/New/Core/MaximalMinors
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Core/MaximalMinors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A divisibility-minimal nonzero full minor divides every right-produced determinant. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-! Determinant divisibility for rectangular matrices over a valuation domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.GRH.New.Core

open scoped BigOperators

private theorem exists_dvd_all_of_finite_total
    {O α : Type*} [CommRing O] [PreValuationRing O]
    (f : α → O) (s : Finset α) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, f a ∣ f b := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      exact ⟨a, by simp, fun b hb => by simp [Finset.mem_singleton.mp hb]⟩
  | cons a s ha hs ih =>
      obtain ⟨b, hb, hmin⟩ := ih
      rcases ValuationRing.dvd_total (f a) (f b) with hab | hba
      · refine ⟨a, by simp, ?_⟩
        intro c hc
        rcases (by simpa using hc) with rfl | hc
        · exact dvd_rfl
        · exact hab.trans (hmin c hc)
      · refine ⟨b, by simp [hb], ?_⟩
        intro c hc
        rcases (by simpa using hc) with rfl | hc
        · exact hba
        · exact hmin c hc

private theorem det_mul_expand_rows
    {O ι κ : Type*} [CommRing O] [Fintype ι] [DecidableEq ι]
    [Fintype κ] (A : Matrix ι κ O) (B : Matrix κ ι O) :
    (A * B).det =
      ∑ f : ι → κ, (∏ i, B (f i) i) *
        ((Matrix.transpose A).submatrix f id).det := by
  rw [← Matrix.det_transpose, Matrix.transpose_mul]
  let detRows : MultilinearMap O (fun _ : ι => ι → O) O :=
    Matrix.detRowAlternating.toMultilinearMap
  let row (i : ι) (k : κ) : ι → O := B k i • A.transpose k
  have hrows : B.transpose * A.transpose = Matrix.of (fun i => ∑ k, row i k) := by
    ext i j
    simp [row, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrows]
  calc
    _ = detRows (fun i => ∑ k, row i k) := rfl
    _ = ∑ f : ι → κ, detRows (fun i => row i (f i)) := detRows.map_sum row
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      calc
        _ = (∏ i, B (f i) i) • detRows (fun i => A.transpose (f i)) :=
          detRows.map_smul_univ _ _
        _ = _ := rfl

private theorem det_submatrix_eq_zero_of_not_injective
    {O ι κ : Type*} [CommRing O] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι κ O) (f : ι → κ) (hf : ¬ Function.Injective f) :
    ((Matrix.transpose A).submatrix f id).det = 0 := by
  obtain ⟨i, j, h, hij⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [Matrix.submatrix_apply, h]

/-- A divisibility-minimal nonzero full column minor divides every determinant of `A * B`. -/
theorem exists_maximal_minor_dvd_det_mul
    {O ι κ : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ O)
    (hA : ∃ s : ι ↪ κ, (A.submatrix id s).det ≠ 0) :
    ∃ s : ι ↪ κ, (A.submatrix id s).det ≠ 0 ∧ ∀ B : Matrix κ ι O,
      (A.submatrix id s).det ∣ (A * B).det := by
  classical
  let f : (ι ↪ κ) → O := fun s => (A.submatrix id s).det
  obtain ⟨s₀, hs₀⟩ := hA
  obtain ⟨s, hs, hmin⟩ := exists_dvd_all_of_finite_total f Finset.univ
    ⟨s₀, Finset.mem_univ _⟩
  refine ⟨s, ?_, ?_⟩
  · exact ne_zero_of_dvd_ne_zero hs₀ (hmin s₀ (Finset.mem_univ _))
  intro B
  rw [det_mul_expand_rows A B]
  apply Finset.dvd_sum
  intro g hg
  by_cases hgi : Function.Injective g
  · let t : ι ↪ κ := ⟨g, hgi⟩
    have hdiv : f s ∣ f t := hmin t (Finset.mem_univ _)
    have heq : ((Matrix.transpose A).submatrix g id).det = f t := by
      exact Matrix.det_transpose (A.submatrix id g)
    rw [heq]
    exact dvd_mul_of_dvd_right hdiv _
  · rw [det_submatrix_eq_zero_of_not_injective A g hgi, mul_zero]
    exact dvd_zero _

end D5.S3.Zeros.GRH.New.Core
