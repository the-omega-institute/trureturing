/- GID: D5/S3/Quantum/Measurement/FactorWidth/FiveCyclePosteriorFactorWidth
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/FactorWidth/FiveCyclePosteriorFactorWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The five-cycle posterior moment has complex factor width exactly three. -/

/-
admission_basis: escape-witness
escape_witness: grouped_integer_gram gives a signed cyclic Gram identity whose nonedge terms cancel.
The width-three construction consumes this identity after rescaling the vectors.
proof_shape: cycle_moment_width_exactly_three: content
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31522
-/

import D5.S3.Quantum.Measurement.FactorWidthTwoCone
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Quantum.Measurement.FactorWidth.FiveCyclePosteriorFactorWidth

private def consecutive (s i : Fin 5) : ℤ :=
  if i = s then 1 else if i = s + 1 then 2 else if i = s + 2 then 1 else 0

private def split (s i : Fin 5) : ℤ :=
  if i = s then 2 else if i = s + 1 then 2 else if i = s + 3 then -1 else 0

private def adjacency (i j : Fin 5) : ℤ :=
  if j = i + 1 ∨ i = j + 1 then 1 else 0

private def diagonal (i j : Fin 5) : ℤ :=
  if i = j then 1 else 0

private theorem grouped_integer_gram :
    ∀ i j : Fin 5,
      12 * (∑ s : Fin 5, consecutive s i * consecutive s j) +
        3 * (∑ s : Fin 5, split s i * split s j) + diagonal i j =
      20 * (5 * diagonal i j + 3 * adjacency i j) := by
  decide

private theorem consecutive_sparse :
    ∀ s : Fin 5, (Finset.univ.filter fun i => consecutive s i ≠ 0).card ≤ 3 := by
  decide

private theorem split_sparse :
    ∀ s : Fin 5, (Finset.univ.filter fun i => split s i ≠ 0).card ≤ 3 := by
  decide



open Matrix Finset
open D5.S3.Quantum.Measurement

noncomputable section

/-- The rational five-cycle moment at the uniform prior. -/
def moment : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (5 * (diagonal i j : ℝ) + 3 * (adjacency i j : ℝ)) / 55

private theorem coordinate_sparse (s : Fin 5) :
    (Finset.univ.filter fun i => diagonal s i ≠ 0).card ≤ 3 :=
  (show ∀ s : Fin 5, (Finset.univ.filter fun i => diagonal s i ≠ 0).card ≤ 3 by decide) s

private theorem coordinate_gram :
    ∀ i j : Fin 5, (∑ s : Fin 5, diagonal s i * diagonal s j) = diagonal i j := by
  decide

private theorem scaled_sum (a : ℝ) (ha : 0 ≤ a) (f : Fin 5 → Fin 5 → ℤ) (i j : Fin 5) :
    (∑ s, (Real.sqrt a * (f s i : ℝ)) * (Real.sqrt a * (f s j : ℝ))) =
      a * (∑ s, ((f s i : ℝ) * (f s j : ℝ))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = (Real.sqrt a) ^ 2 * ((f s i : ℝ) * (f s j : ℝ)) := by ring
    _ = _ := by rw [Real.sq_sqrt ha]

private theorem scaled_sparse (a : ℝ) (f : Fin 5 → ℤ)
    (hf : (Finset.univ.filter fun i => f i ≠ 0).card ≤ 3) :
    FactorWidthTwoCone.IsKSparse 3 (fun i => ((a * (f i : ℝ) : ℝ) : ℂ)) := by
  classical
  unfold FactorWidthTwoCone.IsKSparse
  apply (Finset.card_le_card ?_).trans hf
  intro i hi
  obtain ⟨_, hi⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hz => hi (by simp [hz])⟩

private theorem width_three :
    FactorWidthTwoCone.IsKIncoherentSum 3 (moment.map Complex.ofReal) := by
  classical
  let Index := Fin 5 ⊕ (Fin 5 ⊕ Fin 5)
  let factor : Index → Fin 5 → ℝ := Sum.elim
    (fun s i => Real.sqrt (12 / 1100) * (consecutive s i : ℝ))
    (Sum.elim (fun s i => Real.sqrt (3 / 1100) * (split s i : ℝ))
      (fun s i => Real.sqrt (1 / 1100) * (diagonal s i : ℝ)))
  let e := Fintype.equivFin Index
  have hsparse (z : Index) : FactorWidthTwoCone.IsKSparse 3
      (fun i => (factor z i : ℂ)) := by
    rcases z with s | (s | s)
    · exact scaled_sparse _ _ (consecutive_sparse s)
    · exact scaled_sparse _ _ (split_sparse s)
    · exact scaled_sparse _ _ (coordinate_sparse s)
  refine ⟨Fintype.card Index, fun t i => (factor (e.symm t) i : ℂ),
    fun t => hsparse (e.symm t), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  apply congrArg Complex.ofReal
  rw [Equiv.sum_comp e.symm (fun z => factor z i * factor z j), Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  change moment i j =
    (∑ s, (Real.sqrt (12 / 1100) * (consecutive s i : ℝ)) *
      (Real.sqrt (12 / 1100) * (consecutive s j : ℝ))) +
    ((∑ s, (Real.sqrt (3 / 1100) * (split s i : ℝ)) *
      (Real.sqrt (3 / 1100) * (split s j : ℝ))) +
    (∑ s, (Real.sqrt (1 / 1100) * (diagonal s i : ℝ)) *
      (Real.sqrt (1 / 1100) * (diagonal s j : ℝ))))
  rw [scaled_sum _ (by norm_num), scaled_sum _ (by norm_num), scaled_sum _ (by norm_num)]
  have hcoord :
      (∑ s : Fin 5, (diagonal s i : ℝ) * (diagonal s j : ℝ)) = (diagonal i j : ℝ) := by
    exact_mod_cast coordinate_gram i j
  rw [hcoord]
  have hcertificate :
      12 * (∑ s : Fin 5, (consecutive s i : ℝ) * (consecutive s j : ℝ)) +
        3 * (∑ s : Fin 5, (split s i : ℝ) * (split s j : ℝ)) + (diagonal i j : ℝ) =
      20 * (5 * (diagonal i j : ℝ) + 3 * (adjacency i j : ℝ)) := by
    exact_mod_cast grouped_integer_gram i j
  unfold moment
  linarith

private theorem successor_pair_unique :
    ∀ i j : Fin 5, j ∈ ({i, i + 1} : Finset (Fin 5)) →
      j + 1 ∈ ({i, i + 1} : Finset (Fin 5)) → j = i := by
  decide

private theorem two_sparse_cycle_bound (v : Fin 5 → ℂ)
    (hv : FactorWidthTwoCone.IsKSparse 2 v) :
    2 * (∑ i : Fin 5, (v i * star (v (i + 1))).re) ≤
      ∑ i : Fin 5, Complex.normSq (v i) := by
  classical
  let support := Finset.univ.filter fun i => v i ≠ 0
  have hmem (i : Fin 5) : i ∈ support ↔ v i ≠ 0 := by simp [support]
  by_cases hedge : ∃ i : Fin 5, v i ≠ 0 ∧ v (i + 1) ≠ 0
  · obtain ⟨i, hi, hj⟩ := hedge
    have diff : ∀ i : Fin 5, i ≠ i + 1 := by decide
    have hpair : ({i, i + 1} : Finset (Fin 5)) ⊆ support :=
      Finset.insert_subset ((hmem i).2 hi) (Finset.singleton_subset_iff.mpr ((hmem _).2 hj))
    have hs : ({i, i + 1} : Finset (Fin 5)) = support := by
      apply Finset.eq_of_subset_of_card_le hpair
      simpa [diff i, support, FactorWidthTwoCone.IsKSparse] using hv
    have hcross :
        (∑ j : Fin 5, (v j * star (v (j + 1))).re) = (v i * star (v (i + 1))).re := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_cases hj : v j = 0
        · simp [hj]
        · by_cases hstep : v (j + 1) = 0
          · simp [hstep]
          · exfalso
            apply hji
            exact successor_pair_unique i j (hs ▸ ((hmem _).2 hj)) (hs ▸ ((hmem _).2 hstep))
      · simp
    rw [hcross]
    calc
      _ ≤ Complex.normSq (v i) + Complex.normSq (v (i + 1)) := by
        have h := Complex.normSq_nonneg (v i - v (i + 1))
        rw [Complex.normSq_sub] at h
        simpa only [Complex.star_def] using sub_nonneg.mp h
      _ = ∑ j ∈ ({i, i + 1} : Finset (Fin 5)), Complex.normSq (v j) :=
        by rw [Finset.sum_pair (diff i)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => Complex.normSq_nonneg (v j))
  · have hcross : (∑ i : Fin 5, (v i * star (v (i + 1))).re) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : v i = 0
      · simp [hi]
      · have hj : v (i + 1) = 0 := Classical.byContradiction fun hj => hedge ⟨i, hi, hj⟩
        simp [hj]
    rw [hcross, mul_zero]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i)

private theorem not_width_two :
    ¬ FactorWidthTwoCone.IsKIncoherentSum 2 (moment.map Complex.ofReal) := by
  rintro ⟨m, v, hSparse, hMatrix⟩
  have hEntry (i j : Fin 5) : moment i j = ∑ t, (v t i * star (v t j)).re := by
    have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => (M i j).re) hMatrix
    simpa only [Matrix.map_apply, Complex.ofReal_re, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.re_sum] using h
  have hDiag (i : Fin 5) : moment i i = ∑ t, Complex.normSq (v t i) := by
    rw [hEntry]
    apply Finset.sum_congr rfl
    intro t _
    simp [Complex.mul_conj]
  have hsum : 2 * (∑ i : Fin 5, moment i (i + 1)) ≤ ∑ i : Fin 5, moment i i := by
    simp only [hDiag, hEntry]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 5))), Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 5)))]
    exact Finset.sum_le_sum (fun t _ => two_sparse_cycle_bound (v t) (hSparse t))
  have hdiag : ∀ i : Fin 5, diagonal i i = 1 ∧ adjacency i i = 0 := by decide
  have hedge : ∀ i : Fin 5, diagonal i (i + 1) = 0 ∧ adjacency i (i + 1) = 1 := by decide
  simp only [moment, (hdiag _).1, (hdiag _).2, (hedge _).1, (hedge _).2] at hsum
  norm_num at hsum

/-- The centered-positive five-cycle moment has complex factor width exactly three. -/
theorem cycle_moment_width_exactly_three :
    FactorWidthTwoCone.IsKIncoherentSum 3 (moment.map Complex.ofReal) ∧
      ¬ FactorWidthTwoCone.IsKIncoherentSum 2 (moment.map Complex.ofReal) :=
  ⟨width_three, not_width_two⟩

end

end D5.S3.Quantum.Measurement.FactorWidth.FiveCyclePosteriorFactorWidth
