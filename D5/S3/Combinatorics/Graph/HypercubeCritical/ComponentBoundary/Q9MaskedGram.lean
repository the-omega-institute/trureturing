/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Active row and column degrees bound the rectangular Huang Gram defect. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
import Mathlib.Analysis.Matrix.Normed

/-! The degree test bounds the two rectangular factors of the masked Huang Gram matrix. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedGram

open Matrix
open scoped BigOperators Matrix.Norms.Operator
open BalancedCriticalSpectrum (Q flip)
open Q9IsotropicHuang (flipSign weightedMatrix)

private theorem opNorm_le_of_row_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) {d : NNReal} (h : ∀ x, ∑ y, ‖M x y‖ ≤ d) : ‖M‖ ≤ d := by
  rw [Matrix.linfty_opNorm_def]
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro x _
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, coe_nnnorm] using h x

private theorem det_shift_sub_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {q : ℝ} (h : ‖A‖ < q) :
    (q • (1 : Matrix ι ι ℝ) - A).det ≠ 0 := by
  intro hdet
  obtain ⟨u, hu, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
  have hbound := Matrix.linfty_opNorm_mulVec A u
  rw [← hker, norm_smul, Real.norm_eq_abs, abs_of_pos ((norm_nonneg A).trans_lt h)] at hbound
  exact (not_le.mpr (mul_lt_mul_of_pos_right h (norm_pos_iff.mpr hu))) hbound

private theorem norm_flipSign {n : ℕ} (a : Fin n) (x : Q n) :
    ‖(flipSign a x : ℝ)‖ = 1 := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    induction a using Fin.cases with
    | zero => norm_num [flipSign]
    | succ a =>
      change ‖(((if x 0 then 1 else -1) * flipSign a (Sensitivity.π x) : ℤ) : ℝ)‖ = 1
      rw [Int.cast_mul, norm_mul, ih]
      cases x 0 <;> norm_num

/-- Restrict the integer Huang matrix to unit weights on the chosen axes and to the
given row and column vertex sets. -/
def maskedBlock (I : Finset (Fin 9)) (S T : Finset (Q 9)) : Matrix (↥S) (↥T) ℝ :=
  fun x y => (weightedMatrix (fun a => if a ∈ I then 1 else 0) x.1 y.1 : ℝ)

private theorem maskedBlock_apply (I : Finset (Fin 9)) (S T : Finset (Q 9))
    (x : ↥S) (y : ↥T) :
    maskedBlock I S T x y = ∑ a ∈ I, if flip x.1 a = y.1 then (flipSign a x.1 : ℝ) else 0 := by
  classical
  simp only [maskedBlock, weightedMatrix, Int.cast_sum]
  have hI : Finset.univ.filter (fun a : Fin 9 => a ∈ I) = I := by
    ext a
    simp
  conv_rhs => rw [← hI, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ I <;> by_cases hf : flip x.1 a = y.1 <;> simp [ha, hf]

open Classical in
private theorem sum_norm_flip_entries_le
    (I : Finset (Fin 9)) (T : Finset (Q 9)) (x : Q 9)
    (c : Fin 9 → ↥T → ℝ) (hc : ∀ a y, ‖c a y‖ = 1) :
    (∑ y : ↥T, ‖∑ a ∈ I, if flip x a = y.1 then c a y else 0‖) ≤
      ((I.filter fun a => flip x a ∈ T).card : ℝ) := by
  calc
    _ ≤ ∑ y : ↥T, ∑ a ∈ I, if flip x a = y.1 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro y _
      refine (norm_sum_le I _).trans_eq ?_
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp [hc]
    _ = _ := by
      rw [Finset.sum_comm, ← Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : flip x a ∈ T
      · let z : ↥T := ⟨flip x a, ha⟩
        rw [Finset.sum_eq_single_of_mem z (Finset.mem_univ z)]
        · simp [z, ha]
        · intro y _ hy
          exact ite_eq_right fun he => hy (Subtype.ext he.symm)
      · rw [ite_eq_right ha]
        apply Finset.sum_eq_zero
        intro y _
        apply ite_eq_right
        intro he
        exact ha (by rw [he]; exact y.property)

open Classical in
/-- If the product of the active row and column degree bounds is smaller than
the number of active axes, the shifted Gram matrix of the masked Huang block
is nonsingular. In particular, five active axes suffice for degree bounds of two. -/
theorem masked_gram_det_ne_zero (I : Finset (Fin 9)) (S T : Finset (Q 9))
    {r s : ℕ} (hr : ∀ x ∈ S, (I.filter fun a => flip x a ∈ T).card ≤ r)
    (hs : ∀ y ∈ T, (I.filter fun a => flip y a ∈ S).card ≤ s)
    (hgap : r * s < I.card) :
    let M := maskedBlock I S T
    ((I.card : ℝ) • (1 : Matrix (↥S) (↥S) ℝ) - M * Mᵀ).det ≠ 0 := by
  dsimp only
  let M := maskedBlock I S T
  have hrows : ‖M‖ ≤ (r : ℝ) := by
    apply opNorm_le_of_row_bound M (d := r)
    intro x
    simp only [M, maskedBlock_apply]
    exact (sum_norm_flip_entries_le I T x.1 _ (fun a _ => norm_flipSign a x.1)).trans
      (by exact_mod_cast hr x.1 x.property)
  have hcols : ‖Mᵀ‖ ≤ (s : ℝ) := by
    apply opNorm_le_of_row_bound Mᵀ (d := s)
    intro y
    simp only [M, Matrix.transpose_apply, maskedBlock_apply]
    have hflip (x : ↥S) (a : Fin 9) : flip x.1 a = y.1 ↔ flip y.1 a = x.1 := by
      constructor <;> intro h
      · rw [← h, BalancedCriticalSpectrum.flip_flip]
      · rw [← h, BalancedCriticalSpectrum.flip_flip]
    simp_rw [hflip]
    exact (sum_norm_flip_entries_le I S y.1 _ (fun a x => norm_flipSign a x.1)).trans
      (by exact_mod_cast hs y.1 y.property)
  apply det_shift_sub_ne_zero
  exact (Matrix.linfty_opNorm_mul _ _).trans_lt
    ((mul_le_mul hrows hcols (norm_nonneg _) (Nat.cast_nonneg _)).trans_lt
      (by exact_mod_cast hgap))

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedGram
