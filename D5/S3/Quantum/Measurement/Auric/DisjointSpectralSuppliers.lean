/- GID: D5/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Flat rectangular factors and diagonal Jensen bounds, including zero-capacity factors. -/

import D5.S3.Quantum.Measurement.Auric.ProjectiveRecord
import D5.S3.Quantum.Measurement.Auric.EqualBlockProjection
import Mathlib.Analysis.Convex.Jensen

/-! Flat factors and diagonal Jensen for spectral sums on finite complex matrices. -/

namespace D5.S3.Quantum.Measurement.Auric

open _root_.Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

open D5.S3.Quantum.Measurement.Auric.EqualBlockProjection (exists_flat_rows spectralSum spectralSum_affine)

noncomputable section

variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s] [DecidableEq s]

/-- A flat row factor with an arbitrary row capacity, including an empty row index. -/
theorem exists_flat_rows_of_rank_le {m : ℕ} {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (hr : A.rank ≤ m) :
    ∃ V : Matrix (Fin m) n ℂ, Vᴴ * V = A ∧
      ∀ p, ((V * Vᴴ) p p).re = A.trace.re / (m : ℝ) := by
  classical
  by_cases hm : 0 < m
  · exact exists_flat_rows hA hm hr
  have hm0 : m = 0 := by omega
  subst m
  have hcard : Fintype.card {i // hA.isHermitian.eigenvalues i ≠ 0} ≤ 0 := by
    rwa [← hA.isHermitian.rank_eq_card_non_zero_eigs]
  have he : hA.isHermitian.eigenvalues = 0 := by
    funext i
    change hA.isHermitian.eigenvalues i = 0
    by_contra hi
    let : Nonempty {i // hA.isHermitian.eigenvalues i ≠ 0} := ⟨⟨i, hi⟩⟩
    exact (Nat.not_lt_zero _) (Fintype.card_pos.trans_le hcard)
  have hzero := hA.isHermitian.eigenvalues_eq_zero_iff.mp he
  exact ⟨0, by simp [hzero], fun p => Fin.elim0 p⟩

/-- A Hermitian diagonal is a doubly stochastic average of its eigenvalues. -/
theorem spectral_sum_le_diagonal_of_concave {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    (he : ∀ j, hM.eigenvalues j ∈ S) :
    (∑ j, f (hM.eigenvalues j)) ≤ ∑ i, f ((M i i).re) := by
  classical
  let U : Matrix n n ℂ := hM.eigenvectorUnitary
  let w (i j : n) : ℝ := Complex.normSq (U i j)
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hM.eigenvectorUnitary.prop
  have hU'U : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.prop
  have hn (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
    rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  have hn' (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
    rw [mul_comm, hn]
  have hrow (i : n) : ∑ j, w i j = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, hn, Complex.re_sum,
      Complex.ofReal_re, Matrix.one_apply_eq, Complex.one_re, w] using
        congrArg (fun T : Matrix n n ℂ => (T i i).re) hUU
  have hcol (j : n) : ∑ i, w i j = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, hn', Complex.re_sum,
      Complex.ofReal_re, Matrix.one_apply_eq, Complex.one_re, w] using
        congrArg (fun T : Matrix n n ℂ => (T j j).re) hU'U
  have hd : M = U * diagonal (fun j => (hM.eigenvalues j : ℂ)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, U] using hM.spectral_theorem
  have hentry (i : n) : (M i i).re = ∑ j, w i j * hM.eigenvalues j := by
    calc
      (M i i).re = ((U * diagonal (fun j => (hM.eigenvalues j : ℂ)) * Uᴴ) i i).re :=
        congrArg (fun T : Matrix n n ℂ => (T i i).re) hd
      _ = _ := by
        rw [Matrix.mul_apply, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
          show (U i j * (hM.eigenvalues j : ℂ)) * star (U i j) =
            (U i j * star (U i j)) * (hM.eigenvalues j : ℂ) by ring,
          hn, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hjensen (i : n) : (∑ j, w i j * f (hM.eigenvalues j)) ≤ f ((M i i).re) := by
    rw [hentry i]
    simpa only [smul_eq_mul] using
      hf.le_map_sum (w := w i) (p := hM.eigenvalues) (t := Finset.univ)
        (fun j _ => Complex.normSq_nonneg (U i j)) (hrow i) (fun j _ => he j)
  calc
    (∑ j, f (hM.eigenvalues j)) = ∑ i, ∑ j, w i j * f (hM.eigenvalues j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, hcol, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ => hjensen i

/-- Column-Gram contraction suffices to apply diagonal Jensen to its row Gram. -/
theorem gram_spectral_sum_le_diagonal (V : Matrix s n ℂ)
    (hV : Vᴴ * V ≤ 1) {f : ℝ → ℝ} (h0 : f 0 = 0)
    (hf : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f) :
    (∑ j, f ((Matrix.isHermitian_conjTranspose_mul_self V).eigenvalues j)) ≤
      ∑ i, f (((V * Vᴴ) i i).re) := by
  let hRow := Matrix.isHermitian_mul_conjTranspose_self V
  let hCol := Matrix.isHermitian_conjTranspose_mul_self V
  have hColEig (j : n) : hCol.eigenvalues j ∈ Set.Icc (0 : ℝ) 1 :=
    D5.S3.Quantum.Measurement.Auric.EqualBlockEffects.eigenvalues_mem_unit
      (Matrix.posSemidef_conjTranspose_mul_self V) hV j
  -- The zero-preserving positive part detects precisely eigenvalues above one.
  let excess (x : ℝ) := max (x - 1) 0
  have hexcess : (∑ i, excess (hRow.eigenvalues i)) = 0 := by
    rw [spectralSum_mul_reverse excess (by norm_num [excess]) V Vᴴ hRow hCol]
    apply Finset.sum_eq_zero
    intro j _
    exact max_eq_right (sub_nonpos.mpr (hColEig j).2)
  have hRowEig (i : s) : hRow.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨Matrix.eigenvalues_self_mul_conjTranspose_nonneg V i, ?_⟩
    have hi : excess (hRow.eigenvalues i) ≤ ∑ j, excess (hRow.eigenvalues j) :=
      Finset.single_le_sum (fun j _ => le_max_right (hRow.eigenvalues j - 1) 0)
        (Finset.mem_univ i)
    rw [hexcess] at hi
    exact sub_nonpos.mp ((le_max_left _ _).trans hi)
  rw [← spectralSum_mul_reverse f h0 V Vᴴ hRow hCol]
  exact spectral_sum_le_diagonal_of_concave hRow hf hRowEig

/-- Reflect the spectral integrand across one half. -/
theorem spectral_sum_one_sub (f : ℝ → ℝ) {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (hC : (1 - M).IsHermitian) :
    (∑ i, f (hC.eigenvalues i)) = ∑ i, f (1 - hM.eigenvalues i) := by
  have hC' : (((1 : ℝ) : ℂ) • (1 : Matrix n n ℂ) + ((-1 : ℝ) : ℂ) • M).IsHermitian := by
    simpa [sub_eq_add_neg] using hC
  simpa [spectralSum, sub_eq_add_neg] using spectralSum_affine f hM 1 (-1) hC'

end

end D5.S3.Quantum.Measurement.Auric
