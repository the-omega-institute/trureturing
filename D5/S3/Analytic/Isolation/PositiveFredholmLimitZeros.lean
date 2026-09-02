/- GID: D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros
   generality: G
   mirror-B: D5/B/S3/Analytic/Isolation/PositiveFredholmLimitZeros
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive spectral determinant limits have only nonpositive real zeros. -/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

open Filter Set
open scoped BigOperators ComplexOrder Topology

namespace D5.S3.Analytic.Isolation.PositiveFredholmLimitZeros

/-- The determinant of the identity plus a scalar multiple of a positive semidefinite
complex matrix factors over its nonnegative real eigenvalues. -/
theorem positive_matrix_det_factorization
    {rank : ℕ} (A : Matrix (Fin rank) (Fin rank) ℂ)
    (hA : A.PosSemidef) (w : ℂ) :
    Matrix.det (1 + w • A) =
      ∏ j, (1 + w * (hA.1.eigenvalues j : ℂ)) := by
  classical
  conv_lhs => rw [hA.1.spectral_theorem]
  let U := hA.1.eigenvectorUnitary
  let D : Matrix (Fin rank) (Fin rank) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hA.1.eigenvalues)
  change Matrix.det (1 + w • Unitary.conjStarAlgAut ℂ _ U D) = _
  have hconj : 1 + w • Unitary.conjStarAlgAut ℂ _ U D =
      Unitary.conjStarAlgAut ℂ _ U (1 + w • D) := by
    rw [map_add, map_one, map_smul]
  rw [hconj, Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  have hdet : Matrix.det (U : Matrix (Fin rank) (Fin rank) ℂ) *
      Matrix.det (star (U : Matrix (Fin rank) (Fin rank) ℂ)) = 1 := by
    rw [← Matrix.det_mul]
    have hunit : (U : Matrix (Fin rank) (Fin rank) ℂ) *
        star (U : Matrix (Fin rank) (Fin rank) ℂ) = 1 :=
      Unitary.mul_star_self_of_mem U.prop
    rw [hunit, Matrix.det_one]
  calc
    Matrix.det (U : Matrix (Fin rank) (Fin rank) ℂ) * Matrix.det (1 + w • D) *
          Matrix.det (star (U : Matrix (Fin rank) (Fin rank) ℂ)) =
        (Matrix.det (U : Matrix (Fin rank) (Fin rank) ℂ) *
          Matrix.det (star (U : Matrix (Fin rank) (Fin rank) ℂ))) *
          Matrix.det (1 + w • D) := by ring
    _ = Matrix.det (1 + w • D) := by rw [hdet, one_mul]
    _ = ∏ j, (1 + w * (hA.1.eigenvalues j : ℂ)) := by
      have hdiag : 1 + w • D = Matrix.diagonal
          (fun j => 1 + w * (hA.1.eigenvalues j : ℂ)) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [D]
        · simp [D, hij]
      rw [hdiag, Matrix.det_diagonal]

/-- A compact-uniform limit of determinants of finite-rank positive operators cannot
acquire a zero away from the nonpositive real axis. -/
theorem positive_fredholm_limit_zeros
    (rank : ℕ → ℕ)
    (A : (N : ℕ) → Matrix (Fin (rank N)) (Fin (rank N)) ℂ)
    (hA : ∀ N, (A N).PosSemidef)
    (F : ℂ → ℂ)
    (hlimit : TendstoLocallyUniformly
      (fun N w => Matrix.det (1 + w • A N)) F atTop)
    (hF0 : F 0 = 1) :
    ∀ w, F w = 0 → w.im = 0 ∧ w.re ≤ 0 := by
  let eigenvalue : (N : ℕ) → Fin (rank N) → ℝ :=
    fun N => (hA N).1.eigenvalues
  have hpositive (N : ℕ) (j : Fin (rank N)) : 0 ≤ eigenvalue N j := by
    exact (hA N).eigenvalues_nonneg j
  have hfamily :
      (fun N w => Matrix.det (1 + w • A N)) =
        (fun N w => ∏ j, (1 + w * (eigenvalue N j : ℂ))) := by
    funext N w
    simpa [eigenvalue] using positive_matrix_det_factorization (A N) (hA N) w
  rw [hfamily] at hlimit
  intro w hw
  by_cases hwzero : w = 0
  · subst w
    exact (one_ne_zero (hF0.symm.trans hw)).elim
  have hpoint (z : ℂ) :
      Tendsto (fun N => ∏ j, (1 + z * (eigenvalue N j : ℂ))) atTop (𝓝 (F z)) :=
    (tendstoLocallyUniformlyOn_univ.mpr hlimit).tendsto_at (mem_univ z)
  by_cases him : w.im = 0
  · refine ⟨him, ?_⟩
    by_contra hre
    have hwre : 0 < w.re := lt_of_not_ge hre
    have hfactor (N : ℕ) (j : Fin (rank N)) :
        1 ≤ ‖1 + w * (eigenvalue N j : ℂ)‖ := by
      have hreal : w = (w.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using him
      rw [hreal]
      rw [show 1 + (w.re : ℂ) * (eigenvalue N j : ℂ) =
          ((1 + w.re * eigenvalue N j : ℝ) : ℂ) by norm_num]
      rw [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg]
      · nlinarith [hpositive N j]
      · nlinarith [hpositive N j]
    have hprod (N : ℕ) :
        1 ≤ ‖∏ j, (1 + w * (eigenvalue N j : ℂ))‖ := by
      rw [norm_prod]
      exact Finset.one_le_prod (fun j (_ : j ∈ Finset.univ) => hfactor N j)
    have hlim := (hpoint w).norm
    have hnorm : 1 ≤ ‖F w‖ :=
      ge_of_tendsto hlim (Eventually.of_forall fun N => hprod N)
    rw [hw, norm_zero] at hnorm
    norm_num at hnorm
  · have himabs : 0 < |w.im| := abs_pos.mpr him
    let δ : ℝ := 1 / (2 * (|w.re| + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let t : ℝ := 2 * |w.re| + 1 / (|w.im| * δ ^ 2)
    have ht : 0 ≤ t := by
      dsimp [t]
      positivity
    have ht_two : 2 * |w.re| ≤ t := by
      dsimp [t]
      exact le_add_of_nonneg_right (by positivity)
    have ht_delta : 1 ≤ |w.im| * t * δ ^ 2 := by
      have hδne : δ ≠ 0 := ne_of_gt hδ
      have hinv : 1 / (|w.im| * δ ^ 2) ≤ t := by
        dsimp [t]
        exact le_add_of_nonneg_left (by positivity)
      calc
        1 = |w.im| * (1 / (|w.im| * δ ^ 2)) * δ ^ 2 := by field_simp
        _ ≤ |w.im| * t * δ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinv (abs_nonneg _)) (sq_nonneg δ)
    have hfactor (N : ℕ) (j : Fin (rank N)) :
        1 ≤ ‖1 + w * (eigenvalue N j : ℂ)‖ * (1 + t * eigenvalue N j) := by
      let lam := eigenvalue N j
      have hlam : 0 ≤ lam := hpositive N j
      have hsecond : 0 ≤ 1 + t * lam := by positivity
      by_cases hsmall : lam ≤ δ
      · have hδbound : |w.re| * δ ≤ 1 / 2 := by
          dsimp [δ]
          have habs : 0 ≤ |w.re| := abs_nonneg _
          have hden : 0 < |w.re| + 1 := by positivity
          field_simp
          nlinarith
        have hrehalf : 1 / 2 ≤ 1 + w.re * lam := by
          have hrealneg : -|w.re| ≤ w.re := neg_abs_le _
          have habslam : |w.re| * lam ≤ |w.re| * δ :=
            mul_le_mul_of_nonneg_left hsmall (abs_nonneg _)
          nlinarith
        have hcore : 0 ≤ t * (1 + w.re * lam) + w.re := by
          have htre : |w.re| ≤ t / 2 := by nlinarith
          have hwlower : -|w.re| ≤ w.re := neg_abs_le _
          nlinarith
        have hrealprod : 1 ≤ (1 + w.re * lam) * (1 + t * lam) := by
          nlinarith
        have hrenorm : 1 + w.re * lam ≤ ‖1 + w * (lam : ℂ)‖ := by
          calc
            1 + w.re * lam = (1 + w * (lam : ℂ)).re := by simp [lam]
            _ ≤ |(1 + w * (lam : ℂ)).re| := le_abs_self _
            _ ≤ ‖1 + w * (lam : ℂ)‖ := Complex.abs_re_le_norm _
        exact hrealprod.trans
          (mul_le_mul_of_nonneg_right hrenorm hsecond)
      · have hlarge : δ < lam := lt_of_not_ge hsmall
        have himnorm : |w.im| * lam ≤ ‖1 + w * (lam : ℂ)‖ := by
          calc
            |w.im| * lam = |(1 + w * (lam : ℂ)).im| := by
              simp [abs_mul, abs_of_nonneg hlam]
            _ ≤ ‖1 + w * (lam : ℂ)‖ := Complex.abs_im_le_norm _
        have htpart : t * lam ≤ 1 + t * lam := by linarith
        have hone : 1 ≤ (|w.im| * lam) * (t * lam) := by
          have hsquare : δ ^ 2 ≤ lam ^ 2 := by nlinarith
          nlinarith
        calc
          1 ≤ (|w.im| * lam) * (t * lam) := hone
          _ ≤ ‖1 + w * (lam : ℂ)‖ * (1 + t * lam) :=
            mul_le_mul himnorm htpart (by positivity) (norm_nonneg _)
    have hprod (N : ℕ) :
        1 ≤ ‖∏ j, (1 + w * (eigenvalue N j : ℂ))‖ *
          ‖∏ j, (1 + (t : ℂ) * (eigenvalue N j : ℂ))‖ := by
      have hp : 1 ≤ ∏ j, (‖1 + w * (eigenvalue N j : ℂ)‖ *
          (1 + t * eigenvalue N j)) :=
        Finset.one_le_prod (fun j (_ : j ∈ Finset.univ) => hfactor N j)
      have htfactor (j : Fin (rank N)) :
          ‖1 + (t : ℂ) * (eigenvalue N j : ℂ)‖ = 1 + t * eigenvalue N j := by
        rw [show 1 + (t : ℂ) * (eigenvalue N j : ℂ) =
            ((1 + t * eigenvalue N j : ℝ) : ℂ) by norm_num]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        nlinarith [ht, hpositive N j]
      rw [norm_prod, norm_prod]
      simp_rw [htfactor]
      rw [← Finset.prod_mul_distrib]
      exact hp
    let M : ℝ := ‖F (t : ℂ)‖ + 1
    have htbound : ∀ᶠ N in atTop,
        ‖∏ j, (1 + (t : ℂ) * (eigenvalue N j : ℂ))‖ ≤ M := by
      have hclose : ∀ᶠ N in atTop,
          dist (∏ j, (1 + (t : ℂ) * (eigenvalue N j : ℂ))) (F (t : ℂ)) < 1 :=
        eventually_atTop.2 ((Metric.tendsto_atTop.1 (hpoint (t : ℂ))) 1 zero_lt_one)
      filter_upwards [hclose] with N hN
      dsimp [M]
      calc
        ‖∏ j, (1 + (t : ℂ) * (eigenvalue N j : ℂ))‖ =
            dist (∏ j, (1 + (t : ℂ) * (eigenvalue N j : ℂ))) 0 := by rw [dist_zero_right]
        _ ≤ dist (∏ j, (1 + (t : ℂ) * (eigenvalue N j : ℂ))) (F (t : ℂ)) +
            dist (F (t : ℂ)) 0 := dist_triangle _ _ _
        _ ≤ ‖F (t : ℂ)‖ + 1 := by rw [dist_zero_right]; linarith
    have hbounded : ∀ᶠ N in atTop,
        1 ≤ ‖∏ j, (1 + w * (eigenvalue N j : ℂ))‖ * M := by
      filter_upwards [htbound] with N hN
      exact (hprod N).trans
        (mul_le_mul_of_nonneg_left hN (norm_nonneg _))
    have hlimM : Tendsto
        (fun N => ‖∏ j, (1 + w * (eigenvalue N j : ℂ))‖ * M)
        atTop (𝓝 (‖F w‖ * M)) := (hpoint w).norm.mul_const M
    have hfinal : 1 ≤ ‖F w‖ * M := ge_of_tendsto hlimM hbounded
    rw [hw, norm_zero, zero_mul] at hfinal
    norm_num at hfinal

#print axioms positive_matrix_det_factorization
#print axioms positive_fredholm_limit_zeros

end D5.S3.Analytic.Isolation.PositiveFredholmLimitZeros
