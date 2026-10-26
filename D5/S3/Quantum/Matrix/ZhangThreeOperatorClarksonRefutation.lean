/- GID: D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.claim; result=D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.result; claim=D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.claim
   digest: Three matrices refute Zhang's three-operator Schatten inequality. -/

import D5.S3.Quantum.Schatten.Holder
import D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes
import D5.S3.Quantum.QubitWitnesses

/-! # A counterexample to the three-operator Clarkson–McCarthy conjecture

The Schatten norm is the frozen trace-functional-calculus norm. Its positive
real powers agree with sums of powers of singular values. Only the conjecture's
clause for real exponents at least two is asserted by `claim`.

Source: T. Zhang, arXiv:2410.21961v4, Conjecture `conj:sharp-inequality`.
Preregistration: https://github.com/the-omega-institute/trureturing/issues/22304
admission_basis: open-problem-resolution
-/

noncomputable section

set_option linter.style.longLine false

open Matrix
open D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes (coordinateProjectorTwo)
open D5.S3.Quantum.QubitWitnesses (equalSuperpositionDensity)
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.ZhangThreeOperatorClarksonRefutation

def claim : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∀ (n : ℕ) (a b c : Matrix (Fin n) (Fin n) ℂ),
    schattenNorm (a + b + c) p ^ p + schattenNorm a p ^ p +
      schattenNorm b p ^ p + schattenNorm c p ^ p ≤
    ((3 : ℝ) ^ (p - 1) + 1) / (2 : ℝ) ^ p *
      (schattenNorm (a + b) p ^ p + schattenNorm (b + c) p ^ p +
        schattenNorm (c + a) p ^ p)

private lemma power_of_gram_charpoly (x : Matrix (Fin 2) (Fin 2) ℂ)
    (d : Fin 2 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hc : (xᴴ * x).charpoly = (diagonal (fun i => (d i : ℂ))).charpoly)
    {p : ℝ} (hp : 0 < p) :
    schattenNorm x p ^ p = ∑ i, d i ^ (p / 2) := by
  classical
  let hg := isHermitian_mul_conjTranspose_self xᴴ
  have hh : IsHermitian (diagonal (fun i => (d i : ℂ))) := by
    apply isHermitian_diagonal_iff.mpr
    intro i
    simp [isSelfAdjoint_iff]
  have he : hg.eigenvalues = hh.eigenvalues :=
    (hg.eigenvalues_eq_eigenvalues_iff (hB := hh)).mpr (by simpa using hc)
  obtain ⟨σ, hσ⟩ := hh.eigenvalues_eq_of_unitary_similarity_diagonal
    (U := (1 : Matrix (Fin 2) (Fin 2) ℂ)) (by simp) (f := d) (by simp)
  rw [schattenNorm_rpow_eq_sum_singularValues x hp]
  calc
    _ = ∑ i, singularValues x (σ i) ^ p := (Equiv.sum_comp σ _).symm
    _ = ∑ i, d i ^ (p / 2) := by
      apply Finset.sum_congr rfl
      intro i _
      change Real.sqrt (hg.eigenvalues (σ i)) ^ p = _
      rw [he, show hh.eigenvalues (σ i) = d i from congrFun hσ i]
      exact (Real.rpow_div_two_eq_sqrt p (hd i)).symm

private lemma left_side {p : ℝ} (hp : 0 < p) :
    schattenNorm (coordinateProjectorTwo 0 + coordinateProjectorTwo 1 + -equalSuperpositionDensity) p ^ p +
      schattenNorm (coordinateProjectorTwo 0) p ^ p + schattenNorm (coordinateProjectorTwo 1) p ^ p +
      schattenNorm (-equalSuperpositionDensity) p ^ p = 4 := by
  have hd : ∀ i, 0 ≤ (![1, 0] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num
  have h (x : Matrix (Fin 2) (Fin 2) ℂ)
      (hx : (xᴴ * x).charpoly = (diagonal (fun i =>
        ((![1, 0] : Fin 2 → ℝ) i : ℂ))).charpoly) :
      schattenNorm x p ^ p = 1 := by
    rw [power_of_gram_charpoly x ![1, 0] hd hx hp]
    simp [Fin.sum_univ_two, Real.zero_rpow (by linarith : p / 2 ≠ 0)]
  have ha : schattenNorm (coordinateProjectorTwo 0) p ^ p = 1 := h (coordinateProjectorTwo 0) (by
    norm_num [charpoly_fin_two, trace_fin_two, det_fin_two, mul_apply, conjTranspose_apply,
      Fin.sum_univ_two, coordinateProjectorTwo, diagonal_apply])
  have hb : schattenNorm (coordinateProjectorTwo 1) p ^ p = 1 := h (coordinateProjectorTwo 1) (by
    norm_num [charpoly_fin_two, trace_fin_two, det_fin_two, mul_apply, conjTranspose_apply,
      Fin.sum_univ_two, coordinateProjectorTwo, diagonal_apply])
  have hc : schattenNorm (-equalSuperpositionDensity) p ^ p = 1 := h (-equalSuperpositionDensity) (by
    norm_num [charpoly_fin_two, trace_fin_two, det_fin_two, mul_apply, conjTranspose_apply,
      Fin.sum_univ_two, equalSuperpositionDensity, diagonal_apply]
    norm_num [map_ofNat, ← Polynomial.C_mul, ← Polynomial.C_add])
  have hs : schattenNorm (coordinateProjectorTwo 0 + coordinateProjectorTwo 1 + -equalSuperpositionDensity) p ^ p = 1 :=
      h (coordinateProjectorTwo 0 + coordinateProjectorTwo 1 + -equalSuperpositionDensity) (by
    norm_num [charpoly_fin_two, trace_fin_two, det_fin_two, mul_apply, conjTranspose_apply,
      Fin.sum_univ_two, coordinateProjectorTwo, equalSuperpositionDensity, diagonal_apply]
    norm_num [map_ofNat, ← Polynomial.C_mul, ← Polynomial.C_add])
  rw [ha, hb, hc, hs]
  norm_num

private lemma right_side {p : ℝ} (hp : 0 < p) :
    schattenNorm (coordinateProjectorTwo 0 + coordinateProjectorTwo 1) p ^ p +
      schattenNorm (coordinateProjectorTwo 1 + -equalSuperpositionDensity) p ^ p +
      schattenNorm (-equalSuperpositionDensity + coordinateProjectorTwo 0) p ^ p = 2 + (2 : ℝ) ^ (2 - p / 2) := by
  have hab : schattenNorm (coordinateProjectorTwo 0 + coordinateProjectorTwo 1) p ^ p = 2 := by
    rw [power_of_gram_charpoly (coordinateProjectorTwo 0 + coordinateProjectorTwo 1) (fun _ => 1)
      (by intro i; norm_num) (by
        norm_num [charpoly_fin_two, trace_fin_two, det_fin_two, mul_apply,
          conjTranspose_apply, Fin.sum_univ_two, coordinateProjectorTwo, diagonal_apply]) hp]
    norm_num [Fin.sum_univ_two]
  have h (x : Matrix (Fin 2) (Fin 2) ℂ)
      (hx : (xᴴ * x).charpoly =
        (diagonal (fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ))).charpoly) :
      schattenNorm x p ^ p = 2 * (1 / 2 : ℝ) ^ (p / 2) := by
    rw [power_of_gram_charpoly x (fun _ => 1 / 2) (by intro i; norm_num) hx hp]
    simp [two_mul]
  have hbc : schattenNorm (coordinateProjectorTwo 1 + -equalSuperpositionDensity) p ^ p =
      2 * (1 / 2 : ℝ) ^ (p / 2) := h (coordinateProjectorTwo 1 + -equalSuperpositionDensity) (by
    norm_num [charpoly_fin_two, trace_fin_two, det_fin_two, mul_apply,
      conjTranspose_apply, Fin.sum_univ_two, coordinateProjectorTwo, equalSuperpositionDensity, diagonal_apply]
    norm_num [map_ofNat, ← Polynomial.C_mul, ← Polynomial.C_add])
  have hca : schattenNorm (-equalSuperpositionDensity + coordinateProjectorTwo 0) p ^ p =
      2 * (1 / 2 : ℝ) ^ (p / 2) := h (-equalSuperpositionDensity + coordinateProjectorTwo 0) (by
    norm_num [charpoly_fin_two, trace_fin_two, det_fin_two, mul_apply,
      conjTranspose_apply, Fin.sum_univ_two, coordinateProjectorTwo, equalSuperpositionDensity, diagonal_apply]
    norm_num [map_ofNat, ← Polynomial.C_mul, ← Polynomial.C_add])
  have he : (2 : ℝ) ^ (2 - p / 2) = 4 * (1 / 2 : ℝ) ^ (p / 2) := by
    rw [Real.rpow_sub (by norm_num), Real.div_rpow (by norm_num) (by norm_num)]
    norm_num
    ring
  rw [hab, hbc, hca, he]
  ring

private lemma certified_bound :
    ((3 : ℝ) ^ ((9 / 4 : ℝ) - 1) + 1) / (2 : ℝ) ^ (9 / 4 : ℝ) *
      (2 + (2 : ℝ) ^ (2 - (9 / 4 : ℝ) / 2)) < 4 := by
  have h₃pow : ((3 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = 3 := by
    simpa using Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (4 : ℝ) ≠ 0)
  have h₂pow : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = 2 := by
    simpa using Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (4 : ℝ) ≠ 0)
  have h₇pow : ((2 : ℝ) ^ (7 / 8 : ℝ)) ^ (8 : ℝ) = 128 := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num [Real.rpow_natCast]
  have h₃ : (3 : ℝ) ^ (1 / 4 : ℝ) < 13161 / 10000 := by
    apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
      (by norm_num) (by norm_num : (0 : ℝ) < 4)).mp
    rw [h₃pow]
    norm_num
  have h₂ : (11892 / 10000 : ℝ) < (2 : ℝ) ^ (1 / 4 : ℝ) := by
    apply (Real.rpow_lt_rpow_iff (by norm_num)
      (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0 : ℝ) < 4)).mp
    rw [h₂pow]
    norm_num
  have h₇ : (2 : ℝ) ^ (7 / 8 : ℝ) < 18341 / 10000 := by
    apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
      (by norm_num) (by norm_num : (0 : ℝ) < 8)).mp
    rw [h₇pow]
    norm_num
  have hnum : (3 : ℝ) ^ ((9 / 4 : ℝ) - 1) = 3 * (3 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [show (9 / 4 : ℝ) - 1 = 1 + 1 / 4 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one]
  have hden : (2 : ℝ) ^ (9 / 4 : ℝ) = 4 * (2 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [show (9 / 4 : ℝ) = 2 + 1 / 4 by norm_num, Real.rpow_add (by norm_num)]
    norm_num
  have hexp : (2 - (9 / 4 : ℝ) / 2) = 7 / 8 := by norm_num
  rw [hnum, hden, hexp, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  calc
    (3 * (3 : ℝ) ^ (1 / 4 : ℝ) + 1) * (2 + (2 : ℝ) ^ (7 / 8 : ℝ))
        < (3 * (13161 / 10000 : ℝ) + 1) * (2 + (2 : ℝ) ^ (7 / 8 : ℝ)) :=
      mul_lt_mul_of_pos_right (by linarith) (by positivity)
    _ < (3 * (13161 / 10000 : ℝ) + 1) * (2 + 18341 / 10000) :=
      mul_lt_mul_of_pos_left (by linarith) (by norm_num)
    _ < 4 * (4 * (2 : ℝ) ^ (1 / 4 : ℝ)) := by nlinarith

theorem result : ¬ claim := by
  intro h
  have hw := h (9 / 4) (by norm_num) 2 (coordinateProjectorTwo 0) (coordinateProjectorTwo 1) (-equalSuperpositionDensity)
  rw [left_side (by norm_num), right_side (by norm_num)] at hw
  exact (not_le_of_gt certified_bound) hw

end D5.S3.Quantum.Matrix.ZhangThreeOperatorClarksonRefutation
