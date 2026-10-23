/- GID: D5/S3/Quantum/Information/FisherDiscord/Spectral
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FisherDiscord/Spectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Fisher discord has a nonnegative pair kernel for every Hermitian SLD solution. -/

import D5.S3.Quantum.Information.FisherDiscord.Defs
import D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
import Mathlib.Tactic

/-! Spectral identities for the two information quantities and their difference. -/

noncomputable section
open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Information.FisherDiscord.Spectral
open D5.S3.Quantum.Information.FisherDiscord.Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The scalar kernel in the spectral formula for Fisher discord. -/
def pairKernel (a b : ℝ) : ℝ :=
  2 * Real.sqrt (a * b) * (Real.sqrt a - Real.sqrt b) ^ 2 / (a + b)

/-- Every Hermitian SLD solution gives the same diagonal Fisher information. -/
theorem fisherSLD_diag (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (H L : Matrix n n ℂ)
    (hL : IsSLD (diagonal (fun i => (w i : ℂ))) H L) :
    fisherSLD (diagonal (fun i => (w i : ℂ))) L =
      (1 / 2) * ∑ i, ∑ j, (w i - w j) ^ 2 / (w i + w j) * Complex.normSq (H i j) := by
  have hentry (i j : n) :
      L i j * ((w i + w j : ℝ) : ℂ) =
        2 * Complex.I * ((w i - w j : ℝ) : ℂ) * H i j := by
    have he := congrArg (fun M : Matrix n n ℂ => M i j) hL.2
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.add_apply,
      diagonal_mul, mul_diagonal] at he
    push_cast
    linear_combination -2 * he
  have hterm (i j : n) :
      (w i + w j) * Complex.normSq (L i j) =
        4 * ((w i - w j) ^ 2 / (w i + w j) * Complex.normSq (H i j)) := by
    by_cases hz : w i + w j = 0
    · simp [hz]
    · have he := congrArg Complex.normSq (hentry i j)
      simp only [map_mul, Complex.normSq_ofReal, Complex.normSq_I,
        Complex.normSq_ofNat] at he
      apply (mul_right_cancel₀ hz)
      field_simp
      nlinarith [he]
  have ht : (diagonal (fun i => (w i : ℂ)) * L * L).trace.re =
      ∑ i, ∑ j, w i * Complex.normSq (L i j) := by
    simp only [Matrix.trace, Matrix.diag,
      Matrix.mul_apply (M := diagonal (fun i => (w i : ℂ)) * L) (N := L),
      diagonal_mul, Complex.re_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [← hL.1.apply j i]
    have he : (w i : ℂ) * L i j * star (L i j) =
        (w i : ℂ) * (Complex.normSq (L i j) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      change _ = (w i : ℂ) * (star (L i j) * L i j)
      ring
    rw [he]
    simp
  have hswap : (∑ i, ∑ j, w i * Complex.normSq (L i j)) =
      ∑ i, ∑ j, w j * Complex.normSq (L i j) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [← hL.1.apply i j]
    simp only [Complex.star_def, Complex.normSq_conj]
  have hsum : 2 * (∑ i, ∑ j, w i * Complex.normSq (L i j)) =
      4 * ∑ i, ∑ j, (w i - w j) ^ 2 / (w i + w j) * Complex.normSq (H i j) := by
    calc
      _ = (∑ i, ∑ j, w i * Complex.normSq (L i j)) +
          (∑ i, ∑ j, w j * Complex.normSq (L i j)) := by rw [← hswap]; ring
      _ = ∑ i, ∑ j, (w i + w j) * Complex.normSq (L i j) := by
        simp only [add_mul, sum_add_distrib]
      _ = _ := by simp_rw [hterm]; simp only [← mul_sum]
  unfold fisherSLD
  rw [ht]
  linarith

/-- Skew information in a diagonal eigenbasis. -/
theorem skewWY_diag (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (H : Matrix n n ℂ)
    (hH : H.IsHermitian) :
    skewWY (diagonal (fun i => (w i : ℂ))) H =
      (1 / 2) * ∑ i, ∑ j, (Real.sqrt (w i) - Real.sqrt (w j)) ^ 2 *
        Complex.normSq (H i j) := by
  have hs := D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.sqrt_diagonal w hw
  unfold skewWY
  rw [hs]
  have ht : ((diagonal (fun i => (Real.sqrt (w i) : ℂ)) * H -
      H * diagonal (fun i => (Real.sqrt (w i) : ℂ))) ^ 2).trace.re =
      ∑ i, ∑ j, -((Real.sqrt (w i) - Real.sqrt (w j)) ^ 2 *
        Complex.normSq (H i j)) := by
    rw [pow_two]
    simp only [Matrix.trace, Matrix.diag,
      Matrix.mul_apply (M := diagonal (fun i => (Real.sqrt (w i) : ℂ)) * H -
        H * diagonal (fun i => (Real.sqrt (w i) : ℂ)))
        (N := diagonal (fun i => (Real.sqrt (w i) : ℂ)) * H -
        H * diagonal (fun i => (Real.sqrt (w i) : ℂ))),
      Matrix.sub_apply, diagonal_mul, mul_diagonal, Complex.re_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [← hH.apply j i]
    have he : ((Real.sqrt (w i) : ℂ) * H i j - H i j * (Real.sqrt (w j) : ℂ)) *
        ((Real.sqrt (w j) : ℂ) * star (H i j) - star (H i j) * (Real.sqrt (w i) : ℂ)) =
        -((((Real.sqrt (w i) - Real.sqrt (w j)) ^ 2 : ℝ) : ℂ) *
          (Complex.normSq (H i j) : ℂ)) := by
      rw [Complex.normSq_eq_conj_mul_self]
      change _ = -((((Real.sqrt (w i) - Real.sqrt (w j)) ^ 2 : ℝ) : ℂ) *
        (star (H i j) * H i j))
      push_cast
      ring
    rw [he]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  rw [ht]
  simp only [sum_neg_distrib]
  ring

/-- Fisher discord in a diagonal eigenbasis, for every Hermitian SLD solution. -/
theorem discord_diag (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (H L : Matrix n n ℂ)
    (hH : H.IsHermitian) (hL : IsSLD (diagonal (fun i => (w i : ℂ))) H L) :
    fisherSLD (diagonal (fun i => (w i : ℂ))) L -
      skewWY (diagonal (fun i => (w i : ℂ))) H =
      (1 / 2) * ∑ i, ∑ j, pairKernel (w i) (w j) * Complex.normSq (H i j) := by
  rw [fisherSLD_diag w hw H L hL, skewWY_diag w hw H hH, ← mul_sub,
    ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [← sub_mul]
  congr 1
  unfold pairKernel
  by_cases hz : w i + w j = 0
  · have hi : w i = 0 := by linarith [hw i, hw j]
    have hj : w j = 0 := by linarith [hw i, hw j]
    simp [hi, hj]
  · rw [Real.sqrt_mul (hw i)]
    have hi := Real.sq_sqrt (hw i)
    have hj := Real.sq_sqrt (hw j)
    apply (mul_right_cancel₀ hz)
    field_simp
    nlinarith [sq_nonneg (Real.sqrt (w i) - Real.sqrt (w j))]

/-- The spectral pair kernel is nonnegative, including zero eigenvalues. -/
theorem pairKernel_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ pairKernel a b := by
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (sq_nonneg _)) (add_nonneg ha hb)

/-- Fisher discord is nonnegative for diagonal positive semidefinite matrices. -/
theorem discord_nonneg_diag (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (H L : Matrix n n ℂ)
    (hH : H.IsHermitian) (hL : IsSLD (diagonal (fun i => (w i : ℂ))) H L) :
    0 ≤ fisherSLD (diagonal (fun i => (w i : ℂ))) L -
      skewWY (diagonal (fun i => (w i : ℂ))) H := by
  rw [discord_diag w hw H L hH hL]
  exact mul_nonneg (by norm_num) (sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (pairKernel_nonneg _ _ (hw i) (hw j)) (Complex.normSq_nonneg _))

private theorem information_unitary (ρ H L : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (U : Matrix.unitaryGroup n ℂ) :
    fisherSLD ((U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ))
        ((U : Matrix n n ℂ) * L * star (U : Matrix n n ℂ)) = fisherSLD ρ L ∧
    skewWY ((U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ))
        ((U : Matrix n n ℂ) * H * star (U : Matrix n n ℂ)) = skewWY ρ H := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  have ht (M : Matrix n n ℂ) : (φ M).trace = M.trace := by
    exact Matrix.trace_units_conj (Unitary.toUnits U) M
  have hs : CFC.sqrt (φ ρ) = φ (CFC.sqrt ρ) := by
    exact (NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) φ NNReal.sqrt ρ
      (ha := hρ.nonneg)
      (hφa := (hρ.mul_mul_conjTranspose_same (U : Matrix n n ℂ)).nonneg)).symm
  constructor
  · change (1 / 4 : ℝ) * (trace (φ ρ * φ L * φ L)).re = _
    rw [← map_mul, ← map_mul, ht]
    rfl
  · change -(1 / 2 : ℝ) * (trace ((CFC.sqrt (φ ρ) * φ H -
        φ H * CFC.sqrt (φ ρ)) ^ 2)).re = _
    rw [hs, ← map_mul, ← map_mul, ← map_sub, ← map_pow, ht]
    rfl

private theorem isSLD_unitary (ρ H L : Matrix n n ℂ) (hL : IsSLD ρ H L)
    (U : Matrix.unitaryGroup n ℂ) :
    IsSLD ((U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ))
      ((U : Matrix n n ℂ) * H * star (U : Matrix n n ℂ))
      ((U : Matrix n n ℂ) * L * star (U : Matrix n n ℂ)) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  constructor
  · change star (φ L) = φ L
    rw [← map_star, hL.1.star_eq]
  · have he := congrArg φ hL.2
    change Complex.I • (φ ρ * φ H - φ H * φ ρ) =
      (1 / 2 : ℂ) • (φ L * φ ρ + φ ρ * φ L)
    simpa only [map_smul, map_sub, map_add, map_mul] using he

/-- The Fisher spectral formula for every SLD of a positive semidefinite matrix. -/
theorem fisherSLD_spectral (ρ H L : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (hL : IsSLD ρ H L) :
    fisherSLD ρ L = (1 / 2) * ∑ i, ∑ j,
      (hρ.isHermitian.eigenvalues i - hρ.isHermitian.eigenvalues j) ^ 2 /
        (hρ.isHermitian.eigenvalues i + hρ.isHermitian.eigenvalues j) *
      Complex.normSq ((star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * H *
        (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  let U := hρ.isHermitian.eigenvectorUnitary
  let w := hρ.isHermitian.eigenvalues
  have hd : star (U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ) =
      diagonal (fun i => (w i : ℂ)) := by
    simpa only [U, w, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
        hρ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hl := isSLD_unitary ρ H L hL (star U)
  have hi := (information_unitary ρ H L hρ (star U)).1
  simp only [Unitary.coe_star, star_star] at hl hi
  rw [hd] at hl hi
  rw [← hi]
  exact fisherSLD_diag w hρ.eigenvalues_nonneg _ _ hl

/-- The skew-information spectral formula for every positive semidefinite matrix. -/
theorem skewWY_spectral (ρ H : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (hH : H.IsHermitian) :
    skewWY ρ H = (1 / 2) * ∑ i, ∑ j,
      (Real.sqrt (hρ.isHermitian.eigenvalues i) -
        Real.sqrt (hρ.isHermitian.eigenvalues j)) ^ 2 *
      Complex.normSq ((star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * H *
        (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  let U := hρ.isHermitian.eigenvectorUnitary
  let w := hρ.isHermitian.eigenvalues
  have hd : star (U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ) =
      diagonal (fun i => (w i : ℂ)) := by
    simpa only [U, w, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
        hρ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hi := (information_unitary ρ H 0 hρ (star U)).2
  simp only [Unitary.coe_star, star_star] at hi
  rw [hd] at hi
  rw [← hi]
  exact skewWY_diag w hρ.eigenvalues_nonneg _
    (Matrix.isHermitian_conjTranspose_mul_mul _ hH)

/-- The nonnegative pair-kernel formula in an eigenbasis of an arbitrary state. -/
theorem discord_spectral (ρ H L : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (hH : H.IsHermitian) (hL : IsSLD ρ H L) :
    fisherSLD ρ L - skewWY ρ H = (1 / 2) * ∑ i, ∑ j,
      pairKernel (hρ.isHermitian.eigenvalues i) (hρ.isHermitian.eigenvalues j) *
      Complex.normSq ((star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * H *
        (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  let U := hρ.isHermitian.eigenvectorUnitary
  let w := hρ.isHermitian.eigenvalues
  have hd : star (U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ) =
      diagonal (fun i => (w i : ℂ)) := by
    simpa only [U, w, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
        hρ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hl := isSLD_unitary ρ H L hL (star U)
  simp only [Unitary.coe_star, star_star] at hl
  rw [hd] at hl
  have he := discord_diag w hρ.eigenvalues_nonneg _ _
    (Matrix.isHermitian_conjTranspose_mul_mul _ hH) hl
  rw [fisherSLD_diag w hρ.eigenvalues_nonneg _ _ hl,
    skewWY_diag w hρ.eigenvalues_nonneg _
      (Matrix.isHermitian_conjTranspose_mul_mul _ hH)] at he
  rw [fisherSLD_spectral ρ H L hρ hL, skewWY_spectral ρ H hρ hH]
  exact he

/-- Fisher discord is nonnegative for every positive semidefinite state. -/
theorem discord_nonneg (ρ H L : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (hH : H.IsHermitian) (hL : IsSLD ρ H L) :
    0 ≤ fisherSLD ρ L - skewWY ρ H := by
  let U := hρ.isHermitian.eigenvectorUnitary
  let w := hρ.isHermitian.eigenvalues
  have hd : star (U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ) =
      diagonal (fun i => (w i : ℂ)) := by
    simpa only [U, w, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
        hρ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hl := isSLD_unitary ρ H L hL (star U)
  simp only [Unitary.coe_star, star_star] at hl
  rw [hd] at hl
  have hn := discord_nonneg_diag w hρ.eigenvalues_nonneg _ _
    (Matrix.isHermitian_conjTranspose_mul_mul _ hH) hl
  rw [discord_diag w hρ.eigenvalues_nonneg _ _
    (Matrix.isHermitian_conjTranspose_mul_mul _ hH) hl] at hn
  rw [discord_spectral ρ H L hρ hH hL]
  exact hn

end D5.S3.Quantum.Information.FisherDiscord.Spectral
