/- GID: D5/S3/SpectralTopology/HalfFluxHofstadterMassGap
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/HalfFluxHofstadterMassGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The nonzero mass Hofstadter bands have a uniform gap at the Fermi energy. -/

import D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
import D5.S3.SpectralTopology.PointGapExactInertia
import D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIISLnUnipotentCommutators

/-! A uniform mass gap for the four source Bloch bands. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Complex
open NikolovSegal.PartIISLnUnipotentCommutators (lowerBlock)
open scoped ComplexConjugate

namespace D5.S3.SpectralTopology.HalfFluxHofstadterMassGap

private theorem phase_conj (k : ℝ) :
    conj (exp (2 * I * k)) = exp (-(2 * I * k)) := by
  simpa only [map_mul, map_ofNat, conj_I, conj_ofReal, mul_neg, neg_mul]
    using (Complex.exp_conj (2 * I * k)).symm

private theorem phase_conj_neg (k : ℝ) :
    conj (exp (-(2 * I * k))) = exp (2 * I * k) := by
  rw [← phase_conj, conj_conj]

/-- The source Bloch Hamiltonian, including its overall minus sign, with `d = 2 + m`. -/
def bloch (k₁ k₂ m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let d : ℂ := ((2 + m : ℝ) : ℂ);
  -!![d, 1 - I * exp (2 * I * k₁), 1 - I * exp (2 * I * k₂), 0;
      1 + I * exp (-2 * I * k₁), 0, 0, -I + exp (2 * I * k₂);
      1 + I * exp (-2 * I * k₂), 0, 0, 1 + I * exp (2 * I * k₁);
      0, I + exp (-2 * I * k₂), 1 - I * exp (-2 * I * k₁), -d]

theorem bloch_isHermitian (k₁ k₂ m : ℝ) : (bloch k₁ k₂ m).IsHermitian := by
  change (bloch k₁ k₂ m)ᴴ = bloch k₁ k₂ m
  rw [bloch.eq_1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bloch, Matrix.conjTranspose_apply, phase_conj, phase_conj_neg, neg_mul] <;> ring

/-- `band k₁ k₂ m j` is the source's `λ_{j+1}`, in increasing order with multiplicity. -/
def band (k₁ k₂ m : ℝ) (j : Fin 4) : ℝ :=
  (bloch_isHermitian k₁ k₂ m).eigenvalues₀ j.rev

/-- The source's Fermi energy `μ = λ₃(π/4, π/4; 0)`. -/
def fermiEnergy : ℝ := band (Real.pi / 4) (Real.pi / 4) 0 2

def claim : Prop :=
  band (Real.pi / 4) (Real.pi / 4) 0 3 = fermiEnergy ∧
    ∀ m : ℝ, -2 ≤ m → m ≤ 2 → m ≠ 0 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ k₁ k₂ : ℝ,
        fermiEnergy + δ ≤ band k₁ k₂ m 3 ∧
          band k₁ k₂ m 2 ≤ fermiEnergy - δ

private def gapPolynomial (y₁ y₂ d : ℝ) : ℝ :=
  (y₁ - d) ^ 2 + (y₂ - d) ^ 2 + 2 - d ^ 2

private theorem gapPolynomial_lower (y₁ y₂ m : ℝ)
    (hy₁ : y₁ ≤ 1) (hy₂ : y₂ ≤ 1) (hm₁ : -2 ≤ m) :
    m ^ 2 / 2 ≤ gapPolynomial y₁ y₂ (2 + m) := by
  unfold gapPolynomial
  by_cases hd : 2 + m ≤ 1
  · nlinarith [sq_nonneg (y₁ - (2 + m)), sq_nonneg (y₂ - (2 + m))]
  · have h₁ : (1 - (2 + m)) ^ 2 ≤ (y₁ - (2 + m)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy₁) (show 0 ≤ 2 + m - 1 by linarith)]
    have h₂ : (1 - (2 + m)) ^ 2 ≤ (y₂ - (2 + m)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy₂) (show 0 ≤ 2 + m - 1 by linarith)]
    nlinarith [sq_nonneg m]

private theorem phase_norm (k : ℝ) : ‖exp (2 * I * k)‖ = 1 := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_assoc, mul_comm, mul_left_comm]
    using Complex.norm_exp_I_mul_ofReal (2 * k)

private def coupling (z₁ z₂ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1 + I * z₁, -1 + I * z₂; -I - conj z₂, -1 + I * conj z₁]

private def offDiagonal (z₁ z₂ : ℂ) : ℂ :=
  (1 - I) * (1 - z₁ + z₂ + z₁ * z₂) / 2

private def schur (z₁ z₂ : ℂ) (d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((z₁.im + z₂.im - d : ℝ) : ℂ), offDiagonal z₁ z₂;
      conj (offDiagonal z₁ z₂), ((d - (z₁.im + z₂.im) : ℝ) : ℂ)]

private theorem offDiagonal_normSq (z₁ z₂ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    normSq (offDiagonal z₁ z₂) = 2 * (1 - z₁.im * z₂.im) := by
  have hz₁ : z₁.re ^ 2 + z₁.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, ← sq] using (Complex.sq_norm z₁).symm.trans (by rw [h₁]; norm_num)
  have hz₂ : z₂.re ^ 2 + z₂.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, ← sq] using (Complex.sq_norm z₂).symm.trans (by rw [h₂]; norm_num)
  rw [offDiagonal.eq_1]
  simp only [Complex.normSq_apply, div_re, div_im, mul_re, mul_im,
    sub_re, sub_im, add_re, add_im, one_re, one_im, I_re, I_im,
    re_ofNat, im_ofNat]
  norm_num
  linear_combination (z₂.re ^ 2 - 2 * z₂.re + z₂.im ^ 2 + 1) / 2 * hz₁ +
    (z₁.re + 1) * hz₂

private theorem schur_det (z₁ z₂ : ℂ) (d : ℝ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    (schur z₁ z₂ d).det = -(gapPolynomial z₁.im z₂.im d : ℂ) := by
  rw [schur.eq_1, Matrix.det_fin_two]
  simp only [ Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [Complex.mul_conj]
  rw [offDiagonal_normSq z₁ z₂ h₁ h₂]
  push_cast
  unfold gapPolynomial
  push_cast
  ring

private theorem positive_roots_count {n : Type*} [Fintype n] [DecidableEq n]
    {a : Matrix n n ℂ} (ha : a.IsHermitian) :
    RHLinalg.posIndex ha =
      ((a.charpoly.roots.map Complex.re).filter (fun x => 0 < x)).card := by
  classical
  unfold RHLinalg.posIndex
  rw [ha.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp only [Function.comp_def, Multiset.filter_map, Multiset.card_map]
  rfl

private def shifted (k₁ k₂ m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  bloch k₁ k₂ m + (-2 : ℂ) • 1

private theorem shifted_isHermitian (k₁ k₂ m : ℝ) :
    (shifted k₁ k₂ m).IsHermitian := by
  rw [shifted.eq_1]
  exact (bloch_isHermitian k₁ k₂ m).add
    (Matrix.isHermitian_one.smul (IsSelfAdjoint.natCast 2).neg)

private def reorder : Equiv.Perm (Fin 4) :=
  (Equiv.swap 1 3).trans (Equiv.swap 2 3)

private def blockMatrix (k₁ k₂ m : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  (shifted k₁ k₂ m).reindex reorder reorder |>.reindex
    finSumFinEquiv.symm finSumFinEquiv.symm

private theorem blockMatrix_eq (k₁ k₂ m : ℝ) :
    blockMatrix k₁ k₂ m =
      fromBlocks (diagonal ![-((2 + m : ℝ) : ℂ) - 2, ((2 + m : ℝ) : ℂ) - 2])
        (coupling (exp (2 * I * k₁)) (exp (2 * I * k₂)))
        (coupling (exp (2 * I * k₁)) (exp (2 * I * k₂)))ᴴ
        ((-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [blockMatrix.eq_1, reorder.eq_1]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    norm_num [blockMatrix, shifted, bloch, reorder, coupling, finSumFinEquiv,
      Equiv.swap_apply_def, Matrix.reindex_apply, Matrix.conjTranspose_apply,
      phase_conj, phase_conj_neg, neg_mul] <;> ring

private theorem schur_eq (z₁ z₂ : ℂ) (d : ℝ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    diagonal ![-(d : ℂ) - 2, (d : ℂ) - 2] +
      (1 / 2 : ℂ) • (coupling z₁ z₂ * (coupling z₁ z₂)ᴴ) = schur z₁ z₂ d := by
  have hz₁ : z₁.re ^ 2 + z₁.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, ← sq] using (Complex.sq_norm z₁).symm.trans (by rw [h₁]; norm_num)
  have hz₂ : z₂.re ^ 2 + z₂.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, ← sq] using (Complex.sq_norm z₂).symm.trans (by rw [h₂]; norm_num)
  rw [coupling.eq_1]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [coupling, schur, offDiagonal,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im, map_ofNat] <;>
    nlinarith [hz₁, hz₂]

private theorem schur_congruence (k₁ k₂ m : ℝ) :
    let z₁ := exp (2 * I * k₁)
    let z₂ := exp (2 * I * k₂)
    (lowerBlock ((1 / 2 : ℂ) • (coupling z₁ z₂)ᴴ)).valᴴ * blockMatrix k₁ k₂ m *
        (lowerBlock ((1 / 2 : ℂ) • (coupling z₁ z₂)ᴴ)).val =
      fromBlocks (schur z₁ z₂ (2 + m)) 0 0
        ((-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  dsimp only
  rw [blockMatrix_eq]
  simp only [lowerBlock, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num
  have hs := schur_eq _ _ (2 + m) (phase_norm k₁) (phase_norm k₂)
  norm_num at hs
  exact hs

private theorem shifted_det (k₁ k₂ m : ℝ) :
    (shifted k₁ k₂ m).det =
      -4 * (gapPolynomial (exp (2 * I * k₁)).im (exp (2 * I * k₂)).im (2 + m) : ℂ) := by
  have h := congrArg Matrix.det (schur_congruence k₁ k₂ m)
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, SpecialLinearGroup.det_coe,
    star_one, one_mul, mul_one, Matrix.det_fromBlocks_zero₁₂,
    schur_det _ _ _ (phase_norm k₁) (phase_norm k₂), Matrix.det_smul,
    Fintype.card_fin, Matrix.det_one, blockMatrix, Matrix.det_reindex_self] at h
  norm_num at h
  rw [h]
  ring

private theorem gap_positive (k₁ k₂ m : ℝ) (hm₁ : -2 ≤ m) (hm : m ≠ 0) :
    0 < gapPolynomial (exp (2 * I * k₁)).im (exp (2 * I * k₂)).im (2 + m) := by
  have hy (k : ℝ) : (exp (2 * I * k)).im ≤ 1 :=
    (Complex.im_le_norm _).trans_eq (phase_norm k)
  exact lt_of_lt_of_le (div_pos (sq_pos_of_ne_zero hm) (by norm_num))
    (gapPolynomial_lower _ _ m (hy k₁) (hy k₂) hm₁)

private theorem shifted_band (k₁ k₂ m : ℝ) (j : Fin 4) :
    (shifted_isHermitian k₁ k₂ m).eigenvalues₀ j.rev = band k₁ k₂ m j - 2 := by
  rw [band.eq_1]
  simpa only [ sub_eq_add_neg, Complex.ofReal_neg, Complex.ofReal_ofNat] using
    D5.S3.Quantum.Matrix.LinGProperty.eigenvalues_zero_add_scalar
      (bloch k₁ k₂ m) (bloch_isHermitian k₁ k₂ m) (-2)
      (by simpa only [shifted, Complex.ofReal_neg, Complex.ofReal_ofNat] using
        shifted_isHermitian k₁ k₂ m) j.rev

private theorem schur_positive_index (z₁ z₂ : ℂ) (d : ℝ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1)
    (hq : 0 < gapPolynomial z₁.im z₂.im d)
    (ha : (fromBlocks (schur z₁ z₂ d) 0 0
      ((-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).IsHermitian) :
    RHLinalg.posIndex ha = 1 := by
  classical
  have hs : (schur z₁ z₂ d).IsHermitian := by
    change (schur z₁ z₂ d)ᴴ = schur z₁ z₂ d
    ext i j
    fin_cases i <;> fin_cases j <;> simp [schur, Matrix.conjTranspose_apply]
  have he := hs.det_eq_prod_eigenvalues.symm.trans (schur_det z₁ z₂ d h₁ h₂)
  have hn : hs.eigenvalues 0 * hs.eigenvalues 1 < 0 := by
    have hr := congrArg Complex.re he
    simp only [Fin.prod_univ_two, RCLike.ofReal_eq_complex_ofReal,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.neg_re] at hr
    linarith
  have ht : ((-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = diagonal ![-2, -2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hp : (fromBlocks (schur z₁ z₂ d) 0 0
      ((-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).charpoly =
      (({(hs.eigenvalues 0 : ℂ), (hs.eigenvalues 1 : ℂ), -2, -2} : Multiset ℂ).map
        (fun z => Polynomial.X - Polynomial.C z)).prod := by
    rw [Matrix.charpoly_fromBlocks_zero₁₂, hs.charpoly_eq, ht, Matrix.charpoly_diagonal]
    simp [Fin.prod_univ_two, mul_assoc]
  rw [positive_roots_count ha, hp, Polynomial.roots_multiset_prod_X_sub_C]
  rcases mul_neg_iff.mp hn with h | h
  · simp [h.1, not_lt_of_ge h.2.le]
  · simp [h.2, not_lt_of_ge h.1.le]

private theorem shifted_inertia (k₁ k₂ m : ℝ) (hm₁ : -2 ≤ m) (hm : m ≠ 0) :
    RHLinalg.posIndex (A := shifted k₁ k₂ m) (shifted_isHermitian k₁ k₂ m) = 1 ∧
      RHLinalg.negIndex (A := shifted k₁ k₂ m) (shifted_isHermitian k₁ k₂ m) = 3 := by
  classical
  have hq := gap_positive k₁ k₂ m hm₁ hm
  have ha : (blockMatrix k₁ k₂ m).IsHermitian := by
    unfold blockMatrix
    apply Matrix.IsHermitian.reindex
    exact (shifted_isHermitian k₁ k₂ m).reindex reorder
  let e := lowerBlock ((1 / 2 : ℂ) •
    (coupling (exp (2 * I * k₁)) (exp (2 * I * k₂)))ᴴ)
  have hp := Matrix.isHermitian_conjTranspose_mul_mul e.val ha
  have he := schur_congruence k₁ k₂ m
  dsimp only at he
  have hd : (fromBlocks (schur (exp (2 * I * k₁)) (exp (2 * I * k₂)) (2 + m)) 0 0
      ((-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).IsHermitian := by
    rw [← he]
    exact hp
  have hc := schur_positive_index _ _ (2 + m) (phase_norm k₁) (phase_norm k₂) hq hd
  have hi := D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback.inertia_invariant_of_isUnit_det
    ha e.val (by rw [e.det_coe]; exact isUnit_one)
  have hc' : RHLinalg.posIndex hp = 1 := by
    rw [positive_roots_count hp, he, ← positive_roots_count hd]
    exact hc
  have hp₁ : RHLinalg.posIndex (shifted_isHermitian k₁ k₂ m) = 1 := by
    have hsame : RHLinalg.posIndex (shifted_isHermitian k₁ k₂ m) =
        RHLinalg.posIndex ha := by
      rw [positive_roots_count, positive_roots_count]
      simp only [blockMatrix, Matrix.charpoly_reindex]
    exact hsame.trans (hi.1.symm.trans hc')
  have hu : IsUnit (shifted k₁ k₂ m).det := by
    rw [shifted_det, isUnit_iff_ne_zero]
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hq.ne')
  have hr := Matrix.rank_of_isUnit (shifted k₁ k₂ m)
    ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  have ht := D5.S3.SpectralTopology.PointGapExactInertia.posIndex_add_negIndex_eq_rank
    (shifted_isHermitian k₁ k₂ m)
  simp only [Fintype.card_fin] at hr
  exact ⟨hp₁, by omega⟩

private theorem row_bound (k₁ k₂ m : ℝ) (hm₁ : -2 ≤ m) (hm₂ : m ≤ 2) (i : Fin 4) :
    ∑ j, ‖shifted k₁ k₂ m i j‖ ≤ 10 := by
  have hd : ‖((2 + m : ℝ) : ℂ)‖ ≤ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hd₁ : ‖-((2 + m : ℝ) : ℂ) - 2‖ ≤ 6 := by
    calc
      _ ≤ ‖-((2 + m : ℝ) : ℂ)‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ = ‖((2 + m : ℝ) : ℂ)‖ + 2 := by rw [norm_neg]; norm_num
      _ ≤ 6 := by linarith
  have hd₂ : ‖((2 + m : ℝ) : ℂ) - 2‖ ≤ 6 := by
    calc
      _ ≤ ‖((2 + m : ℝ) : ℂ)‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 6 := by simpa using (show ‖((2 + m : ℝ) : ℂ)‖ + 2 ≤ 6 by linarith)
  have hu (z : ℂ) (hz : ‖z‖ = 1) :
      ‖I * z - 1‖ ≤ 2 ∧ ‖-(I * z) + -1‖ ≤ 2 ∧ ‖-z + I‖ ≤ 2 ∧ ‖-z + -I‖ ≤ 2 := by
    have h₁ := norm_sub_le (I * z) (1 : ℂ)
    have h₂ := norm_add_le (-(I * z)) (-1)
    have h₃ := norm_add_le (-z) I
    have h₄ := norm_add_le (-z) (-I)
    simp only [norm_one, norm_mul, Complex.norm_I, hz, one_mul, norm_neg] at *
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hn (k : ℝ) : ‖exp (-2 * I * k)‖ = 1 := by
    simpa only [Complex.ofReal_neg, mul_neg, neg_mul] using phase_norm (-k)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hu _ (phase_norm k₁)
  obtain ⟨h₅, h₆, h₇, h₈⟩ := hu _ (phase_norm k₂)
  obtain ⟨h₉, h₁₀, h₁₁, h₁₂⟩ := hu _ (hn k₁)
  obtain ⟨h₁₃, h₁₄, h₁₅, h₁₆⟩ := hu _ (hn k₂)
  have hdiag : ‖-(m : ℂ) + -2 + -2‖ ≤ 6 := by
    convert hd₁ using 1
    push_cast
    congr 1
    ring
  norm_num at hd₂
  fin_cases i <;> norm_num [shifted, bloch, Fin.sum_univ_succ, Matrix.one_apply] <;>
    simp only [neg_mul] at * <;> linarith

private theorem shifted_eigenvalue_bound (k₁ k₂ m : ℝ)
    (hm₁ : -2 ≤ m) (hm₂ : m ≤ 2) (j : Fin 4) :
    |(shifted_isHermitian k₁ k₂ m).eigenvalues₀ j| ≤ 10 := by
  let h := shifted_isHermitian k₁ k₂ m
  have he : Module.End.HasEigenvalue (shifted k₁ k₂ m).toLin'
      (h.eigenvalues₀ j : ℂ) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rw [Matrix.spectrum_toLin']
    rw [h.spectrum_eq_image_range]
    refine ⟨h.eigenvalues (RHLinalg.eigEquiv j), ⟨RHLinalg.eigEquiv j, rfl⟩, ?_⟩
    rw [RHLinalg.eigenvalues_eigEquiv]
    rfl
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball he
  rw [mem_closedBall_iff_norm] at hi
  have hb : ‖(h.eigenvalues₀ j : ℂ)‖ ≤ ∑ l, ‖shifted k₁ k₂ m i l‖ := by
    calc
      _ ≤ ‖(h.eigenvalues₀ j : ℂ) - shifted k₁ k₂ m i i‖ +
          ‖shifted k₁ k₂ m i i‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le ((h.eigenvalues₀ j : ℂ) - shifted k₁ k₂ m i i) (shifted k₁ k₂ m i i)
      _ ≤ (∑ l ∈ Finset.univ.erase i, ‖shifted k₁ k₂ m i l‖) +
          ‖shifted k₁ k₂ m i i‖ := add_le_add hi le_rfl
      _ = _ := Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have hb' := hb.trans (row_bound k₁ k₂ m hm₁ hm₂ i)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hb'

private theorem fermi_charpoly :
    (bloch (Real.pi / 4) (Real.pi / 4) 0).charpoly =
      Polynomial.X * (Polynomial.X + 4) * (Polynomial.X - 2) ^ 2 := by
  have hp : exp (2 * I * ((Real.pi / 4 : ℝ) : ℂ)) = I := by
    convert Complex.exp_pi_div_two_mul_I using 1
    push_cast
    ring
  have hn : exp (-2 * I * ((Real.pi / 4 : ℝ) : ℂ)) = -I := by
    rw [show -2 * I * ((Real.pi / 4 : ℝ) : ℂ) =
      -(2 * I * ((Real.pi / 4 : ℝ) : ℂ)) by ring, ← phase_conj, hp]
    simp
  have hb : bloch (Real.pi / 4) (Real.pi / 4) 0 =
      !![-2, -2, -2, 0; -2, 0, 0, 0; -2, 0, 0, 0; 0, 0, 0, 2] := by
    unfold bloch
    dsimp only
    rw [hp, hn]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hb, Matrix.charpoly, Matrix.det_succ_row_zero]
  norm_num [Matrix.charmatrix_apply, Matrix.submatrix, Matrix.det_fin_three,
    Fin.sum_univ_succ, Fin.succAbove, Fin.succ, Fin.castSucc, Polynomial.C_ofNat]
  ring

private theorem fermi_bands :
    band (Real.pi / 4) (Real.pi / 4) 0 2 = 2 ∧
      band (Real.pi / 4) (Real.pi / 4) 0 3 = 2 := by
  have hr : (bloch (Real.pi / 4) (Real.pi / 4) 0).charpoly.roots =
      ({(2 : ℂ), 2, 0, -4} : Multiset ℂ) := by
    have hp : (bloch (Real.pi / 4) (Real.pi / 4) 0).charpoly =
        (({(2 : ℂ), 2, 0, -4} : Multiset ℂ).map
          (fun z => Polynomial.X - Polynomial.C z)).prod := by
      rw [fermi_charpoly]
      simp [Polynomial.C_ofNat]
      ring
    rw [hp, Polynomial.roots_multiset_prod_X_sub_C]
  have hs := Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀
    (bloch_isHermitian (Real.pi / 4) (Real.pi / 4) 0)
  rw [hr] at hs
  norm_num [Multiset.sort_cons, Multiset.sort_zero] at hs
  constructor
  · simpa [band] using hs.2.1.symm
  · simpa [band] using hs.1.symm

private theorem band_signs (k₁ k₂ m : ℝ)
    (hm₁ : -2 ≤ m) (hm : m ≠ 0) :
    band k₁ k₂ m 2 < 2 ∧ 2 < band k₁ k₂ m 3 := by
  classical
  let h := shifted_isHermitian k₁ k₂ m
  obtain ⟨hp, hn⟩ := shifted_inertia k₁ k₂ m hm₁ hm
  unfold RHLinalg.posIndex at hp
  unfold RHLinalg.negIndex at hn
  change (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card = 1 at hp
  change (Finset.univ.filter (fun i => h.eigenvalues i < 0)).card = 3 at hn
  rw [RHLinalg.card_eigenvalues_reindex h (fun x => 0 < x)] at hp
  rw [RHLinalg.card_eigenvalues_reindex h (fun x => x < 0)] at hn
  change (Finset.univ.filter (fun i : Fin 4 => h.eigenvalues₀ i < 0)).card = 3 at hn
  rw [Finset.card_filter] at hp
  have hanti := h.eigenvalues₀_antitone
  have htop : 0 < h.eigenvalues₀ 0 := by
    by_contra ht
    have hall (i : Fin 4) : ¬0 < h.eigenvalues₀ i :=
      not_lt.mpr ((hanti (Fin.zero_le i)).trans (not_lt.mp ht))
    simp only [hall, ite_false, Finset.sum_const_zero] at hp
    omega
  have hsecond : h.eigenvalues₀ 1 < 0 := by
    by_contra hs
    have hsub : (Finset.univ.filter (fun i : Fin 4 => h.eigenvalues₀ i < 0)) ⊆ {2, 3} := by
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      fin_cases i
      · exact False.elim ((not_lt_of_ge htop.le) hi')
      · exact False.elim (hs hi')
      · simp
      · simp
    have hle := Finset.card_le_card hsub
    norm_num at hle
    omega
  have hs₂ := shifted_band k₁ k₂ m 2
  have hs₃ := shifted_band k₁ k₂ m 3
  norm_num at hs₂ hs₃
  change (shifted_isHermitian k₁ k₂ m).eigenvalues₀ 1 < 0 at hsecond
  change 0 < (shifted_isHermitian k₁ k₂ m).eigenvalues₀ 0 at htop
  constructor <;> linarith

private theorem band_distance (k₁ k₂ m : ℝ)
    (hm₁ : -2 ≤ m) (hm₂ : m ≤ 2) (j : Fin 4) :
    m ^ 2 / 500 ≤ |band k₁ k₂ m j - 2| := by
  classical
  let h := shifted_isHermitian k₁ k₂ m
  have hy (k : ℝ) : (exp (2 * I * k)).im ≤ 1 :=
    (Complex.im_le_norm _).trans_eq (phase_norm k)
  have hq := gapPolynomial_lower _ _ m (hy k₁) (hy k₂) hm₁
  have hq₀ : 0 ≤ gapPolynomial (exp (2 * I * k₁)).im (exp (2 * I * k₂)).im (2 + m) :=
    (div_nonneg (sq_nonneg m) (by norm_num)).trans hq
  have hd : 2 * m ^ 2 ≤ ‖(shifted k₁ k₂ m).det‖ := by
    rw [shifted_det, norm_mul]
    norm_num only [norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq₀]
    nlinarith
  have hp : ‖(shifted k₁ k₂ m).det‖ = ∏ i : Fin 4, |h.eigenvalues₀ i| := by
    rw [h.det_eq_prod_eigenvalues, ← (RHLinalg.eigEquiv (n := Fin 4)).prod_comp]
    simp only [RHLinalg.eigenvalues_eigEquiv, norm_prod,
      RCLike.ofReal_eq_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
    rfl
  have hb : (∏ i ∈ Finset.univ.erase j.rev, |h.eigenvalues₀ i|) ≤ 1000 := by
    calc
      _ ≤ ∏ _i ∈ (Finset.univ.erase j.rev : Finset (Fin 4)), (10 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun i _ => shifted_eigenvalue_bound k₁ k₂ m hm₁ hm₂ i)
      _ = 1000 := by norm_num
  have hf := Finset.prod_erase_mul Finset.univ (fun i : Fin 4 => |h.eigenvalues₀ i|)
    (Finset.mem_univ j.rev)
  have hu : ‖(shifted k₁ k₂ m).det‖ ≤ 1000 * |h.eigenvalues₀ j.rev| := by
    rw [hp, ← hf]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hs := shifted_band k₁ k₂ m j
  change (shifted_isHermitian k₁ k₂ m).eigenvalues₀ j.rev = _ at hs
  change ‖(shifted k₁ k₂ m).det‖ ≤ 1000 *
    |(shifted_isHermitian k₁ k₂ m).eigenvalues₀ j.rev| at hu
  rw [hs] at hu
  linarith

theorem result : claim := by
  have hf : fermiEnergy = 2 := fermi_bands.1
  refine ⟨fermi_bands.2.trans hf.symm, ?_⟩
  intro m hm₁ hm₂ hm
  refine ⟨m ^ 2 / 500, div_pos (sq_pos_of_ne_zero hm) (by norm_num), ?_⟩
  intro k₁ k₂
  obtain ⟨hlo, hhi⟩ := band_signs k₁ k₂ m hm₁ hm
  have h₃ := band_distance k₁ k₂ m hm₁ hm₂ 3
  have h₂ := band_distance k₁ k₂ m hm₁ hm₂ 2
  rw [abs_of_pos (sub_pos.mpr hhi)] at h₃
  rw [abs_of_neg (sub_neg.mpr hlo)] at h₂
  rw [hf]
  constructor <;> linarith

end D5.S3.SpectralTopology.HalfFluxHofstadterMassGap
