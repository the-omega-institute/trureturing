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
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! A uniform mass gap for the four source Bloch bands. -/

noncomputable section

open Matrix Complex
open scoped ComplexConjugate

namespace D5.S3.SpectralTopology.HalfFluxHofstadterMassGap

private theorem phase_conj (k : ℝ) :
    conj (exp (2 * I * k)) = exp (-(2 * I * k)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, conj_I, conj_ofReal]
  ring

/-- The source Bloch Hamiltonian, including its overall minus sign, with `d = 2 + m`. -/
def bloch (k₁ k₂ m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let d : ℂ := ((2 + m : ℝ) : ℂ);
  -!![d, 1 - I * exp (2 * I * k₁), 1 - I * exp (2 * I * k₂), 0;
      1 + I * exp (-2 * I * k₁), 0, 0, -I + exp (2 * I * k₂);
      1 + I * exp (-2 * I * k₂), 0, 0, 1 + I * exp (2 * I * k₁);
      0, I + exp (-2 * I * k₂), 1 - I * exp (-2 * I * k₁), -d]

theorem bloch_isHermitian (k₁ k₂ m : ℝ) : (bloch k₁ k₂ m).IsHermitian := by
  have hc (k : ℝ) : conj (exp (-(2 * I * k))) = exp (2 * I * k) := by
    rw [← phase_conj, conj_conj]
  change (bloch k₁ k₂ m)ᴴ = bloch k₁ k₂ m
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bloch, Matrix.conjTranspose_apply, phase_conj, hc, neg_mul] <;> ring

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
  rw [Complex.norm_exp]
  simp

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
  simp only [offDiagonal, Complex.normSq_apply, div_re, div_im, mul_re, mul_im,
    sub_re, sub_im, add_re, add_im, one_re, one_im, I_re, I_im,
    re_ofNat, im_ofNat]
  norm_num
  linear_combination (z₂.re ^ 2 - 2 * z₂.re + z₂.im ^ 2 + 1) / 2 * hz₁ +
    (z₁.re + 1) * hz₂

private theorem schur_det (z₁ z₂ : ℂ) (d : ℝ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    (schur z₁ z₂ d).det = -(gapPolynomial z₁.im z₂.im d : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [schur, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
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
  rw [ha.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp only [RHLinalg.posIndex, Function.comp_def, RCLike.ofReal_re,
    Complex.ofReal_re, Multiset.filter_map, Multiset.card_map]
  rfl

private def shifted (k₁ k₂ m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  bloch k₁ k₂ m + (-2 : ℂ) • 1

private theorem shifted_isHermitian (k₁ k₂ m : ℝ) :
    (shifted k₁ k₂ m).IsHermitian :=
  (bloch_isHermitian k₁ k₂ m).add
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
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    norm_num [blockMatrix, shifted, bloch, reorder, coupling, finSumFinEquiv,
      Equiv.swap_apply_def, Matrix.reindex_apply, Matrix.conjTranspose_apply,
      phase_conj, neg_mul] <;> ring

private theorem schur_eq (z₁ z₂ : ℂ) (d : ℝ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    diagonal ![-(d : ℂ) - 2, (d : ℂ) - 2] +
      (1 / 2 : ℂ) • (coupling z₁ z₂ * (coupling z₁ z₂)ᴴ) = schur z₁ z₂ d := by
  have hz₁ : z₁.re ^ 2 + z₁.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, ← sq] using (Complex.sq_norm z₁).symm.trans (by rw [h₁]; norm_num)
  have hz₂ : z₂.re ^ 2 + z₂.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, ← sq] using (Complex.sq_norm z₂).symm.trans (by rw [h₂]; norm_num)
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [coupling, schur, offDiagonal,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [hz₁, hz₂]

private def eliminator (z₁ z₂ : ℂ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  fromBlocks 1 0 ((1 / 2 : ℂ) • (coupling z₁ z₂)ᴴ) 1

private theorem eliminator_det (z₁ z₂ : ℂ) : (eliminator z₁ z₂).det = 1 := by
  simp [eliminator, Matrix.det_fromBlocks_zero₁₂]

private theorem schur_congruence (k₁ k₂ m : ℝ) :
    let z₁ := exp (2 * I * k₁)
    let z₂ := exp (2 * I * k₂)
    (eliminator z₁ z₂)ᴴ * blockMatrix k₁ k₂ m * eliminator z₁ z₂ =
      fromBlocks (schur z₁ z₂ (2 + m)) 0 0
        ((-2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  dsimp only
  rw [blockMatrix_eq]
  simp only [eliminator, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, map_div₀, map_one, map_ofNat,
    Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← add_smul]
  norm_num
  rw [schur_eq _ _ _ (phase_norm k₁) (phase_norm k₂)]

private theorem fermi_bands :
    band (Real.pi / 4) (Real.pi / 4) 0 2 = 2 ∧
      band (Real.pi / 4) (Real.pi / 4) 0 3 = 2 := by
  sorry

private theorem band_signs (k₁ k₂ m : ℝ)
    (hm₁ : -2 ≤ m) (hm₂ : m ≤ 2) (hm : m ≠ 0) :
    band k₁ k₂ m 2 < 2 ∧ 2 < band k₁ k₂ m 3 := by
  sorry

private theorem band_distance (k₁ k₂ m : ℝ)
    (hm₁ : -2 ≤ m) (hm₂ : m ≤ 2) (j : Fin 4) :
    m ^ 2 / 500 ≤ |band k₁ k₂ m j - 2| := by
  sorry

theorem result : claim := by
  have hf : fermiEnergy = 2 := fermi_bands.1
  refine ⟨fermi_bands.2.trans hf.symm, ?_⟩
  intro m hm₁ hm₂ hm
  refine ⟨m ^ 2 / 500, div_pos (sq_pos_of_ne_zero hm) (by norm_num), ?_⟩
  intro k₁ k₂
  obtain ⟨hlo, hhi⟩ := band_signs k₁ k₂ m hm₁ hm₂ hm
  have h₃ := band_distance k₁ k₂ m hm₁ hm₂ 3
  have h₂ := band_distance k₁ k₂ m hm₁ hm₂ 2
  rw [abs_of_pos (sub_pos.mpr hhi)] at h₃
  rw [abs_of_neg (sub_neg.mpr hlo)] at h₂
  rw [hf]
  constructor <;> linarith

end D5.S3.SpectralTopology.HalfFluxHofstadterMassGap
