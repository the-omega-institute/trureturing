/- GID: D5/S3/Quantum/Information/QuantumFisherPositivity
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/QuantumFisherPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-dimensional Hermitian Fisher matrices have nonnegative real quadratic forms. -/

/- The escape registrations for both public declarations remain open in issue #27072. -/

import D5.S3.Quantum.Matrix.MatrixSelfPairing
import D5.S3.Weil.ZetaLinear.RankTrace

noncomputable section
open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace D5.S3.Quantum.Information.QuantumFisherPositivity

private def sldCombination {ι d : Type*} [Fintype ι]
    (a : ι → ℝ) (L : ι → Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ i, (a i : ℂ) • L i

private theorem hermitian_sld_energy_nonneg {d : Type*} [Fintype d] [DecidableEq d]
    (rho L : Matrix d d ℂ) (hRho : rho.PosSemidef) (hL : L.IsHermitian) :
    0 ≤ (L * rho * L).trace.re := by
  have hGram : (Lᴴ * L).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self L
  have h := RHLinalg.trace_mul_nonneg_of_posSemidef hRho hGram
  have hCycle : (rho * (Lᴴ * L)).trace = (L * rho * Lᴴ).trace := by
    rw [← Matrix.mul_assoc]
    exact Matrix.trace_mul_cycle rho Lᴴ L
  rw [hCycle] at h
  have hLstar : Lᴴ = L := by
    simpa only [Matrix.star_eq_conjTranspose] using hL.star_eq
  rw [hLstar] at h
  exact h

private theorem sld_combination_isHermitian {ι d : Type*} [Fintype ι]
    (a : ι → ℝ) (L : ι → Matrix d d ℂ)
    (hL : ∀ i, (L i).IsHermitian) :
    (sldCombination a L).IsHermitian := by
  unfold sldCombination
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    map_sum, map_smul, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro k hk
  simpa [Complex.real_smul, Matrix.smul_apply, Complex.star_def] using
    congrArg (fun z : ℂ => (a k : ℂ) * z) ((hL k).apply i j)

/- The finite-dimensional parameter-index form of the Fisher positivity claim. -/
theorem quantum_fisher_quadratic_nonneg {ι d : Type*} [Fintype ι] [Fintype d]
    [DecidableEq d] (rho : Matrix d d ℂ) (a : ι → ℝ)
    (L : ι → Matrix d d ℂ) (hTrace : Matrix.trace rho = 1)
    (hRho : rho.PosSemidef)
    (hL : ∀ i, (L i).IsHermitian) :
    0 ≤ ∑ i, ∑ j, a i * (Matrix.trace (rho * L i * L j)).re * a j := by
  let A := sldCombination a L
  have hA : A.IsHermitian := sld_combination_isHermitian a L hL
  have hEnergy : 0 ≤ (A * rho * A).trace.re :=
    hermitian_sld_energy_nonneg rho A hRho hA
  have hCycle : (A * rho * A).trace = (rho * A * A).trace := by
    exact (Matrix.trace_mul_cycle rho A A).symm
  have hExpand :
      ∑ i, ∑ j, a i * (Matrix.trace (rho * L i * L j)).re * a j =
        (rho * A * A).trace.re := by
    dsimp [A, sldCombination]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_sum,
      Complex.smul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hExpand]
  rw [← hCycle]
  exact hEnergy

/- A real Jacobian acts by substituting the transformed coefficient vector. -/
theorem quantum_fisher_congruence_quadratic_nonneg {ι d κ : Type*}
    [Fintype ι] [Fintype d] [Fintype κ] [DecidableEq d]
    (rho : Matrix d d ℂ) (b : κ → ℝ) (L : ι → Matrix d d ℂ)
    (T : Matrix ι κ ℝ) (hTrace : Matrix.trace rho = 1)
    (hRho : rho.PosSemidef) (hL : ∀ i, (L i).IsHermitian) :
    0 ≤ ∑ i, ∑ j, b i *
      (∑ p, ∑ q, T p i * (Matrix.trace (rho * L p * L q)).re * T q j) * b j := by
  let M : κ → Matrix d d ℂ := fun i => sldCombination (fun p => T p i) L
  have hM : ∀ i, (M i).IsHermitian := by
    intro i
    exact sld_combination_isHermitian (fun p => T p i) L hL
  have hBase := quantum_fisher_quadratic_nonneg rho b M hTrace hRho hM
  have hExpand :
      (∑ i, ∑ j, b i *
        (∑ p, ∑ q, T p i * (Matrix.trace (rho * L p * L q)).re * T q j) * b j) =
        ∑ i, ∑ j, b i * (Matrix.trace (rho * M i * M j)).re * b j := by
    dsimp [M, sldCombination]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_sum,
      Complex.smul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hExpand]
  exact hBase

end D5.S3.Quantum.Information.QuantumFisherPositivity
