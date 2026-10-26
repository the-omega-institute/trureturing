/- GID: D5/S3/Quantum/Information/SLDSpectralEnergy
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/SLDSpectralEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Density matrices and the spectral energy of Hermitian symmetric logarithmic derivatives. -/

import D5.S3.Quantum.Information.ActualPureQubitGeometry

noncomputable section
open Matrix Finset
open scoped ComplexOrder

namespace D5.S3.Quantum.Information.SLDSpectralEnergy
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

/-- A positive semidefinite matrix of trace one. -/
def IsDensity {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ trace ρ = 1

/-- The SLD energy in a specified diagonal basis, including zero eigenvalues. -/
theorem diagonal_energy {n : Type*} [Fintype n] [DecidableEq n]
    (w : n → ℝ) (B L : Matrix n n ℂ) (hL : L.IsHermitian)
    (hsolve : L * diagonal (fun i => (w i : ℂ)) +
      diagonal (fun i => (w i : ℂ)) * L = (2 : ℂ) • B) :
    (L * diagonal (fun i => (w i : ℂ)) * L).trace.re =
      ∑ i, ∑ j, 2 * Complex.normSq (B i j) / (w i + w j) := by
  classical
  let d : n → ℂ := fun i => (w i : ℂ)
  have hentry (i j : n) : L i j * (d i + d j) = 2 * B i j := by
    have he := congrArg (fun X : Matrix n n ℂ => X i j) hsolve
    simp only [Matrix.add_apply, mul_diagonal, diagonal_mul, Matrix.smul_apply,
      smul_eq_mul] at he
    change L i j * d j + d i * L i j = 2 * B i j at he
    linear_combination he
  have hterm (i j : n) :
      2 * Complex.normSq (B i j) /
        (w i + w j) =
      (w i + w j) / 2 *
        Complex.normSq (L i j) := by
    have he := hentry i j
    have hm : B i j = ((d i + d j) / 2) * L i j := by linear_combination -he / 2
    rw [hm, map_mul]
    have hd : (d i + d j) / 2 =
        (((w i + w j) / 2 : ℝ) : ℂ) := by
      simp [d]
    rw [hd, Complex.normSq_ofReal]
    by_cases hz : w i + w j = 0
    · simp [hz]
    · field_simp
      <;> ring
  have heSum : (L * diagonal d * L).trace.re =
      ∑ i, ∑ j, w j * Complex.normSq (L i j) := by
    simp only [Matrix.trace, Matrix.diag]
    simp only [Matrix.mul_apply (M := L * diagonal d) (N := L), mul_diagonal, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hn : L j i = star (L i j) := by simpa using (hL.apply j i).symm
    rw [hn]
    have : L i j * d j * star (L i j) = d j * (Complex.normSq (L i j) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      change _ = d j * (star (L i j) * L i j)
      ring
    rw [this]
    simp [d]
  have hswap : (∑ i, ∑ j, w i * Complex.normSq (L i j)) =
      ∑ i, ∑ j, w j * Complex.normSq (L i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← hL.apply i j]
    simp only [Complex.star_def, Complex.normSq_conj]
  rw [heSum]
  simp_rw [hterm, add_div, add_mul]
  simp only [Finset.sum_add_distrib, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [hswap]
  ring

/-- Every Hermitian solution of the SLD equation has the spectral QFI energy. -/
theorem spectral_energy {n : Type*} [Fintype n] [DecidableEq n]
    (rho B L : Matrix n n ℂ) (hp : rho.PosSemidef)
    (hL : L.IsHermitian) (hsolve : L * rho + rho * L = (2 : ℂ) • B) :
    (L * rho * L).trace.re = spectralQFI rho B hp := by
  classical
  let U := hp.isHermitian.eigenvectorUnitary
  let w := hp.isHermitian.eigenvalues
  let d : n → ℂ := fun i => (w i : ℂ)
  let M := star (U : Matrix n n ℂ) * B * U
  let N := star (U : Matrix n n ℂ) * L * U
  have hs : rho = (U : Matrix n n ℂ) * diagonal d * star (U : Matrix n n ℂ) := by
    simpa [U, w, d, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hp.isHermitian.spectral_theorem
  have hN : N.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul _ hL
  have hu : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := U.property.1
  have hu' : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := U.property.2
  have hdiag : star (U : Matrix n n ℂ) * rho * (U : Matrix n n ℂ) = diagonal d := by
    rw [hs]
    simp only [← Matrix.mul_assoc, hu, one_mul]
    simp only [Matrix.mul_assoc, hu, mul_one]
  have hsolveN : N * diagonal d + diagonal d * N = (2 : ℂ) • M := by
    have he := congrArg (fun X : Matrix n n ℂ =>
      star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) hsolve
    rw [← hdiag]
    dsimp only [N, M]
    simpa only [mul_add, add_mul, Matrix.mul_assoc, ← mul_assoc (U : Matrix n n ℂ),
      hu', one_mul, Matrix.mul_smul, Matrix.smul_mul] using he
  have heTrace : (L * rho * L).trace = (N * diagonal d * N).trace := by
    rw [← hdiag]
    dsimp only [N]
    simp only [Matrix.mul_assoc, ← mul_assoc (U : Matrix n n ℂ), hu', one_mul]
    rw [trace_mul_comm (star (U : Matrix n n ℂ))]
    simp only [Matrix.mul_assoc, hu', mul_one]
  rw [heTrace]
  exact diagonal_energy w M N hN hsolveN

end D5.S3.Quantum.Information.SLDSpectralEnergy
