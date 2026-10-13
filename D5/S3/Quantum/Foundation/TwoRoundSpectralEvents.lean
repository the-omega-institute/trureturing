/- GID: D5/S3/Quantum/Foundation/TwoRoundSpectralEvents
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TwoRoundSpectralEvents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular normalization and attained full spectral quantum events. -/

import D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
import Mathlib.Analysis.Matrix.Order

noncomputable section

open Matrix Unitary
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Foundation.TwoRoundSpectralEvents

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complete event interval, including singular normalization operators. -/
def EventInterval (M E : Matrix n n ℂ) : Prop :=
  E.PosSemidef ∧ (M - E).PosSemidef

/-- The positive square root expressed in the normalization's spectral basis. -/
private def spectralRoot {M : Matrix n n ℂ} (hM : M.PosSemidef) : Matrix n n ℂ :=
  hM.isHermitian.cfc Real.sqrt

private theorem conjugate_pos (U : Matrix.unitaryGroup n ℂ)
    {E : Matrix n n ℂ} (hE : E.PosSemidef) :
    (conjStarAlgAut ℂ _ U E).PosSemidef := by
  rw [conjStarAlgAut_apply]
  exact hE.mul_mul_conjTranspose_same _

private theorem diagonal_real_star (d : n → ℝ) :
    (diagonal (fun i => (d i : ℂ)))ᴴ = diagonal (fun i => (d i : ℂ)) := by
  simp [diagonal_conjTranspose]

private theorem spectralRoot_sq {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    spectralRoot hM * spectralRoot hM = M := by
  unfold spectralRoot Matrix.IsHermitian.cfc
  rw [← map_mul, diagonal_mul_diagonal]
  conv_rhs => rw [hM.isHermitian.spectral_theorem]
  congr 2
  funext i
  change (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ) *
    (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ) = (hM.isHermitian.eigenvalues i : ℂ)
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hM.eigenvalues_nonneg i)]

private theorem spectralRoot_hermitian {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (spectralRoot hM).IsHermitian := by
  unfold spectralRoot Matrix.IsHermitian.cfc
  rw [conjStarAlgAut_apply]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal_iff.mpr (fun i => by
      change IsSelfAdjoint (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ)
      simp [IsSelfAdjoint]))

private theorem spectralRoot_eq_sqrt {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    spectralRoot hM = CFC.sqrt M := by
  have hpos : (spectralRoot hM).PosSemidef := by
    unfold spectralRoot Matrix.IsHermitian.cfc
    rw [conjStarAlgAut_apply]
    apply PosSemidef.mul_mul_conjTranspose_same
    apply PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ)
    exact_mod_cast Real.sqrt_nonneg (hM.isHermitian.eigenvalues i)
  exact (CFC.sqrt_unique (spectralRoot_sq hM) hpos.nonneg).symm

private theorem zero_diag_column {E : Matrix n n ℂ} (hE : E.PosSemidef)
    {i : n} (hi : E i i = 0) (j : n) : E j i = 0 := by
  have hq : star (Pi.single i (1 : ℂ)) ⬝ᵥ E *ᵥ Pi.single i 1 = 0 := by
    simpa using hi
  have hz := (hE.dotProduct_mulVec_zero_iff _).mp hq
  simpa using congrFun hz j

private theorem diagonal_interval_factorization (d : n → ℝ) (hd : ∀ i, 0 ≤ d i)
    {E : Matrix n n ℂ} (hE : EventInterval (diagonal (fun i => (d i : ℂ))) E) :
    ∃ F : Matrix n n ℂ, EventInterval 1 F ∧
      E = diagonal (fun i => (Real.sqrt (d i) : ℂ)) * F *
        diagonal (fun i => (Real.sqrt (d i) : ℂ)) := by
  let s : n → ℝ := fun i => Real.sqrt (d i)
  let r : n → ℝ := fun i => (s i)⁻¹
  let D : Matrix n n ℂ := diagonal (fun i => (s i : ℂ))
  let J : Matrix n n ℂ := diagonal (fun i => (r i : ℂ))
  let P : Matrix n n ℂ := diagonal (fun i => if d i = 0 then 0 else 1)
  let F := J * E * J
  have hs (i : n) : s i = 0 ↔ d i = 0 := Real.sqrt_eq_zero (hd i)
  have hJ : Jᴴ = J := diagonal_real_star r
  have hF : F.PosSemidef := by
    simpa only [hJ] using hE.1.conjTranspose_mul_mul_same J
  have hzero (i : n) (hi : d i = 0) : E i i = 0 := by
    have h₁ := hE.1.diag_nonneg (i := i)
    have h₂ := hE.2.diag_nonneg (i := i)
    simp only [Matrix.sub_apply, diagonal_apply_eq, hi, Complex.ofReal_zero, zero_sub] at h₂
    exact le_antisymm (neg_nonneg.mp h₂) h₁
  have hcol (i j : n) (hi : d i = 0) : E j i = 0 :=
    zero_diag_column hE.1 (hzero i hi) j
  have hrow (i j : n) (hi : d i = 0) : E i j = 0 := by
    apply star_injective
    simpa only [star_zero] using (hE.1.isHermitian.apply j i).trans (hcol i j hi)
  have hJEJ : J * diagonal (fun i => (d i : ℂ)) * J = P := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [J, P, diagonal_mul_diagonal, diagonal_apply_eq]
      by_cases hi : d i = 0
      · simp [r, s, hi]
      · have hsi : s i ≠ 0 := fun h => hi ((hs i).mp h)
        have hdsi : d i = s i * s i := (Real.mul_self_sqrt (hd i)).symm
        simp only [hi, if_false]
        change (r i : ℂ) * (d i : ℂ) * (r i : ℂ) = 1
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
        congr 1
        dsimp [r]
        rw [hdsi]
        field_simp
    · simp [J, P, diagonal_mul_diagonal, hij]
  have hPF : (P - F).PosSemidef := by
    have h := hE.2.conjTranspose_mul_mul_same J
    simpa only [hJ, Matrix.mul_sub, Matrix.sub_mul, hJEJ] using h
  have hIP : (1 - P).PosSemidef := by
    dsimp [P]
    rw [show (1 : Matrix n n ℂ) = diagonal (fun _ => 1) from diagonal_one.symm,
      diagonal_sub]
    apply PosSemidef.diagonal
    intro i
    dsimp
    split_ifs <;> norm_num
  refine ⟨F, ⟨hF, ?_⟩, ?_⟩
  · simpa only [sub_add_sub_cancel] using hIP.add hPF
  · change E = D * F * D
    ext i j
    simp only [D, F, J, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hi : d i = 0
    · simp [s, r, hi, hrow i j hi]
    by_cases hj : d j = 0
    · simp [s, r, hj, hcol j i hj]
    have hsi : s i ≠ 0 := fun h => hi ((hs i).mp h)
    have hsj : s j ≠ 0 := fun h => hj ((hs j).mp h)
    have hci : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsi
    have hcj : (s j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsj
    simp only [r, Complex.ofReal_inv]
    field_simp

/-- Every event under a possibly singular normalization is a congruence of a full effect. -/
theorem singular_interval_factorization {M E : Matrix n n ℂ} (hM : M.PosSemidef) :
    EventInterval M E ↔ ∃ F : Matrix n n ℂ,
      EventInterval 1 F ∧ E = CFC.sqrt M * F * CFC.sqrt M := by
  classical
  rw [← spectralRoot_eq_sqrt hM]
  let U := hM.isHermitian.eigenvectorUnitary
  let a := conjStarAlgAut ℂ (Matrix n n ℂ) U
  let d : n → ℝ := hM.isHermitian.eigenvalues
  have hdiag : a.symm M = diagonal (fun i => (d i : ℂ)) := by
    rw [show M = a (diagonal (fun i => (d i : ℂ))) from
      hM.isHermitian.spectral_theorem]
    exact a.symm_apply_apply _
  have hroot : spectralRoot hM = a (diagonal (fun i => (Real.sqrt (d i) : ℂ))) := rfl
  constructor
  · intro hE
    have hE' : EventInterval (diagonal (fun i => (d i : ℂ))) (a.symm E) := by
      refine ⟨?_, ?_⟩
      · have := conjugate_pos (star U) hE.1
        simpa only [a, conjStarAlgAut_symm] using this
      · rw [← hdiag, ← map_sub]
        simpa only [a, conjStarAlgAut_symm] using conjugate_pos (star U) hE.2
    obtain ⟨F, hF, hEF⟩ := diagonal_interval_factorization d hM.eigenvalues_nonneg hE'
    refine ⟨a F, ⟨conjugate_pos U hF.1, ?_⟩, ?_⟩
    · simpa only [map_sub, map_one] using conjugate_pos U hF.2
    · have := congrArg a hEF
      simpa only [StarAlgEquiv.apply_symm_apply, map_mul, ← hroot] using this
  · rintro ⟨F, hF, rfl⟩
    have hH := (spectralRoot_hermitian hM).eq
    refine ⟨?_, ?_⟩
    · simpa only [hH] using hF.1.conjTranspose_mul_mul_same (spectralRoot hM)
    · have := hF.2.conjTranspose_mul_mul_same (spectralRoot hM)
      simpa only [hH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        spectralRoot_sq] using this

end D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
