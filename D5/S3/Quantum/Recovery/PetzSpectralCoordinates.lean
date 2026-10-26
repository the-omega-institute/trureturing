/- GID: D5/S3/Quantum/Recovery/PetzSpectralCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzSpectralCoordinates
   mirror-E: none(waiver:full-petz-work-in-progress)
   anchors: []
   utility: none
   digest: Actual supported relative-modular coordinates reconstruct the Petz matrix. -/

/- Escape audit unfinished for newly public cfc_spectral_sum: https://github.com/the-omega-institute/trureturing/issues/19210. -/

import D5.S3.Quantum.Divergence.CanonicalChannelDPI
import D5.S3.Quantum.Recovery.ReferencePetzChannel

noncomputable section
universe u v
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

namespace D5.S3.Quantum.Recovery.PetzSpectralCoordinates

theorem cfc_spectral_sum {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (f : ℝ → ℝ) :
    cfc f H = ∑ i : n, (f (hH.eigenvalues i) : ℂ) •
      Matrix.vecMulVec (fun x => hH.eigenvectorBasis i x)
        (star (fun x => hH.eigenvectorBasis i x)) := by
  classical
  rw [hH.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  change (hH.eigenvectorUnitary : Matrix n n ℂ) *
    diagonal (Complex.ofReal ∘ f ∘ hH.eigenvalues) *
      (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ = _
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem cfc_supported_sum {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.PosSemidef) (f : ℝ → ℝ) (hf : f 0 = 0) :
    cfc f H = ∑ i : {i : n // 0 < hH.1.eigenvalues i},
      (f (hH.1.eigenvalues i.1) : ℂ) •
        Matrix.vecMulVec (fun x => hH.1.eigenvectorBasis i.1 x)
          (star (fun x => hH.1.eigenvectorBasis i.1 x)) := by
  classical
  rw [cfc_spectral_sum H hH.1 f]
  have hzero : (∑ i : {i : n // ¬0 < hH.1.eigenvalues i},
      (f (hH.1.eigenvalues i.1) : ℂ) •
        Matrix.vecMulVec (fun x => hH.1.eigenvectorBasis i.1 x)
          (star (fun x => hH.1.eigenvectorBasis i.1 x))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi0 : hH.1.eigenvalues i.1 = 0 :=
      le_antisymm (le_of_not_gt i.2) (hH.eigenvalues_nonneg i.1)
    rw [hi0, hf, Complex.ofReal_zero, zero_smul]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : n => 0 < hH.1.eigenvalues i)
    (fun i : n => (f (hH.1.eigenvalues i) : ℂ) •
      Matrix.vecMulVec (fun x => hH.1.eigenvectorBasis i x)
        (star (fun x => hH.1.eigenvectorBasis i x)))
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]
  {Φ : QuantumChannel a b} {ρ σ : DensityState a}

set_option maxHeartbeats 1000000 in
/-- The relative-modular inverse-square-root vector is the actual physical Petz matrix. -/
theorem spectral_petz_coordinate_matrix (D : SupportedRelativeModularData Φ ρ σ) :
    D.spectralX (cfc (fun t : ℝ => 1 / Real.sqrt t) D.B *ᵥ D.η) =
      spectralInverseSqrt D.Q * cfc Real.sqrt D.T := by
  classical
  have hdiag : cfc (fun t : ℝ => 1 / Real.sqrt t) D.B =
      diagonal (fun lk : D.L × D.K =>
        ((Real.sqrt (D.pk lk.2) / Real.sqrt (D.ql lk.1) : ℝ) : ℂ)) := by
    change cfc (fun t : ℝ => 1 / Real.sqrt t)
      (diagonal (fun lk : D.L × D.K => ((D.ql lk.1 / D.pk lk.2 : ℝ) : ℂ))) = _
    rw [cfc_diagonal]
    congr 1
    funext lk
    rw [Real.sqrt_div (le_of_lt lk.1.2), one_div_div]
  have hcoeff (lk : D.L × D.K) :
      (cfc (fun t : ℝ => 1 / Real.sqrt t) D.B *ᵥ D.η) lk /
          (Real.sqrt (D.pk lk.2) : ℂ) =
        ((Real.sqrt (D.pk lk.2) : ℂ) / (Real.sqrt (D.ql lk.1) : ℂ)) *
          (star (D.w lk.1) ⬝ᵥ D.z lk.2) := by
    rw [hdiag, Matrix.mulVec_diagonal]
    dsimp only [SupportedRelativeModularData.η]
    rw [Complex.ofReal_div]
    have hp : (Real.sqrt (D.pk lk.2) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr lk.2.2))
    field_simp
    <;> ring
  have hQ : spectralInverseSqrt D.Q = ∑ l : D.L,
      (((Real.sqrt (D.ql l))⁻¹ : ℝ) : ℂ) •
        Matrix.vecMulVec (D.w l) (star (D.w l)) := by
    exact cfc_supported_sum D.Q D.hQ (fun t : ℝ => (Real.sqrt t)⁻¹) (by simp)
  have hT : cfc Real.sqrt D.T = ∑ k : D.K,
      (Real.sqrt (D.pk k) : ℂ) •
        Matrix.vecMulVec (D.z k) (star (D.z k)) := by
    exact cfc_supported_sum D.T D.hT Real.sqrt (by simp)
  change (∑ lk : D.L × D.K,
    ((cfc (fun t : ℝ => 1 / Real.sqrt t) D.B *ᵥ D.η) lk /
      (Real.sqrt (D.pk lk.2) : ℂ)) •
      Matrix.vecMulVec (D.w lk.1) (star (D.z lk.2))) = _
  simp_rw [hcoeff]
  rw [hQ, hT]
  rw [Matrix.sum_mul]
  simp only [Fintype.sum_prod_type, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul, smul_smul, Complex.ofReal_inv, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  simp only [div_eq_mul_inv]
  ring

private theorem supported_input_reconstruction
    (M : SupportedRelativeModularModel Φ ρ σ) (i : M.data.I) :
    (∑ j : M.data.J, (star (M.data.v j) ⬝ᵥ M.data.u i) • M.data.v j) =
      M.data.u i := by
  classical
  let D := M.data
  have hfull : (∑ j : a,
      (star (fun x => D.hS.1.eigenvectorBasis j x) ⬝ᵥ D.u i) •
        (fun x => D.hS.1.eigenvectorBasis j x)) = D.u i := by
    have h := D.hS.1.eigenvectorBasis.sum_repr' (WithLp.toLp 2 (D.u i))
    have h' := congrArg WithLp.ofLp h
    simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul,
      EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      dotProduct_comm] using h'
  have hzero : (∑ j : {j : a // ¬0 < D.hS.1.eigenvalues j},
      (star (fun x => D.hS.1.eigenvectorBasis j.1 x) ⬝ᵥ D.u i) •
        (fun x => D.hS.1.eigenvectorBasis j.1 x)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : D.hS.1.eigenvalues j.1 = 0 :=
      le_antisymm (le_of_not_gt j.2) (D.hS.eigenvalues_nonneg j.1)
    rw [M.zeroCoordinatesR j.1 hj0 i.1 i.2, zero_smul]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun j : a => 0 < D.hS.1.eigenvalues j)
    (fun j : a => (star (fun x => D.hS.1.eigenvectorBasis j x) ⬝ᵥ D.u i) •
      (fun x => D.hS.1.eigenvectorBasis j x))
  rw [hzero, add_zero, hfull] at hsplit
  exact hsplit

set_option maxHeartbeats 1000000 in
/-- Exact positive-spectrum coordinates reconstruct the reference-weighted matrix
on the entire support of the input state. The kernel columns remain explicit. -/
theorem petz_input_support_columns (M : SupportedRelativeModularModel Φ ρ σ)
    (Y : Matrix b b ℂ)
    (hcoord : ∀ (j : M.data.J) (i : M.data.I),
      (Real.sqrt (M.data.sj j) : ℂ) *
          (star (M.data.v j) ⬝ᵥ (M.data.Ψ Y *ᵥ M.data.u i)) =
        (Real.sqrt (M.data.ri i) : ℂ) * (star (M.data.v j) ⬝ᵥ M.data.u i)) :
    cfc Real.sqrt M.data.S * M.data.Ψ Y * spectralSupport M.data.R =
      cfc Real.sqrt M.data.R := by
  classical
  let D := M.data
  have hS : cfc Real.sqrt D.S = ∑ j : D.J,
      (Real.sqrt (D.sj j) : ℂ) • Matrix.vecMulVec (D.v j) (star (D.v j)) :=
    cfc_supported_sum D.S D.hS Real.sqrt (by simp)
  have hcolumns (i : D.I) :
      (cfc Real.sqrt D.S * D.Ψ Y) *ᵥ D.u i =
        (Real.sqrt (D.ri i) : ℂ) • D.u i := by
    rw [← Matrix.mulVec_mulVec, hS, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul, smul_smul]
    calc
      _ = ∑ j : D.J, ((Real.sqrt (D.ri i) : ℂ) *
          (star (D.v j) ⬝ᵥ D.u i)) • D.v j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoord j i]
      _ = (Real.sqrt (D.ri i) : ℂ) • D.u i := by
        simp only [← smul_smul]
        rw [← Finset.smul_sum, supported_input_reconstruction M i]
  have hP : spectralSupport D.R = ∑ i : D.I,
      Matrix.vecMulVec (D.u i) (star (D.u i)) := by
    change cfc (fun t : ℝ => if t = 0 then 0 else 1) D.R = _
    rw [cfc_supported_sum D.R D.hR _ (by simp)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [if_neg (ne_of_gt i.2), Complex.ofReal_one, one_smul]
  have hR : cfc Real.sqrt D.R = ∑ i : D.I,
      (Real.sqrt (D.ri i) : ℂ) • Matrix.vecMulVec (D.u i) (star (D.u i)) :=
    cfc_supported_sum D.R D.hR Real.sqrt (by simp)
  rw [hP, hR, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mul_vecMulVec, hcolumns, Matrix.smul_vecMulVec]

end D5.S3.Quantum.Recovery.PetzSpectralCoordinates
