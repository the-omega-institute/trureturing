/- GID: D5/S3/Quantum/Schatten/ExpandingGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/ExpandingGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Expanding square matrices and right multiplication. -/

import D5.S3.Quantum.Schatten.SingularValueOrder
import D5.S3.Quantum.Foundation.FiniteTraceDistance

/-! Expansion transfers from the right Gram matrix to the left Gram matrix. -/
noncomputable section
open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Schatten

/-- An expanding square matrix is invertible. -/
theorem expanding_isUnit_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (h : (Tᴴ * T - 1).PosSemidef) : IsUnit T.det := by
  have hp : (Tᴴ * T).PosDef := by
    convert (PosDef.one : (1 : Matrix (Fin n) (Fin n) ℂ).PosDef).add_posSemidef h using 1
    abel
  have hu : IsUnit (Tᴴ * T).det := (Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- For a square matrix, expansion also holds after taking the adjoint. -/
theorem expanding_adjoint {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (h : (Tᴴ * T - 1).PosSemidef) : (T * Tᴴ - 1).PosSemidef := by
  obtain ⟨U, V, hv⟩ := Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues T
  let S : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (singularValues T i : ℂ))
  have hv : T = U.val * S * V.valᴴ := by
    simpa only [S, singularValues, conjTranspose_conjTranspose] using hv
  have hs : Sᴴ = S := by simp [S]
  have hu : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  have hvv : V.valᴴ * V.val = 1 := Matrix.mem_unitaryGroup_iff'.mp V.property
  have hvvr : V.val * V.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp V.property
  have huur : U.val * U.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.property
  have hg : Tᴴ * T = V.val * (S * S) * V.valᴴ := by
    calc Tᴴ * T = V.val * S * (U.valᴴ * U.val) * S * V.valᴴ := by
           rw [hv, conjTranspose_mul, conjTranspose_mul, hs, conjTranspose_conjTranspose]
           noncomm_ring
         _ = V.val * (S * S) * V.valᴴ := by rw [hu]; noncomm_ring
  have hg' : T * Tᴴ = U.val * (S * S) * U.valᴴ := by
    calc T * Tᴴ = U.val * S * (V.valᴴ * V.val) * S * U.valᴴ := by
           rw [hv, conjTranspose_mul, conjTranspose_mul, hs, conjTranspose_conjTranspose]
           noncomm_ring
         _ = U.val * (S * S) * U.valᴴ := by rw [hvv]; noncomm_ring
  have hd : (S * S - 1).PosSemidef := by
    have hh := h.conjTranspose_mul_mul_same V.val
    have he : V.valᴴ * (Tᴴ * T - 1) * V.val = S * S - 1 := by
      rw [hg]
      calc V.valᴴ * (V.val * (S * S) * V.valᴴ - 1) * V.val =
          (V.valᴴ * V.val) * (S * S) * (V.valᴴ * V.val) - V.valᴴ * V.val := by
            noncomm_ring
        _ = S * S - 1 := by rw [hvv]; simp
    rwa [he] at hh
  have hh := hd.mul_mul_conjTranspose_same U.val
  convert hh using 1
  calc T * Tᴴ - 1 = U.val * (S * S) * U.valᴴ - U.val * U.valᴴ := by rw [hg', huur]
       _ = U.val * (S * S - 1) * U.valᴴ := by noncomm_ring

/-- Right multiplication by an expanding square matrix increases each singular value. -/
theorem expanding_right_singularValuesSorted {n : ℕ}
    (A T : Matrix (Fin n) (Fin n) ℂ) (h : (Tᴴ * T - 1).PosSemidef)
    (i : Fin (Fintype.card (Fin n))) :
    singularValuesSorted A i ≤ singularValuesSorted (A * T) i := by
  have hp := (expanding_adjoint T h).mul_mul_conjTranspose_same A
  have hg : ((A * T)ᴴ)ᴴ * (A * T)ᴴ - (Aᴴ)ᴴ * Aᴴ = A * (T * Tᴴ - 1) * Aᴴ := by
    simp only [conjTranspose_conjTranspose, conjTranspose_mul]
    noncomm_ring
  have hm := gram_singularValuesSorted_mono Aᴴ (A * T)ᴴ (by rw [hg]; exact hp) i
  simpa only [singularValuesSorted_conjTranspose] using hm

end D5.S3.Quantum.Schatten
