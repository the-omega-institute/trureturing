/- GID: D5/S3/Quantum/Recovery/BurriReverseCompletion
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriReverseCompletion
   mirror-E: none(waiver:unfinished-independent-fidelity-review)
   anchors: []
   utility: none
   digest: Full nonnegative source SVD and independence of its null-space completion. -/

import D5.S3.Quantum.Recovery.BurriReverseSource

/-! Identity padding is a genuine source SVD completion; all allowed completions
have the same action on every prepared physical input. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Recovery.BurriReverseDecoder
open D5.S3.Quantum.Recovery.BurriReversePolar
open D5.S3.Quantum.Recovery.BurriReversePetz
open D5.S3.Quantum.Recovery.BurriReverseSource

namespace D5.S3.Quantum.Recovery.BurriReverseCompletion

theorem lift_mul_pad (Z T : Matrix B B ℂ) : lift Z * pad T = lift (Z * T) := by
  simp only [pad, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
    lift_mul, Matrix.mul_one, sub_self, add_zero]

theorem pad_mul_lift (Z T : Matrix B B ℂ) : pad Z * lift T = lift (Z * T) := by
  simp only [pad, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
    lift_mul, Matrix.one_mul, sub_self, add_zero]

def padUnitary (Z : Matrix.unitaryGroup B ℂ) : Matrix.unitaryGroup P ℂ :=
  ⟨pad Z, by
    apply Unitary.mem_iff.mpr
    simpa only [star_eq_conjTranspose] using
      pad_unitary (Z : Matrix B B ℂ) (by
        simpa only [star_eq_conjTranspose] using Z.prop)⟩

/-- Nonnegative active singular values are extended by zero, and both unitary
factors by the identity, on the eighteen unused source coordinates. -/
theorem full_source_svd :
    ∃ H T : Matrix.unitaryGroup P ℂ, ∃ v : P → ℝ,
      (∀ p, 0 ≤ v p) ∧
      M = (H : Matrix P P ℂ) * Matrix.diagonal (fun p => (v p : ℂ)) * T ∧
      sourceU (cosine 4) (cosine 2) (sine 4) (sine 2) =
        (T : Matrix P P ℂ)ᴴ * (H : Matrix P P ℂ)ᴴ := by
  obtain ⟨H, T, v, hv, hM, hU⟩ := active_svd
  refine ⟨padUnitary H, padUnitary T,
    fun p => if active p.2 then v (p.1, p.2.2.2) else 0,
    fun p => by split_ifs; exact hv _; exact le_rfl, ?_, ?_⟩
  · have hd : Matrix.diagonal (fun p : P =>
        ((if active p.2 then v (p.1, p.2.2.2) else 0 : ℝ) : ℂ)) =
        lift (Matrix.diagonal (fun b => (v b : ℂ))) := by
      rw [lift_diagonal]
      congr 1
      funext p
      split_ifs <;> simp
    change M = pad (H : Matrix B B ℂ) * _ * pad (T : Matrix B B ℂ)
    rw [hd, pad_mul_lift, lift_mul_pad, source_matrix, hM]
  · change sourceU _ _ _ _ = (pad (T : Matrix B B ℂ))ᴴ *
      (pad (H : Matrix B B ℂ))ᴴ
    rw [source_unitary_identification, pad_adjoint, pad_adjoint, pad_mul, ← hU]

theorem active_matrix_invertible : IsUnit activeM := by
  have hd : D.PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro b
    dsimp [D]
    split_ifs <;> simp [s, t, Complex.pos_iff]
  simpa only [activeM, D, Matrix.smul_mul] using
    (amplitude_positive.smul (by norm_num [Complex.pos_iff] : (0 : ℂ) < 1 / 62)).isUnit.mul hd.isUnit

theorem polar_product_unique (Uprime : Matrix P P ℂ)
    (hu : Uprime * Uprimeᴴ = 1) (hp : (M * Uprime).PosSemidef) :
    M * Uprime = M * pad U := by
  have hs (T : Matrix P P ℂ) (hT : T * Tᴴ = 1) (hP : (M * T).PosSemidef) :
      (M * T) * (M * T) = M * Mᴴ := by
    calc
      _ = (M * T) * (M * T)ᴴ := by rw [hP.isHermitian]
      _ = M * Mᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc T Tᴴ, hT, Matrix.one_mul]
  exact (CFC.sqrt_unique (hs Uprime hu hp) hp.nonneg).symm.trans
    (CFC.sqrt_unique (hs (pad U) (pad_unitary U actual_unitary).2 full_polar_positive)
      full_polar_positive.nonneg)

theorem adjoint_injection_pad (Z : Matrix B B ℂ) : injectᴴ * pad Z = Z * injectᴴ := by
  simp only [pad, lift, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
    ← Matrix.mul_assoc, injection_isometry, Matrix.one_mul, sub_self, add_zero]

/-- Only the supported rows are determined by positivity; no off-support
equality of different completions is asserted. -/
theorem supported_rows_unique (Uprime : Matrix P P ℂ)
    (hu : Uprime * Uprimeᴴ = 1) (hp : (M * Uprime).PosSemidef) :
    injectᴴ * Uprime = U * injectᴴ := by
  have hrow : injectᴴ * M = activeM * injectᴴ := by
    simp only [source_matrix, lift, ← Matrix.mul_assoc, injection_isometry, Matrix.one_mul]
  have h := congrArg (fun Z : Matrix P P ℂ => injectᴴ * Z)
    (polar_product_unique Uprime hu hp)
  simp only [← Matrix.mul_assoc, hrow] at h
  rw [Matrix.mul_assoc activeM injectᴴ (pad U), adjoint_injection_pad] at h
  have hc := congrArg (fun Z : Matrix B P ℂ => activeM⁻¹ * Z) h
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp active_matrix_invertible), Matrix.one_mul] using hc

theorem supported_action_unique (Uprime : Matrix P P ℂ)
    (hu : Uprime * Uprimeᴴ = 1) (hp : (M * Uprime).PosSemidef) :
    Uprime * inject = inject * U := by
  have hs := congrArg (fun Z : Matrix B P ℂ => Zᴴ) (supported_rows_unique Uprime hu hp)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hs
  calc
    Uprime * inject = Uprime * (inject * Uᴴ) * U := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc inject, actual_unitary.1, Matrix.mul_one]
    _ = Uprime * (Uprimeᴴ * inject) * U := by rw [hs]
    _ = inject * U := by rw [← Matrix.mul_assoc Uprime Uprimeᴴ, hu, Matrix.one_mul]

theorem ancilla_normalized : (∑ i : A, ∑ j : A, star (ancilla i j) * ancilla i j) = 1 := by
  norm_num [ancilla, Fin.sum_univ_two]

theorem source_permutation_unitary : Wᴴ * W = 1 ∧ W * Wᴴ = 1 := by
  simp only [W, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, inv_mul_cancel, Matrix.permMatrix_one, and_self]

theorem injection_transpose : inject.transpose = injectᴴ := by
  ext p b
  simp [inject, Matrix.transpose_apply, Matrix.conjTranspose_apply]

/-- Appendix A.9 as a full matrix of purification amplitudes, including zeros. -/
theorem source_purification_identity :
    purifiedAmplitude * (W * prepare).transpose = CFC.sqrt X := by
  rw [source_injection, injection_transpose, purified_amplitude, Matrix.smul_mul,
    complementary_root]
  rfl

/-- Appendix A.11 followed by actual ancilla preparation is independent of all
unitary choices in the nonnegative source SVD's zero singular subspace. -/
theorem source_decoder_completion_independent (Uprime : Matrix P P ℂ)
    (hu : Uprime * Uprimeᴴ = 1) (hp : (M * Uprime).PosSemidef)
    (e : E) (k : A) (b : B) :
    ((Uprime * W) * prepare) (k, e) b =
      swKraus (cosine 4) (cosine 2) (sine 4) (sine 2) e k b := by
  rw [Matrix.mul_assoc, source_injection, supported_action_unique Uprime hu hp]
  have h := supported_rows (cosine 4) (cosine 2) (sine 4) (sine 2) e k b
  rw [h]
  rw [inject_mul]
  rfl

#print axioms full_source_svd
#print axioms supported_action_unique
#print axioms source_purification_identity
#print axioms source_decoder_completion_independent

end D5.S3.Quantum.Recovery.BurriReverseCompletion
