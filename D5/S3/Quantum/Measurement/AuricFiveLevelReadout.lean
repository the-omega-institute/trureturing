import D5.S3.Quantum.Measurement.AuricDiamondBounds
import D5.S3.Quantum.Measurement.AuricTiltedInstrument

/-! # The two-flag output test on the five-level input purification -/

namespace D5.S3.Quantum.Measurement.AuricFiveLevelReadout

open _root_.Matrix D5.S3.Quantum.Foundation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.AuricDiamondBounds
open D5.S3.Quantum.Measurement.AuricTiltedInstrument

abbrev Level := Fin 5
abbrev Flag := Fin 2
abbrev ChoiIndex := (Flag × Level) × Level

private noncomputable def mass (r : ℝ) : ℝ := (r + 2 * Real.sqrt 2)⁻¹

private noncomputable def backgroundAmplitude (r : ℝ) : ℝ :=
  Real.sqrt (mass r / Real.sqrt 2)

private noncomputable def spectatorAmplitude (r : ℝ) : ℝ :=
  Real.sqrt (r * mass r)

noncomputable def inputWeights (r : ℝ) : Level → ℂ :=
  ![backgroundAmplitude r, backgroundAmplitude r, backgroundAmplitude r,
    backgroundAmplitude r, spectatorAmplitude r]

private noncomputable def activeAmplitude (r : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt 2 * mass r)

private noncomputable def outputWeights (r : ℝ) (j : Flag) : Level → ℂ :=
  if j = 0 then ![activeAmplitude r, activeAmplitude r, 0, 0, spectatorAmplitude r]
  else ![0, 0, activeAmplitude r, activeAmplitude r, spectatorAmplitude r]

/-- A column is supported on a single flag and on equal input and output levels. -/
noncomputable def outputFrame (r : ℝ) : Matrix ChoiIndex Flag ℂ :=
  fun x j => if x.1.1 = j ∧ x.1.2 = x.2 then outputWeights r j x.2 else 0

noncomputable def inputVector (r : ℝ) : Level × Level → ℂ :=
  fun x => if x.1 = x.2 then inputWeights r x.2 else 0

private theorem mass_pos (r : ℝ) (hr : 0 < r) : 0 < mass r := by
  unfold mass
  positivity

private theorem mass_spec (r : ℝ) (hr : 0 < r) :
    r * mass r + 2 * (Real.sqrt 2 * mass r) = 1 := by
  unfold mass
  have hn : r + 2 * Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]

private theorem input_sq (r : ℝ) (hr : 0 < r) :
    backgroundAmplitude r ^ 2 = mass r / Real.sqrt 2 ∧
      spectatorAmplitude r ^ 2 = r * mass r := by
  have hq := mass_pos r hr
  exact ⟨Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)⟩

/-- The purification has unit input trace. -/
theorem input_purification_trace (r : ℝ) (hr : 0 < r) :
    (vecMulVec (inputVector r) (star (inputVector r))).trace = 1 := by
  have hsq := input_sq r hr
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hstep : 4 * (mass r / Real.sqrt 2) = 2 * (Real.sqrt 2 * mass r) := by
    field_simp [hs0.ne']
    nlinarith only [congrArg (fun x : ℝ => x * mass r) hs]
  have he : 4 * backgroundAmplitude r ^ 2 + spectatorAmplitude r ^ 2 = 1 := by
    rw [hsq.1, hsq.2, hstep]
    linarith only [mass_spec r hr]
  rw [trace_vecMulVec]
  have hdiag : inputVector r ⬝ᵥ star (inputVector r) =
      ∑ j : Level, inputWeights r j * star (inputWeights r j) := by
    simp [dotProduct, Fintype.sum_prod_type, inputVector, Pi.star_apply]
  rw [hdiag]
  simp only [inputWeights, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Complex.star_def, Complex.conj_ofReal, add_zero]
  norm_cast
  linarith only [he, pow_two (backgroundAmplitude r), pow_two (spectatorAmplitude r)]

/-- The output columns define one legitimate orthogonal projection across both flags. -/
theorem outputFrame_isometry (r : ℝ) (hr : 0 < r) :
    (outputFrame r)ᴴ * outputFrame r = 1 := by
  have hq := mass_pos r hr
  have hs : activeAmplitude r ^ 2 = Real.sqrt 2 * mass r :=
    Real.sq_sqrt (by positivity)
  have hss := (input_sq r hr).2
  have hnorm : ∀ j : Flag, (∑ i : Level, star (outputWeights r j i) * outputWeights r j i) = 1 := by
    intro j
    have he : 2 * activeAmplitude r ^ 2 + spectatorAmplitude r ^ 2 = 1 := by
      rw [hs, hss]
      linarith only [mass_spec r hr]
    fin_cases j <;> simp [outputWeights, Fin.sum_univ_succ] <;> norm_cast <;>
      linarith only [he, pow_two (activeAmplitude r), pow_two (spectatorAmplitude r)]
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, outputFrame,
      Fintype.sum_prod_type, ite_and, Finset.sum_ite_irrel] using hnorm i
  · rw [Matrix.one_apply_ne hij, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    rintro ⟨⟨label, k⟩, l⟩ _
    rw [Matrix.conjTranspose_apply]
    by_cases hleft : label = i
    · have hright : label ≠ j := by rwa [hleft]
      simp [outputFrame, hright]
    · simp [outputFrame, hleft]

/-- The unweighted Choi tests are the two vectorized diagonal witnesses placed
in their respective flag coordinates. -/
noncomputable def witnessFrame (r : ℝ) : Matrix ChoiIndex Flag ℂ :=
  fun x j => if x.1.1 = j then (if j = 0 then witnessZero r else witnessOne r) x.1.2 x.2
    else 0

/-- Multiplying the orthogonal measurement columns by the input weights
recovers the exact common scaling of the two Choi witness vectors. -/
theorem input_diagonal_mul_outputFrame (r : ℝ) (hr : 0 < r) :
    (Matrix.diagonal (fun x : ChoiIndex => inputWeights r x.2))ᴴ * outputFrame r =
      (mass r : ℂ) • witnessFrame r := by
  have hq := mass_pos r hr
  have hs0 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hact : backgroundAmplitude r * activeAmplitude r = mass r := by
    unfold backgroundAmplitude activeAmplitude
    rw [← Real.sqrt_mul (by positivity)]
    have harg : (mass r / Real.sqrt 2) * (Real.sqrt 2 * mass r) = mass r ^ 2 := by
      field_simp [hs0.ne']
    rw [harg, Real.sqrt_sq hq.le]
  have hspec : spectatorAmplitude r * spectatorAmplitude r = r * mass r := by
    rw [← pow_two]
    exact (input_sq r hr).2
  ext ⟨⟨label, i⟩, k⟩ j
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases hf : label = j
  · subst label
    by_cases hk : i = k
    · subst i
      fin_cases j <;> fin_cases k <;>
        simp [outputFrame, outputWeights, inputWeights, witnessFrame, witnessZero,
          witnessOne, Pi.star_apply, ← Complex.ofReal_mul, hact, hspec] <;> ring
    · by_cases hj : j = 0 <;>
        simp [outputFrame, witnessFrame, witnessZero, witnessOne, hk, hj]
  · simp [outputFrame, witnessFrame, hf]

/-- The reference purification gives a lower bound for comparing any two
trace-compatible CP maps with the original two-flag output space. -/
theorem two_flag_score_le_trace_error (r : ℝ) (hr : 0 < r)
    (F G : MatrixMap Level (Flag × Level) ℂ)
    (hF : F.IsCompletelyPositive) (hG : G.IsCompletelyPositive)
    (htrace : ∀ X, (F X).trace = (G X).trace) :
    2 * mass r ^ 2 * ((witnessFrame r)ᴴ * (F - G).choi_matrix * witnessFrame r).trace.re ≤
      FiniteTraceDistance.traceNorm
        (MatrixMap.kron (F - G) (LinearMap.id : MatrixMap Level Level ℂ)
          (vecMulVec (inputVector r) (star (inputVector r)))) := by
  let D : Matrix ChoiIndex ChoiIndex ℂ := diagonal (fun x => inputWeights r x.2)
  let V := outputFrame r
  let W := witnessFrame r
  let J := (F - G).choi_matrix
  have h := weighted_choi_trace_le_amplified_traceNorm F G hF hG htrace
    (inputWeights r) V (outputFrame_isometry r hr)
  change 2 * (Vᴴ * D * J * Dᴴ * V).trace.re ≤ _ at h
  have hright : Dᴴ * V = (mass r : ℂ) • W := input_diagonal_mul_outputFrame r hr
  have hleft : Vᴴ * D = (mass r : ℂ) • Wᴴ := by
    have he := congrArg Matrix.conjTranspose hright
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, Complex.star_def] using he
  have hprod : Vᴴ * D * J * Dᴴ * V = (mass r : ℂ) • ((mass r : ℂ) • (Wᴴ * J * W)) := by
    rw [Matrix.mul_assoc (_ * J) Dᴴ V, hleft, hright, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul]
  rw [hprod, Matrix.trace_smul, Matrix.trace_smul] at h
  change 2 * ((mass r : ℂ) * ((mass r : ℂ) * (Wᴴ * J * W).trace)).re ≤ _ at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  have hv : (fun x : Level × Level => if x.1 = x.2 then inputWeights r x.2 else 0) =
      inputVector r := by
    rfl
  rw [hv] at h
  convert h using 1
  change 2 * mass r ^ 2 * (Wᴴ * J * W).trace.re =
    2 * (mass r * (mass r * (Wᴴ * J * W).trace.re))
  ring

end D5.S3.Quantum.Measurement.AuricFiveLevelReadout
