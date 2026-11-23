/- GID: D5/S3/Quantum/Recovery/PetzPhysicalFirstVariation
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/PetzPhysicalFirstVariation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual ordinary Petz derivative on the physical two-flag path. -/

import D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot
import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
import D5.S3.Quantum.Recovery.PetzProjectedHessian

/-! The first variation of ordinary Petz recovery for the physical two-flag reference. -/

noncomputable section

open Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (mpow_smul_of_nonneg)
open D5.S3.Quantum.Recovery.BKMFlagRefinement
open D5.S3.Quantum.Recovery.PetzProjectedHessian (Joint)
open D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot

open private symmetric_posDef from D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot

namespace D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation

/-- The signed flag biases, in retained-space-first ordering. -/
def flagBias (ε : ℝ) : Fin 2 → ℝ := ![ε, -ε]

private def scale (η : ℝ) : ℝ := (1 + η ^ 2)⁻¹

/-- The faithful retained reference with eigenvalue ratio η². -/
def referenceMarginal (η : ℝ) : Qubit :=
  diagonal fun i : Fin 2 => ((scale η * ![η ^ 2, 1] i : ℝ) : ℂ)

private def referenceBlock (ε η c : ℝ) (s : Fin 2) : Qubit :=
  (scale η / 2) • unscaledBlock (flagBias ε s) η c

/-- The trace-one two-flag reference. -/
def reference (ε η c : ℝ) : Joint := joint (referenceBlock ε η c)

private def profile (c : ℝ) : ℝ := (1 + Real.sqrt (1 - 4 * c ^ 2)) / 2

/-- The retained source of eigenvalues 1−t and t on the physical rotation path. -/
def sourceMarginal (t c : ℝ) : Qubit :=
  let r := profile c
  let j := 1 - t - t
  qubit (t + j * r) (j * c) (j * c) (1 - t - j * r)

private theorem profile_firstVariation : profile 0 = 1 ∧ HasDerivAt profile 0 0 := by
  refine ⟨by norm_num [profile], ?_⟩
  have h : HasDerivAt (fun c : ℝ => 1 - 4 * c ^ 2) 0 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 4) using 1
    · rfl
    · simp
  have hs := h.sqrt (by norm_num)
  change HasDerivAt (fun c => (1 + Real.sqrt (1 - 4 * c ^ 2)) / 2) 0 0
  simpa using ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add hs).div_const 2

private theorem source_firstVariation (t : ℝ) :
    sourceMarginal t 0 = qubit (1 - t) 0 0 t ∧
      HasDerivAt (sourceMarginal t) (qubit 0 (1 - t - t) (1 - t - t) 0) 0 := by
  obtain ⟨hr, hd⟩ := profile_firstVariation
  refine ⟨?_, hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_⟩
  · simp [sourceMarginal, hr]
  · let j₀ := 1 - t - t
    have h₀ := (hasDerivAt_const (0 : ℝ) t).add (hd.const_mul j₀)
    have h₁ := (hasDerivAt_const (0 : ℝ) (1 - t)).sub (hd.const_mul j₀)
    have hₓ := (hasDerivAt_id (0 : ℝ)).const_mul j₀
    fin_cases i <;> fin_cases j <;>
      first
      | simpa [sourceMarginal, qubit, j₀] using h₀.ofReal_comp
      | simpa [sourceMarginal, qubit, j₀] using h₁.ofReal_comp
      | simpa [sourceMarginal, qubit, j₀] using hₓ.ofReal_comp

private theorem reference_marginal (ε η c : ℝ) :
    partialTraceRight (reference ε η c) = referenceMarginal η := by
  rw [show partialTraceRight (reference ε η c) = marginal (referenceBlock ε η c) by rfl,
    marginal_eq_sum]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [referenceBlock, referenceMarginal, Fin.sum_univ_two, flagBias, unscaledBlock, qubit,
      Complex.real_smul] <;> ring

private theorem flag_pos {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 16) (s : Fin 2) :
    0 < 1 - flagBias ε s ∧ 0 < 1 + flagBias ε s := by
  fin_cases s <;> simp [flagBias] <;> constructor <;> linarith

private theorem reference_near {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 16) (hη : 0 < η) :
    ∀ᶠ c in 𝓝 (0 : ℝ), ∀ s, (referenceBlock ε η c s).PosDef := by
  apply (Filter.eventually_all.2 _)
  intro s
  obtain ⟨hb, hd⟩ := flag_pos hε hε' s
  have h0 : 0 < detFactor (flagBias ε s) 0 := by simpa [detFactor] using mul_pos hb hd
  have hcont : Continuous (detFactor (flagBias ε s)) := by unfold detFactor; fun_prop
  filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds h0)] with c hc
  exact (unscaledBlock_posDef hη hb hc).smul (show 0 < scale η / 2 by unfold scale; positivity)

private theorem inverse_half {η : ℝ} (hη : 0 < η) :
    mpow (referenceMarginal η) (-(1 / 2)) =
      (Real.sqrt (scale η))⁻¹ • qubit η⁻¹ 0 0 1 := by
  have hscale : 0 < scale η := by unfold scale; positivity
  have hdiag : mpow (referenceMarginal η) (-(1 / 2)) =
      diagonal fun i : Fin 2 => (((scale η * ![η ^ 2, 1] i) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) :=
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
      (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) (fun i => scale η * ![η ^ 2, 1] i)
  rw [hdiag]
  have hpow : (η ^ 2 : ℝ) ^ (-(1 / 2) : ℝ) = η⁻¹ := by
    rw [Real.rpow_neg (sq_nonneg η), ← Real.sqrt_eq_rpow, Real.sqrt_sq hη.le]
  ext i j
  fin_cases i <;> fin_cases j
  · change (((scale η * η ^ 2) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) =
      (Real.sqrt (scale η))⁻¹ • ((η⁻¹ : ℝ) : ℂ)
    rw [Real.mul_rpow hscale.le (sq_nonneg η), hpow, Real.rpow_neg hscale.le, ← Real.sqrt_eq_rpow]
    exact Complex.ofReal_mul _ _
  · simp [qubit]
  · simp [qubit]
  · change (((scale η * 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) = (Real.sqrt (scale η))⁻¹ • (1 : ℂ)
    rw [mul_one, Real.rpow_neg hscale.le, ← Real.sqrt_eq_rpow]
    simp [Complex.real_smul]

private theorem recovery_blocks {ε η c : ℝ} (hη : 0 < η)
    (h : ∀ s, (referenceBlock ε η c s).PosDef) (P : Qubit) :
    partialTracePetz (reference ε η c) P =
      joint fun s => (1 / 2 : ℝ) •
        (normalizedRoot (flagBias ε s) η c * P * (normalizedRoot (flagBias ε s) η c)ᴴ) := by
  have hscale : 0 < scale η := by unfold scale; positivity
  have hcoef :
      Real.sqrt (scale η / 2) * (Real.sqrt (scale η))⁻¹ *
        (Real.sqrt (scale η))⁻¹ * Real.sqrt (scale η / 2) = 1 / 2 := by
    have hscale' := (Real.sqrt_pos.mpr hscale).ne'
    field_simp
    nlinarith [Real.sq_sqrt hscale.le, Real.sq_sqrt (show 0 ≤ scale η / 2 by positivity)]
  rw [reference, partialTracePetz, mpow_joint _ (fun s => (h s).isHermitian),
    lift_eq_joint, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
  change joint _ = joint _
  have hm : partialTraceRight (joint (referenceBlock ε η c)) = referenceMarginal η :=
    reference_marginal ε η c
  apply congrArg joint
  funext s
  let M := unscaledBlock (flagBias ε s) η c
  have hM : M.PosSemidef := by
    have hh := (h s).posSemidef
    have he : ((scale η)⁻¹ * 2 : ℝ) • referenceBlock ε η c s = M := by
      change ((scale η)⁻¹ * 2 : ℝ) • ((scale η / 2) • M) = M
      rw [smul_smul, show (scale η)⁻¹ * 2 * (scale η / 2) = 1 by field_simp, one_smul]
    rw [← he]
    exact hh.smul (by positivity)
  have hroot : (mpow M (1 / 2)).IsHermitian := by
    rw [mpow, ← CFC.rpow_eq_cfc_real hM.nonneg, ← CFC.sqrt_eq_rpow]
    exact (CFC.sqrt_nonneg M).posSemidef.isHermitian
  have hdiag : (qubit η⁻¹ 0 0 1)ᴴ = qubit η⁻¹ 0 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [qubit]
  rw [hm, inverse_half hη, show referenceBlock ε η c s = (scale η / 2) • M from rfl,
    mpow_smul_of_nonneg hM.nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow]
  simp only [normalizedRoot, ← show M = unscaledBlock (flagBias ε s) η c from rfl,
    Matrix.conjTranspose_mul, hdiag, hroot.eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show Real.sqrt (scale η / 2) *
      ((Real.sqrt (scale η))⁻¹ * (Real.sqrt (scale η))⁻¹ * Real.sqrt (scale η / 2)) =
      (1 / 2 : ℝ) by simpa only [mul_assoc] using hcoef]
  simp only [Matrix.mul_assoc]

private theorem matrix_mul_deriv {A B : ℝ → Qubit} {A' B' : Qubit}
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun c => A c * B c) (A' * B 0 + A 0 * B') 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB k) j)

/-- The real within-flag coherence of the actual joint Petz derivative. -/
def recoveryEntry (t x η : ℝ) : ℝ :=
  Real.sqrt (1 - x) * Real.sqrt (1 + x) * (1 - t - t) / 2 +
    x * ((1 - t) * Real.sqrt (1 - x) + t * η * Real.sqrt (1 + x)) /
      (η * Real.sqrt (1 - x) + Real.sqrt (1 + x))

/-- The ordinary Petz derivative before the flag is traced out. -/
def recoveryVariation (t ε η : ℝ) : Joint :=
  joint fun s => qubit 0 (recoveryEntry t (flagBias ε s) η) (recoveryEntry t (flagBias ε s) η) 0

private theorem block_deriv (t : ℝ) {x η : ℝ} (hη : 0 < η)
    (hb : 0 < 1 - x) (hd : 0 < 1 + x) :
    HasDerivAt (fun c => (1 / 2 : ℝ) •
      (normalizedRoot x η c * sourceMarginal t c * (normalizedRoot x η c)ᴴ))
      (qubit 0 (recoveryEntry t x η) (recoveryEntry t x η) 0) 0 := by
  obtain ⟨hK₀, hK⟩ := normalizedRoot_firstVariation hη hb hd
  obtain ⟨hP₀, hP⟩ := source_firstVariation t
  let D := η * Real.sqrt (1 - x) + Real.sqrt (1 + x)
  let K' := qubit 0 (2 * x * η / D) (2 * x / D) 0
  have hKstar : HasDerivAt (fun c => (normalizedRoot x η c)ᴴ) K'ᴴ 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hK j) i).star
  have hprod := matrix_mul_deriv (matrix_mul_deriv hK hP) hKstar
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have he := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hprod i) j).const_smul (1 / 2 : ℝ)
  convert he using 1
  simp only [hK₀, hP₀, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [recoveryEntry, K', qubit, ← show D = η * Real.sqrt (1 - x) + Real.sqrt (1 + x)
      from rfl, Complex.real_smul] <;> ring

/-- The derivative in the joint matrix space, and the derivative of its physical input. -/
theorem physical_firstVariation (t : ℝ) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 16)
    (hη : 0 < η) :
    HasDerivAt (fun c => partialTracePetz (reference ε η c) (sourceMarginal t c))
      (recoveryVariation t ε η) 0 ∧
    HasDerivAt (sourceMarginal t) (qubit 0 (1 - t - t) (1 - t - t) 0) 0 := by
  refine ⟨?_, (source_firstVariation t).2⟩
  have hnear := reference_near hε hε' hη
  refine HasDerivAt.congr_of_eventuallyEq
    (f := fun c => joint fun s => (1 / 2 : ℝ) •
      (normalizedRoot (flagBias ε s) η c * sourceMarginal t c *
        (normalizedRoot (flagBias ε s) η c)ᴴ)) ?_ ?_
  · apply hasDerivAt_pi.mpr
    rintro ⟨i, s⟩
    apply hasDerivAt_pi.mpr
    rintro ⟨j, u⟩
    by_cases hsu : s = u
    · subst u
      obtain ⟨hb, hd⟩ := flag_pos hε hε' s
      simpa [recoveryVariation, Matrix.blockDiagonal_apply] using
        hasDerivAt_pi.mp (hasDerivAt_pi.mp (block_deriv t hη hb hd) i) j
    · simpa [recoveryVariation, Matrix.blockDiagonal_apply, hsu] using
        hasDerivAt_const (0 : ℝ) (0 : ℂ)
  · filter_upwards [hnear] with c hc
    exact recovery_blocks hη hc (sourceMarginal t c)

/-- The physical source with the retained state in both flags, with flag weights one half. -/
def duplicatedSource (t c : ℝ) : Joint :=
  joint fun _ : Fin 2 => (1 / 2 : ℝ) • sourceMarginal t c

private theorem source_marginal_posDef {t c : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 8)
    (hc : |c| ≤ 1 / 2) : (sourceMarginal t c).PosDef := by
  have hsq : c ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_abs c, mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ 1 / 2 + |c| by positivity)]
  have hroot : (Real.sqrt (1 - 4 * c ^ 2)) ^ 2 = 1 - 4 * c ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ profile c := by unfold profile; positivity
  have hr : profile c * (1 - profile c) = c ^ 2 := by
    unfold profile
    nlinarith only [hroot]
  have hj : 0 < 1 - t - t := by linarith
  unfold sourceMarginal
  apply symmetric_posDef (add_pos_of_pos_of_nonneg ht (mul_nonneg hj.le hr0))
  calc
    _ = t * (1 - t) + (1 - t - t) ^ 2 * (profile c * (1 - profile c) - c ^ 2) := by ring
    _ = t * (1 - t) := by rw [hr, sub_self, mul_zero, add_zero]
    _ > 0 := mul_pos ht (by linarith)

private theorem source_noncommute {t ε η c : ℝ} (ht' : t ≤ 1 / 8)
    (hε : 0 < ε) (hη : 0 < η) (hc : c ≠ 0) :
    ¬ Commute (duplicatedSource t c) (reference ε η c) := by
  let j := 1 - t - t
  let d := Real.sqrt (1 - 4 * c ^ 2)
  have hj : 0 < j := by dsimp [j]; linarith
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hscale : 0 < scale η := by unfold scale; positivity
  intro h
  have hblock (s : Fin 2) :
      ((1 / 2 : ℝ) • sourceMarginal t c) * referenceBlock ε η c s =
        referenceBlock ε η c s * ((1 / 2 : ℝ) • sourceMarginal t c) := by
    have he :
        joint (fun _ : Fin 2 => (1 / 2 : ℝ) • sourceMarginal t c) *
            joint (referenceBlock ε η c) =
          joint (referenceBlock ε η c) *
            joint (fun _ : Fin 2 => (1 / 2 : ℝ) • sourceMarginal t c) := h.eq
    rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul] at he
    exact congrFun (Matrix.blockDiagonal_inj.mp he) s
  have he (s : Fin 2) :
      j * c * (scale η / 4) *
        ((1 - η ^ 2) + flagBias ε s * (1 + η ^ 2 + 2 * η * d)) = 0 := by
    have hentry := congrArg (fun A : Qubit => (A 0 1).re) (hblock s)
    simp only [referenceBlock, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two] at hentry
    simp [sourceMarginal, profile, unscaledBlock, qubit, Complex.real_smul, pow_two] at hentry
    dsimp [j, d]
    simp only [pow_two]
    linear_combination hentry
  have hz (s : Fin 2) : (1 - η ^ 2) + flagBias ε s * (1 + η ^ 2 + 2 * η * d) = 0 :=
    (mul_eq_zero.mp (he s)).resolve_left
      (mul_ne_zero (mul_ne_zero hj.ne' hc) (div_pos hscale (by norm_num)).ne')
  have hp := hz 0
  have hm := hz 1
  simp only [flagBias, Matrix.cons_val_zero, Matrix.cons_val_one] at hp hm
  have hpos : 0 < ε * (1 + η ^ 2 + 2 * η * d) := by positivity
  linarith

/-- A faithful, noncommuting source on the exact physical fibre near the base. -/
theorem physical_source_on_fibre {t ε η : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 16) (hη : 0 < η) :
    ∀ᶠ c in 𝓝 (0 : ℝ),
      (duplicatedSource t c).PosDef ∧ (duplicatedSource t c).trace = 1 ∧
      partialTraceRight (duplicatedSource t c) = sourceMarginal t c ∧
      (reference ε η c).PosDef ∧ (reference ε η c).trace = 1 ∧
      partialTraceRight (reference ε η c) = referenceMarginal η ∧
      (c ≠ 0 → ¬ Commute (duplicatedSource t c) (reference ε η c)) := by
  have hnear : ∀ᶠ c in 𝓝 (0 : ℝ), |c| ≤ 1 / 2 :=
    (continuous_abs.continuousAt.eventually (gt_mem_nhds (by norm_num))).mono
      fun _ h => h.le
  filter_upwards [hnear, reference_near hε hε' hη] with c hc href
  have hm : partialTraceRight (duplicatedSource t c) = sourceMarginal t c := by
    change marginal _ = _
    rw [marginal_eq_sum, Fin.sum_univ_two, ← add_smul]
    norm_num
  refine ⟨joint_posDef _ (fun _ => (source_marginal_posDef ht ht' hc).smul (by norm_num)),
    ?_, hm, joint_posDef _ href, ?_, reference_marginal ε η c, source_noncommute ht' hε hη⟩
  · rw [← D5.S3.Quantum.Information.PartialTraceMutualInformation.trace_partialTraceRight, hm]
    simp [sourceMarginal, qubit, Matrix.trace_fin_two]
  · rw [← D5.S3.Quantum.Information.PartialTraceMutualInformation.trace_partialTraceRight,
      reference_marginal]
    simp [referenceMarginal, Matrix.trace_diagonal, Fin.sum_univ_two, scale]
    push_cast
    have h : (1 : ℂ) + (η : ℂ) ^ 2 ≠ 0 := by
      exact_mod_cast (show (1 : ℝ) + η ^ 2 ≠ 0 by positivity)
    field_simp
    ring

end D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation
