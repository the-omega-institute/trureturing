import D5.S3.Quantum.Recovery.PetzSingularInputLimit
import D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

/-!
# Ordinary partial-trace Petz recovery with a singular reference

Depolarize both input states with the same weight. Partial trace sends the
normalized identity to the normalized identity on the retained system.
Supported data processing supplies the upper bounds for both entropy limits.
The faithful retained reference supplies a positive spectral floor for its
inverse square root along the path.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Filter
open scoped Topology CStarAlgebra ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight partialTraceRight_add partialTraceRight_kronecker
    marginalRight density_posSemidef)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (act partialTraceRight_smul state_nonempty)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
  (extended_quantum_relative_entropy_channel_dpi)
open D5.S3.Quantum.Divergence.UmegakiSupportedNoise
  (tendsto_finiteTraceLogRelativeEntropy_of_noise)
open D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
  (depolarizingChannel act_depolarizingChannel)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt)
open PetzPhysicalAmplitude (ordinaryPetz lift)
open PetzSingularInputLimit (faithfulMixture faithfulMixture_posDef finiteTraceLog_eq_raw)

namespace PetzCommonUniformNoise

universe u

section UniformNoise

variable {n : Type u} [Fintype n] [DecidableEq n]

private abbrev raw (X : DensityState n) : Matrix n n ℂ :=
  CStarMatrix.ofMatrix.symm X.1

/-- The normalized identity on the indicated matrix algebra. -/
def uniformMatrix (n : Type u) [Fintype n] [DecidableEq n] : Matrix n n ℂ :=
  (Fintype.card n : ℝ)⁻¹ • 1

private lemma density_nonempty (X : DensityState n) : Nonempty n :=
  state_nonempty ⟨density_posSemidef X, X.2.2⟩

private lemma card_cast_pos [Nonempty n] : 0 < (Fintype.card n : ℝ) :=
  Nat.cast_pos.mpr Fintype.card_pos

private lemma uniformMatrix_posDef [Nonempty n] : (uniformMatrix n).PosDef :=
  Matrix.PosDef.one.smul (inv_pos.mpr (card_cast_pos (n := n)))

private def uniformState (n : Type u) [Fintype n] [DecidableEq n] [Nonempty n] :
    DensityState n := by
  refine ⟨CStarMatrix.ofMatrix (uniformMatrix n),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (uniformMatrix_posDef (n := n)).posSemidef.nonneg, ?_⟩
  change (uniformMatrix n).trace = 1
  rw [uniformMatrix, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]
  exact_mod_cast (inv_mul_cancel₀ (card_cast_pos (n := n)).ne')

private abbrev Weight := Set.Ioo (0 : ℝ) 1

/-- The CPTP uniform replacement mixture on the open unit interval, extended
by the original state to define a total path. -/
def uniformNoise (X : DensityState n) (t : ℝ) : DensityState n :=
  if ht : t ∈ Set.Ioo (0 : ℝ) 1 then (depolarizingChannel n (⟨t, ht⟩ : Weight)).mapState X
  else X

private lemma uniformNoise_apply (X : DensityState n) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    uniformNoise X t = (depolarizingChannel n (⟨t, ht⟩ : Weight)).mapState X := by
  rw [uniformNoise, dif_pos ht]

theorem uniformNoise_raw (X : DensityState n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    raw (uniformNoise X t) = (1 - t) • raw X + t • uniformMatrix n := by
  rw [uniformNoise_apply X ht]
  change act (depolarizingChannel n (⟨t, ht⟩ : Weight)) (raw X) = _
  rw [act_depolarizingChannel, show (raw X).trace = 1 from X.2.2, one_smul] <;> rfl

private lemma uniformNoise_posDef (X : DensityState n) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) : (raw (uniformNoise X t)).PosDef := by
  letI : Nonempty n := density_nonempty X
  rw [uniformNoise_raw X ht]
  exact faithfulMixture_posDef (density_posSemidef X) (uniformMatrix_posDef (n := n))
    ht.1 ht.2.le

private lemma supported_channel_dpi (C : QuantumChannel n n) (X Y : DensityState n)
    (hXY : SupportContained X Y) :
    SupportContained (C.mapState X) (C.mapState Y) ∧
      finiteTraceLogRelativeEntropy (C.mapState X) (C.mapState Y) ≤
        finiteTraceLogRelativeEntropy X Y := by
  letI : Nonempty n := density_nonempty X
  have hDPI := extended_quantum_relative_entropy_channel_dpi C X Y
  have hOut := (extendedQuantumRelativeEntropy_ne_top_iff _ _).mp
    (ne_top_of_le_ne_top ((extendedQuantumRelativeEntropy_ne_top_iff X Y).mpr hXY) hDPI)
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support hXY,
    extendedQuantumRelativeEntropy_eq_coe_of_support hOut] at hDPI
  exact ⟨hOut, WithTop.coe_le_coe.mp hDPI⟩

/-- The actual finite branch converges under common uniform replacement.
This specializes the common-noise argument in `UmegakiChannelSupportedExtension`. -/
theorem tendsto_finiteTraceLog_uniformNoise (X Y : DensityState n)
    (hXY : SupportContained X Y) :
    Tendsto (fun t : ℝ => finiteTraceLogRelativeEntropy (uniformNoise X t) (uniformNoise Y t))
      (𝓝[>] 0) (𝓝 (finiteTraceLogRelativeEntropy X Y)) := by
  letI : Nonempty n := density_nonempty X
  have hNear : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT zero_lt_one
  have hDPI : ∀ᶠ t : ℝ in 𝓝[>] 0,
      SupportContained (uniformNoise X t) (uniformNoise Y t) ∧
        finiteTraceLogRelativeEntropy (uniformNoise X t) (uniformNoise Y t) ≤
          finiteTraceLogRelativeEntropy X Y := by
    filter_upwards [hNear] with t ht
    rw [uniformNoise_apply X ht, uniformNoise_apply Y ht]
    exact supported_channel_dpi (depolarizingChannel n ⟨t, ht⟩) X Y hXY
  apply tendsto_finiteTraceLogRelativeEntropy_of_noise X Y (uniformState n) (uniformState n)
    (uniformNoise X) (uniformNoise Y) hXY
  · filter_upwards [hNear] with t ht
    exact uniformNoise_raw X ht
  · filter_upwards [hNear] with t ht
    exact uniformNoise_raw Y ht
  · exact hDPI.mono (fun _ h => h.1)
  · exact hDPI.mono (fun _ h => h.2)

private lemma tendsto_raw_uniformNoise (X : DensityState n) :
    Tendsto (fun t : ℝ => raw (uniformNoise X t)) (𝓝[>] 0) (𝓝 (raw X)) := by
  let path (t : ℝ) := (1 - t) • raw X + t • uniformMatrix n
  have hpath : Continuous path := by unfold path; fun_prop
  have hlim : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (raw X)) := by
    simpa [path] using (hpath.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply Tendsto.congr' _ hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  exact (uniformNoise_raw X ht).symm

end UniformNoise

section Marginal

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The retained noise state is the partial trace of the full noise state. -/
theorem partialTraceRight_uniformMatrix [Nonempty B] :
    partialTraceRight (uniformMatrix (A × B)) = uniformMatrix A := by
  unfold uniformMatrix
  have htrace : partialTraceRight (1 : Matrix (A × B) (A × B) ℂ) =
      (Fintype.card B : ℂ) • (1 : Matrix A A ℂ) := by
    calc
      _ = partialTraceRight (Matrix.kronecker (1 : Matrix A A ℂ) (1 : Matrix B B ℂ)) :=
        congrArg partialTraceRight (Matrix.one_kronecker_one (m := A) (n := B) (α := ℂ)).symm
      _ = _ := by rw [partialTraceRight_kronecker, Matrix.trace_one]
  rw [partialTraceRight_smul, htrace]
  have hcast : (Fintype.card B : ℂ) • (1 : Matrix A A ℂ) =
      (Fintype.card B : ℝ) • (1 : Matrix A A ℂ) := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [hcast, smul_smul, Fintype.card_prod, Nat.cast_mul, _root_.mul_inv_rev,
    mul_comm ((Fintype.card B : ℝ)⁻¹) ((Fintype.card A : ℝ)⁻¹),
    inv_mul_cancel_right₀ (card_cast_pos (n := B)).ne']

/-- The actual marginal follows the same uniform replacement channel on the
retained algebra. -/
theorem marginalRight_uniformNoise (X : DensityState (A × B)) (t : ℝ) :
    marginalRight (uniformNoise X t) = uniformNoise (marginalRight X) t := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · letI : Nonempty B := Nonempty.map Prod.snd (density_nonempty X)
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change partialTraceRight (raw (uniformNoise X t)) =
      raw (uniformNoise (marginalRight X) t)
    rw [uniformNoise_raw X ht, uniformNoise_raw (marginalRight X) ht, partialTraceRight_add,
      partialTraceRight_smul, partialTraceRight_smul, partialTraceRight_uniformMatrix] <;> rfl
  · simp only [uniformNoise, dif_neg ht]

/-- The entropy of the actual noisy marginals converges to the actual retained
entropy when the retained reference is faithful. -/
theorem tendsto_marginal_finiteTraceLog_uniformNoise (X Y : DensityState (A × B))
    (hY : (partialTraceRight (raw Y)).PosDef) :
    Tendsto (fun t : ℝ =>
      finiteTraceLogRelativeEntropy (marginalRight (uniformNoise X t))
        (marginalRight (uniformNoise Y t))) (𝓝[>] 0)
      (𝓝 (finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y))) := by
  simpa only [marginalRight_uniformNoise] using
    (tendsto_finiteTraceLog_uniformNoise (marginalRight X) (marginalRight Y)
      (support_of_posDef (marginalRight X) (marginalRight Y) hY))

end Marginal

section InverseSqrt

variable {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]

set_option maxHeartbeats 800000 in
/-- In the fixed eigenbasis of a positive definite matrix, mixing with a positive
scalar identity keeps all noisy eigenvalues on a common positive interval. -/
theorem tendsto_spectralInverseSqrt_identityMixture {Q : Matrix n n ℂ}
    (hQ : Q.PosDef) {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => spectralInverseSqrt
      ((1 - t) • Q + t • (k • (1 : Matrix n n ℂ))))
      (𝓝[>] 0) (𝓝 (spectralInverseSqrt Q)) := by
  let U := hQ.isHermitian.eigenvectorUnitary
  let E := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  let eigenvalues := hQ.isHermitian.eigenvalues
  let mixedEigenvalues (t : ℝ) (i : n) := (1 - t) * eigenvalues i + t * k
  let D (r : n → ℝ) : Matrix n n ℂ := diagonal (fun i => (r i : ℂ))
  let path (t : ℝ) := (1 - t) • Q + t • (k • (1 : Matrix n n ℂ))
  have hE : Continuous (fun M : Matrix n n ℂ => E M) := by
    change Continuous (fun M : Matrix n n ℂ =>
      (U : Matrix n n ℂ) * M * (star U : Matrix n n ℂ))
    fun_prop
  have hEsmul (a : ℝ) (M : Matrix n n ℂ) : E (a • M) = a • E M :=
    (E.toAlgEquiv.restrictScalars ℝ).toLinearEquiv.map_smul a M
  have hQdiag : Q = E (D eigenvalues) := by
    simpa only [E, U, D, eigenvalues, Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
      using hQ.isHermitian.spectral_theorem
  have hPath (t : ℝ) : path t = E (D (mixedEigenvalues t)) := by
    have hdiag : (1 - t) • D eigenvalues + t • (k • (1 : Matrix n n ℂ)) = D (mixedEigenvalues t) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D, mixedEigenvalues, Matrix.diagonal_apply, Matrix.one_apply, Complex.real_smul]
      · simp [D, Matrix.diagonal_apply, Matrix.one_apply, hij]
    calc
      path t = E ((1 - t) • D eigenvalues + t • (k • (1 : Matrix n n ℂ))) := by
        rw [map_add, hEsmul, hEsmul, hEsmul, map_one, ← hQdiag] <;> rfl
      _ = E (D (mixedEigenvalues t)) := congrArg (fun M => E M) hdiag
  have hInverse (t : ℝ) : spectralInverseSqrt (path t) =
      E (D (fun i => (Real.sqrt (mixedEigenvalues t i))⁻¹)) := by
    let f (x : ℝ) := (Real.sqrt x)⁻¹
    have hd : IsSelfAdjoint (D (mixedEigenvalues t)) := by
      apply Matrix.IsHermitian.isSelfAdjoint
      apply Matrix.isHermitian_diagonal_of_self_adjoint
      ext i
      simp [Pi.star_apply]
    unfold spectralInverseSqrt
    rw [hPath]
    change cfc f (E (D (mixedEigenvalues t))) = _
    exact (StarAlgHomClass.map_cfc E f (D (mixedEigenvalues t))
      ((D (mixedEigenvalues t)).finite_real_spectrum.continuousOn f) hE hd (hd.map E)).symm.trans
      (congrArg (fun M => E M) (cfc_diagonal f (mixedEigenvalues t)))
  let m : ℝ := Finset.univ.inf' Finset.univ_nonempty eigenvalues
  have hm : 0 < m :=
    (Finset.lt_inf'_iff _).mpr (fun i _ => hQ.eigenvalues_pos i)
  let ε := min m k
  have hε : 0 < ε := lt_min hm hk
  have hFloor (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : n) : ε ≤ mixedEigenvalues t i := by
    have hEigenvalue : ε ≤ eigenvalues i :=
      (min_le_left m k).trans (Finset.inf'_le eigenvalues (Finset.mem_univ i))
    have hk' : ε ≤ k := min_le_right _ _
    calc
      ε = (1 - t) * ε + t * ε := by ring
      _ ≤ mixedEigenvalues t i :=
        add_le_add (mul_le_mul_of_nonneg_left hEigenvalue (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left hk' ht.1)
  let f (x : ℝ) := (Real.sqrt (max ε x))⁻¹
  have hf : Continuous f :=
    (Real.continuous_sqrt.comp (continuous_const.max continuous_id)).inv₀
      (fun x => (Real.sqrt_pos.mpr (hε.trans_le (le_max_left ε x))).ne')
  let clipped (t : ℝ) := E (D (fun i => f (mixedEigenvalues t i)))
  have hDiagonal : Continuous (fun t : ℝ => D (fun i => f (mixedEigenvalues t i))) := by
    apply continuous_matrix
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [D, Matrix.diagonal_apply_eq]
      exact Complex.continuous_ofReal.comp (hf.comp (by unfold mixedEigenvalues; fun_prop))
    · simpa only [D, Matrix.diagonal_apply_ne _ hij] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  have hClip : Continuous clipped := hE.comp hDiagonal
  have hEq (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      clipped t = spectralInverseSqrt (path t) := by
    rw [hInverse]
    exact congrArg (fun r => E (D r))
      (funext fun i => by simp only [f, max_eq_right (hFloor t ht i)])
  have hzero : clipped 0 = spectralInverseSqrt Q := by
    simpa [path] using hEq 0 ⟨le_rfl, zero_le_one⟩
  have hlim : Tendsto clipped (𝓝[>] (0 : ℝ)) (𝓝 (spectralInverseSqrt Q)) := by
    rw [← hzero]
    exact (hClip.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply Tendsto.congr' _ hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  exact hEq t ⟨ht.1.le, ht.2.le⟩

end InverseSqrt

section PetzLimit

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The inverse square root of the actual retained noisy reference converges to
that of the faithful retained reference. -/
theorem tendsto_retained_inverseSqrt_uniformNoise (Y : DensityState (A × B))
    (hY : (partialTraceRight (raw Y)).PosDef) :
    Tendsto (fun t : ℝ => spectralInverseSqrt (partialTraceRight (raw (uniformNoise Y t))))
      (𝓝[>] 0) (𝓝 (spectralInverseSqrt (partialTraceRight (raw Y)))) := by
  letI : Nonempty A := density_nonempty (marginalRight Y)
  apply Tendsto.congr' _ (tendsto_spectralInverseSqrt_identityMixture hY
    (inv_pos.mpr (card_cast_pos (n := A))))
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  change spectralInverseSqrt ((1 - t) • partialTraceRight (raw Y) + t • uniformMatrix A) =
    spectralInverseSqrt (raw (marginalRight (uniformNoise Y t)))
  rw [marginalRight_uniformNoise, uniformNoise_raw (marginalRight Y) ht] <;> rfl

private lemma continuous_sqrtMatrix {n : Type u} [Fintype n] [DecidableEq n]
    {T : Type*} [TopologicalSpace T] {M : T → Matrix n n ℂ}
    (hM : Continuous M) (hHerm : ∀ t, (M t).IsHermitian) :
    Continuous (fun t => cfc Real.sqrt (M t)) :=
  Continuous.cfc_of_mem_nhdsSet Real.sqrt (s := Set.univ)
    (by simp (config := { congrConsts := false })) hM
    (fun t => (hHerm t).isSelfAdjoint) Real.continuous_sqrt.continuousOn

private lemma tendsto_sqrt_uniformNoise (Y : DensityState (A × B)) :
    Tendsto (fun t : ℝ => cfc Real.sqrt (raw (uniformNoise Y t)))
      (𝓝[>] 0) (𝓝 (cfc Real.sqrt (raw Y))) := by
  let path (t : ℝ) := (1 - t) • raw Y + t • uniformMatrix (A × B)
  letI : Nonempty (A × B) := density_nonempty Y
  have hHerm (t : ℝ) : (path t).IsHermitian :=
    ((density_posSemidef Y).isHermitian.smul (show IsSelfAdjoint (1 - t) from rfl)).add
      ((uniformMatrix_posDef (n := A × B)).isHermitian.smul (show IsSelfAdjoint t from rfl))
  have hcont := continuous_sqrtMatrix (M := path) (by unfold path; fun_prop) hHerm
  have hlim : Tendsto (fun t => cfc Real.sqrt (path t)) (𝓝[>] (0 : ℝ))
      (𝓝 (cfc Real.sqrt (raw Y))) := by
    simpa [path] using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply Tendsto.congr' _ hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  rw [uniformNoise_raw Y ht] <;> rfl

private lemma continuous_partialTraceRight :
    Continuous (partialTraceRight : Matrix (A × B) (A × B) ℂ → Matrix A A ℂ) := by
  apply continuous_matrix
  intro i j
  unfold partialTraceRight
  exact continuous_finsetSum _ fun b _ => continuous_apply_apply (i, b) (j, b)

private lemma continuous_lift : Continuous (lift (A := A) (B := B)) := by
  apply continuous_matrix
  rintro ⟨i, b⟩ ⟨j, d⟩
  simp only [lift, Matrix.kronecker_apply]
  exact (continuous_apply_apply i j).mul continuous_const

private lemma continuous_traceNorm {n : Type u} [Fintype n] [DecidableEq n] :
    Continuous (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm : Matrix n n ℂ → ℝ) := by
  have hGram : Continuous (fun M : Matrix n n ℂ => Mᴴ * M) := by fun_prop
  have hSqrt := continuous_sqrtMatrix hGram Matrix.isHermitian_conjTranspose_mul_self
  have hTrace : Continuous (fun M : Matrix n n ℂ => M.trace.re) := by
    unfold Matrix.trace
    fun_prop
  have hFormula (M : Matrix n n ℂ) :
      D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm M =
        (cfc Real.sqrt (Mᴴ * M)).trace.re := by
    change (CFC.sqrt (Mᴴ * M)).trace.re = _
    rw [CFC.sqrt_eq_real_sqrt (Mᴴ * M) M.posSemidef_conjTranspose_mul_self.nonneg,
      cfcₙ_eq_cfc (a := Mᴴ * M) Real.continuous_sqrt.continuousOn Real.sqrt_zero]
  rw [funext hFormula]
  exact hTrace.comp hSqrt

/-- The ordinary Petz output on the actual noisy input marginal tends to the
ordinary Petz output of the unregularized pair. -/
theorem tendsto_ordinaryPetz_uniformNoise (X Y : DensityState (A × B))
    (hY : (partialTraceRight (raw Y)).PosDef) :
    Tendsto (fun t : ℝ => ordinaryPetz (raw (uniformNoise Y t))
      (partialTraceRight (raw (uniformNoise X t)))) (𝓝[>] 0)
      (𝓝 (ordinaryPetz (raw Y) (partialTraceRight (raw X)))) := by
  have hInput := tendsto_raw_uniformNoise X
  have hMarginal := (continuous_partialTraceRight (A := A) (B := B)).continuousAt.tendsto.comp
    hInput
  have hInv := tendsto_retained_inverseSqrt_uniformNoise Y hY
  have hSqrt := tendsto_sqrt_uniformNoise Y
  have hLift := (continuous_lift (A := A) (B := B)).continuousAt.tendsto.comp
    ((hInv.mul hMarginal).mul hInv)
  exact (hSqrt.mul hLift).mul hSqrt

/-- The squared trace norm of the actual ordinary Petz error has the same
right limit along the common uniform noise. -/
theorem tendsto_traceNorm_sub_ordinaryPetz_sq_uniformNoise (X Y : DensityState (A × B))
    (hY : (partialTraceRight (raw Y)).PosDef) :
    Tendsto (fun t : ℝ => traceNorm (raw (uniformNoise X t) -
        ordinaryPetz (raw (uniformNoise Y t))
          (partialTraceRight (raw (uniformNoise X t)))) ^ 2) (𝓝[>] 0)
      (𝓝 (traceNorm (raw X - ordinaryPetz (raw Y) (partialTraceRight (raw X))) ^ 2)) :=
  (continuous_traceNorm.continuousAt.tendsto.comp
    ((tendsto_raw_uniformNoise X).sub (tendsto_ordinaryPetz_uniformNoise X Y hY))).pow 2

private lemma faithful_bound (X Y : DensityState (A × B))
    (hX : (raw X).PosDef) (hY : (raw Y).PosDef) :
    traceNorm (raw X - ordinaryPetz (raw Y) (partialTraceRight (raw X))) ^ 2 ≤
      (8 * (1 + (Fintype.card A : ℝ) ^ 2)) *
        (finiteTraceLogRelativeEntropy X Y -
          finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y)) := by
  rw [finiteTraceLog_eq_raw X Y, finiteTraceLog_eq_raw (marginalRight X) (marginalRight Y)]
  exact PetzFaithfulDimensionRecovery.traceNorm_sub_ordinaryPetz_sq_le hX hY X.2.2

/-- The ordinary Petz error for partial trace with a supported input and faithful
retained reference is bounded by `8 * (1 + (card A)^2)` times the actual
full-minus-marginal Umegaki entropy. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_finiteTraceLog (X Y : DensityState (A × B))
    (hXY : SupportContained X Y)
    (hY : (partialTraceRight (CStarMatrix.ofMatrix.symm Y.1)).PosDef) :
    traceNorm (CStarMatrix.ofMatrix.symm X.1 -
        ordinaryPetz (CStarMatrix.ofMatrix.symm Y.1)
          (partialTraceRight (CStarMatrix.ofMatrix.symm X.1))) ^ 2 ≤
      (8 * (1 + (Fintype.card A : ℝ) ^ 2)) *
        (finiteTraceLogRelativeEntropy X Y -
          finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y)) := by
  let c : ℝ := 8 * (1 + (Fintype.card A : ℝ) ^ 2)
  have hEntropy := (tendsto_finiteTraceLog_uniformNoise X Y hXY).sub
    (tendsto_marginal_finiteTraceLog_uniformNoise X Y hY)
  have hRight := (tendsto_const_nhds (x := c)).mul hEntropy
  letI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  apply le_of_tendsto_of_tendsto (tendsto_traceNorm_sub_ordinaryPetz_sq_uniformNoise X Y hY) hRight
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  exact faithful_bound (uniformNoise X t) (uniformNoise Y t)
    (uniformNoise_posDef X ht) (uniformNoise_posDef Y ht)

end PetzLimit

end PetzCommonUniformNoise
