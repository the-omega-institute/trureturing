import D5.S3.Quantum.Recovery.PetzLikelihoodHessianIntegration
import D5.S3.Quantum.Recovery.PetzSingularInputLimit
import D5.S3.Quantum.Divergence.UmegakiBKMPath
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry

/-!
# Actual likelihood entropy loss for ordinary Petz recovery

The scalar and matrix paths use the same likelihood interpolation. The
trace corrections cancel by equality of the scalar and matrix likelihood
masses at each time. This works for subnormalized ensembles, including
those obtained by adjoining a unit-likelihood label on the kernel of the
output reference. The fixed-reference entropy is continuous at a
singular terminal output.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix Set
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open QuadraticBayesRiskGeometricPetz
open PetzLikelihoodHessianIntegration
open LikelihoodRationalTailSeparation (mixtureScore)
open PetzOverlapEntropyDerivative (faithfulRelativeEntropy)
open D5.S3.Divergence.LogDerivTrace (logDeriv)
open D5.S3.Divergence.AudenaertBinaryHolevoBound (log_hasDerivAt_affine_of_lower_bound)
open D5.S3.Quantum.Divergence.TraceEntropyCalculus (hasDerivAt_trace_mul_log)
open D5.S3.Quantum.Divergence.UmegakiBKMPath
  (common_floor continuousOn_logDeriv_of_floor reindexStar reindex_logDeriv)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport spectralInverseSqrt)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
  (spectral_sqrt_normalization support_of_nonneg_le_smul)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer (spectral_sqrt_inverse_products)
open D5.S3.Quantum.Lieb.PositiveMapJensen (cfc_intertwining)

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace

namespace PetzActualLikelihoodEntropy

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- Classical likelihood entropy minus the actual output Umegaki expression. -/
def actualEntropyLoss (A : ι → Matrix n n ℂ) (lam : ι → ℝ) : ℝ :=
  (∑ i, (trace (A i)).re * (lam i * Real.log (lam i))) -
    faithfulRelativeEntropy (scoreMoment A lam) (∑ i, A i)

private def weight (a t : ℝ) : ℝ := 1 - t + t * a

private def direction (A : ι → Matrix n n ℂ) (lam : ι → ℝ) : Matrix n n ℂ :=
  scoreMoment A lam - ∑ i, A i

private def outputPath (A : ι → Matrix n n ℂ) (lam : ι → ℝ) (t : ℝ) : Matrix n n ℂ :=
  (∑ i, A i) + t • direction A lam

private def lossPath (A : ι → Matrix n n ℂ) (lam : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ i, (trace (A i)).re * (weight (lam i) t * Real.log (weight (lam i) t))) -
    faithfulRelativeEntropy (outputPath A lam t) (∑ i, A i)

private def velocity (A : ι → Matrix n n ℂ) (lam : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ i, ((trace (A i)).re * (lam i - 1)) * (Real.log (weight (lam i) t) + 1)) -
    tracePair (direction A lam)
      (CFC.log (outputPath A lam t) + 1 - CFC.log (∑ i, A i))

private def hessian (A : ι → Matrix n n ℂ) (lam : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ i, (trace (A i)).re * ((lam i - 1) ^ 2 / weight (lam i) t)) -
    tracePair (direction A lam) (logDeriv (outputPath A lam t) (direction A lam))

private def tracePairCLM (X : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap.comp
    (mulLeftLinearMap n ℝ X).toContinuousLinearMap)

private theorem tracePairCLM_apply (X Y : Matrix n n ℂ) :
    tracePairCLM X Y = tracePair X Y := rfl

omit [DecidableEq n] in
private theorem trace_scoreMoment (A : ι → Matrix n n ℂ) (c : ι → ℝ) :
    (trace (scoreMoment A c)).re = ∑ i, c i * (trace (A i)).re := by
  simp only [scoreMoment, Matrix.trace_sum, Matrix.trace_smul, Complex.real_smul,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

omit [Fintype n] [DecidableEq n] in
private theorem direction_eq_sum (A : ι → Matrix n n ℂ) (lam : ι → ℝ) :
    direction A lam = ∑ i, (lam i - 1) • A i := by
  simp [direction, scoreMoment, sub_smul, Finset.sum_sub_distrib]

omit [DecidableEq n] in
/-- The input likelihood mass, weighted by the output block traces, equals
the matrix likelihood mass. In particular, normalization is optional. -/
theorem likelihoodMass_eq_trace (A : ι → Matrix n n ℂ) (lam : ι → ℝ) :
    (∑ i, (trace (A i)).re * lam i) = (trace (scoreMoment A lam)).re := by
  simpa only [mul_comm] using (trace_scoreMoment A lam).symm

private theorem weight_pos {a t : ℝ} (ha : 0 ≤ a) (ht : t ∈ Ico (0 : ℝ) 1) :
    0 < weight a t :=
  add_pos_of_pos_of_nonneg (sub_pos.mpr ht.2) (mul_nonneg ht.1 ha)

private theorem weight_hasDerivAt (a t : ℝ) :
    HasDerivAt (weight a) (a - 1) t := by
  rw [show a - 1 = -1 + 1 * a by ring]
  exact ((hasDerivAt_id t).const_sub 1).add ((hasDerivAt_id t).mul_const a)

omit [Fintype n] [DecidableEq n] in
private theorem outputPath_eq_sum (A : ι → Matrix n n ℂ) (lam : ι → ℝ) (t : ℝ) :
    outputPath A lam t = ∑ i, weight (lam i) t • A i := by
  rw [outputPath, direction_eq_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp [weight]
  module

omit [Fintype n] [DecidableEq n] in
private theorem outputPath_isHermitian (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (t : ℝ) :
    (outputPath A lam t).IsHermitian := by
  rw [outputPath_eq_sum, Matrix.IsHermitian, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ =>
    ((hA i).isHermitian.smul (IsSelfAdjoint.all (weight (lam i) t))).eq

omit [Fintype n] [DecidableEq n] in
private theorem outputPath_posDef (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hQ : (∑ i, A i).PosDef) (hlam : ∀ i, 0 ≤ lam i)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (outputPath A lam t).PosDef := by
  have hp : (scoreMoment A lam).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ => (hA i).smul (hlam i)
  have he : outputPath A lam t = (1 - t) • (∑ i, A i) + t • scoreMoment A lam := by
    unfold outputPath direction
    module
  rw [he]
  exact (hQ.smul (sub_pos.mpr ht.2)).add_posSemidef (hp.smul ht.1)

private theorem log_affine_calculus (B H : Matrix n n ℂ) (t : ℝ)
    (ht : (B + t • H).PosDef)
    (hNear : ∀ᶠ u in 𝓝 t, (1 / 2 : ℝ) • (B + t • H) ≤ B + u • H) :
    HasDerivAt (fun u : ℝ => CFC.log (B + u • H)) (logDeriv (B + t • H) H) t ∧
      ContinuousAt (fun u : ℝ => logDeriv (B + u • H) H) t := by
  let e := Fintype.equivFin n
  let R := reindexStar e
  let E := (Matrix.reindexLinearEquiv ℝ ℂ e e).toContinuousLinearEquiv
  have hAffine (u : ℝ) : R (B + u • H) = R B + u • R H := by
    simp only [map_add, map_smul]
  have hPos : (R B + t • R H).PosDef := by
    rw [← hAffine]
    exact ht.submatrix e.symm.injective
  obtain ⟨c, hc, hcB, _⟩ := common_floor _ _ hPos hPos
  have hfloor : ∀ᶠ u in 𝓝 t, (c / 2) • 1 ≤ R B + u • R H := by
    filter_upwards [hNear] with u hu
    have hu' : R ((1 / 2 : ℝ) • (B + t • H)) ≤ R (B + u • H) := by
      apply Matrix.le_iff.mpr
      rw [← map_sub]
      exact (Matrix.le_iff.mp hu).submatrix e.symm
    simp only [map_smul, hAffine] at hu'
    rw [← one_div_mul_eq_div, ← smul_smul]
    exact (smul_le_smul_of_nonneg_left hcB (by norm_num : 0 ≤ (1 / 2 : ℝ))).trans hu'
  let s : Set ℝ := {u | (c / 2) • 1 ≤ R B + u • R H}
  have hs : s ∈ 𝓝 t := hfloor
  have hd := log_hasDerivAt_affine_of_lower_bound (R B) (R H) t (c / 2) (half_pos hc) s hs
    (fun _ hu => hu)
  have hcont := ((continuousOn_logDeriv_of_floor (R B) (R H) s (c / 2) (half_pos hc)
    (fun _ hu => hu))
    t (mem_of_mem_nhds hs)).continuousAt hs
  have hLog (u : ℝ) : CFC.log (R B + u • R H) = E (CFC.log (B + u • H)) := by
    rw [← hAffine]
    exact Matrix.cfc_reindex (A := B + u • H) Real.log e
  have hDerivative (u : ℝ) :
      logDeriv (R B + u • R H) (R H) = E (logDeriv (B + u • H) H) := by
    rw [← hAffine]
    exact (reindex_logDeriv e (B + u • H) H).symm
  simp only [hLog, hDerivative] at hd hcont
  constructor
  · have h := E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun u => E.symm (E (CFC.log (B + u • H))))
      (E.symm (E (logDeriv (B + t • H) H))) t at h
    simpa only [E.symm_apply_apply] using h
  · have h := E.symm.continuous.continuousAt.comp hcont
    change ContinuousAt (fun u => E.symm (E (logDeriv (B + u • H) H))) t at h
    simpa only [E.symm_apply_apply] using h

private theorem lossPath_zero (A : ι → Matrix n n ℂ) (lam : ι → ℝ) :
    lossPath A lam 0 = 0 := by
  simp [lossPath, weight, outputPath, faithfulRelativeEntropy]

private theorem lossPath_one (A : ι → Matrix n n ℂ) (lam : ι → ℝ) :
    lossPath A lam 1 = actualEntropyLoss A lam := by
  have hZ : outputPath A lam 1 = scoreMoment A lam := by
    simp only [outputPath, one_smul, direction]
    abel
  simp [lossPath, actualEntropyLoss, weight, hZ]

private theorem velocity_zero (A : ι → Matrix n n ℂ) (lam : ι → ℝ) :
    velocity A lam 0 = 0 := by
  have hmass : (trace (direction A lam)).re =
      ∑ i, (trace (A i)).re * (lam i - 1) := by
    simpa only [direction_eq_sum, scoreMoment] using
      (likelihoodMass_eq_trace A (fun i => lam i - 1)).symm
  have hlog : CFC.log (∑ i, A i) + 1 - CFC.log (∑ i, A i) = 1 := by abel
  have hZ : outputPath A lam 0 = ∑ i, A i := by simp [outputPath]
  simp [velocity, weight, hZ, hlog, tracePair, hmass]

private theorem continuous_lossPath (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) : Continuous (lossPath A lam) := by
  refine Continuous.sub (continuous_finsetSum _ fun i _ => ?_) ?_
  · exact continuous_const.mul
      (Real.continuous_mul_log.comp (by unfold weight; fun_prop))
  · exact PetzSingularInputLimit.continuous_fixedReference_traceLog
      (by unfold outputPath; fun_prop) (outputPath_isHermitian A lam hA) (∑ i, A i)

private theorem lossPath_hasDerivAt (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hQ : (∑ i, A i).PosDef) (hlam : ∀ i, 0 ≤ lam i)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (lossPath A lam) (velocity A lam t) t := by
  let Q := ∑ i, A i
  let H := direction A lam
  let Z := outputPath A lam
  have hZ : HasDerivAt Z H t := by
    change HasDerivAt (fun u : ℝ => Q + u • H) H t
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const H).const_add Q
  have hSelf := hasDerivAt_trace_mul_log Z H t hZ
    (Eventually.of_forall (outputPath_isHermitian A lam hA))
    (outputPath_posDef A lam hA hQ hlam ht)
  have hCross := hZ.mul_const (CFC.log Q)
  let T : Matrix n n ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  have hOut : HasDerivAt (fun u => faithfulRelativeEntropy (Z u) Q)
      (tracePair H (CFC.log (Z t) + 1 - CFC.log Q)) t := by
    have h := hSelf.sub (T.hasFDerivAt.comp_hasDerivAt t hCross)
    change HasDerivAt (fun u => (Z u * CFC.log (Z u)).trace.re -
        (Z u * CFC.log Q).trace.re)
        ((H * (CFC.log (Z t) + 1)).trace.re - (H * CFC.log Q).trace.re) t at h
    simpa only [faithfulRelativeEntropy, tracePair, Matrix.mul_sub, Matrix.trace_sub,
      Complex.sub_re, CFC.log] using h
  have hIn : HasDerivAt
      (fun u => ∑ i, (trace (A i)).re * (weight (lam i) u * Real.log (weight (lam i) u)))
      (∑ i, ((trace (A i)).re * (lam i - 1)) * (Real.log (weight (lam i) t) + 1)) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have hd := (Real.hasDerivAt_mul_log (weight_pos (hlam i) ht).ne').comp t
      (weight_hasDerivAt (lam i) t)
    convert hd.const_mul (trace (A i)).re using 1
    · funext u
      simp only [Function.comp_apply]
    · ring
  exact hIn.sub hOut

private theorem outputPath_log_calculus (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hQ : (∑ i, A i).PosDef) (hlam : ∀ i, 0 ≤ lam i)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (fun u => CFC.log (outputPath A lam u))
      (logDeriv (outputPath A lam t) (direction A lam)) t ∧
    ContinuousAt (fun u => logDeriv (outputPath A lam u) (direction A lam)) t := by
  have hWeights : ∀ᶠ u in 𝓝 t, ∀ i, weight (lam i) t / 2 ≤ weight (lam i) u := by
    apply eventually_all.mpr
    intro i
    exact (continuousAt_const.eventually_lt (weight_hasDerivAt (lam i) t).continuousAt
      (half_lt_self (weight_pos (hlam i) ht))).mono fun _ hu => hu.le
  have hNear : ∀ᶠ u in 𝓝 t, (1 / 2 : ℝ) • outputPath A lam t ≤ outputPath A lam u := by
    filter_upwards [hWeights] with u hu
    rw [outputPath_eq_sum, outputPath_eq_sum, Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [smul_smul, one_div_mul_eq_div]
    exact smul_le_smul_of_nonneg_right (hu i) (hA i).nonneg
  exact log_affine_calculus (∑ i, A i) (direction A lam) t
    (outputPath_posDef A lam hA hQ hlam ht) hNear

private theorem velocity_hasDerivAt (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hQ : (∑ i, A i).PosDef) (hlam : ∀ i, 0 ≤ lam i)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (velocity A lam) (hessian A lam t) t := by
  have hIn : HasDerivAt
      (fun u => ∑ i, ((trace (A i)).re * (lam i - 1)) * (Real.log (weight (lam i) u) + 1))
      (∑ i, (trace (A i)).re * ((lam i - 1) ^ 2 / weight (lam i) t)) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have hd := (Real.hasDerivAt_log (weight_pos (hlam i) ht).ne').comp t
      (weight_hasDerivAt (lam i) t)
    convert (hd.add_const 1).const_mul ((trace (A i)).re * (lam i - 1)) using 1
    all_goals simp only [Function.comp_def, div_eq_mul_inv]
    all_goals ring
  have hd := (outputPath_log_calculus A lam hA hQ hlam ht).1
  have hOut : HasDerivAt (fun u => tracePair (direction A lam)
      (CFC.log (outputPath A lam u) + 1 - CFC.log (∑ i, A i)))
      (tracePair (direction A lam) (logDeriv (outputPath A lam t) (direction A lam))) t := by
    simpa only [Function.comp_def, tracePairCLM_apply] using
      (tracePairCLM (direction A lam)).hasFDerivAt.comp_hasDerivAt t
        ((hd.add_const 1).sub_const (CFC.log (∑ i, A i)))
  exact hIn.sub hOut

private theorem continuousOn_hessian (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hQ : (∑ i, A i).PosDef) (hlam : ∀ i, 0 ≤ lam i)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) : ContinuousOn (hessian A lam) (Icc 0 u) := by
  have hsub : Icc (0 : ℝ) u ⊆ Ico 0 1 := fun _ ht => ⟨ht.1, ht.2.trans_lt hu.2⟩
  refine ContinuousOn.sub (continuousOn_finsetSum _ fun i _ => ?_) ?_
  · exact continuousOn_const.mul (continuousOn_const.div
      (by unfold weight; fun_prop) fun t ht => (weight_pos (hlam i) (hsub ht)).ne')
  · intro t ht
    simpa only [Function.comp_def, tracePairCLM_apply] using
      ((tracePairCLM (direction A lam)).continuous.continuousAt.comp
        (outputPath_log_calculus A lam hA hQ hlam (hsub ht)).2).continuousWithinAt

private theorem hessian_eq_tilted_bkmDeficit (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    hessian A lam t =
      bkmDeficit (fun i => (1 - t + t * lam i) • A i) (fun i => mixtureScore (lam i) t) := by
  let A' : ι → Matrix n n ℂ := fun i => weight (lam i) t • A i
  let d : ι → ℝ := fun i => mixtureScore (lam i) t
  have hd (i : ι) : d i = (lam i - 1) / weight (lam i) t := rfl
  have hMoment : scoreMoment A' d = direction A lam := by
    rw [scoreMoment, direction_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [A']
    rw [smul_smul, hd, div_mul_cancel₀ _ (weight_pos (hlam i) ht).ne']
  change _ = bkmDeficit A' d
  rw [hessian, bkmDeficit, hMoment, ← outputPath_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [A', hd, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp [(weight_pos (hlam i) ht).ne']

/-- The actual loss dominates two thirds of the geometric risk on square-root
likelihoods. The output reference is faithful and the terminal output may
be singular. -/
theorem two_thirds_geometricRisk_sqrt_le_actualEntropyLoss_of_posDef
    (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hlam : ∀ i, 0 ≤ lam i)
    (hQ : (∑ i, A i).PosDef) :
    (2 / 3) * geometricRisk A (fun i => Real.sqrt (lam i)) ≤ actualEntropyLoss A lam := by
  rw [← lossPath_one]
  refine geometricRisk_sqrt_le_of_bkm_hessian A hA hQ lam hlam
    (lossPath A lam) (velocity A lam) (hessian A lam)
    (continuous_lossPath A lam hA).continuousAt (lossPath_zero A lam) (velocity_zero A lam)
    (fun _ ht => (lossPath_hasDerivAt A lam hA hQ hlam ht).hasDerivWithinAt)
    (fun _ ht => (velocity_hasDerivAt A lam hA hQ hlam ht).hasDerivWithinAt)
    (fun _ hu => continuousOn_hessian A lam hA hQ hlam hu) ?_
  exact fun _ ht => (hessian_eq_tilted_bkmDeficit A lam hlam ht).symm.le

/-- Functional calculus on the old support and the added identity block. -/
private theorem cfc_add_orthogonal_projection (X E : Matrix n n ℂ)
    (hX : X.IsHermitian) (hE : E.IsHermitian) (hEE : E * E = E)
    (hXE : X * E = 0) (hEX : E * X = 0) (f : ℝ → ℝ) (hf0 : f 0 = 0) :
    cfc f (X + E) = cfc f X + f 1 • E ∧ E * cfc f X = 0 := by
  have hZero : E * cfc f X = 0 := by
    have h := cfc_intertwining 0 X Matrix.isHermitian_zero hX E
      (by rw [Matrix.zero_mul, hEX]) f
    simpa only [cfc_apply_zero, hf0, map_zero, Matrix.zero_mul] using h.symm
  have hOld : (X + E) * (1 - E) = (1 - E) * X := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hXE, hEX, hEE, sub_zero, zero_add, add_sub_cancel_right]
  have hNew : (X + E) * E = E * 1 := by
    simp only [Matrix.add_mul, Matrix.mul_one, hXE, hEE, zero_add]
  have hOldCfc := cfc_intertwining (X + E) X (hX.add hE) hX (1 - E) hOld f
  have hNewCfc := cfc_intertwining (X + E) 1 (hX.add hE)
    Matrix.isHermitian_one E hNew f
  refine ⟨?_, hZero⟩
  calc
    cfc f (X + E) = cfc f (X + E) * (1 - E) + cfc f (X + E) * E := by
      rw [← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
    _ = cfc f X + f 1 • E := by
      rw [hOldCfc, hNewCfc, cfc_apply_one, Algebra.algebraMap_eq_smul_one]
      simp only [Matrix.sub_mul, Matrix.one_mul, hZero, sub_zero,
        Matrix.mul_smul, Matrix.mul_one]

private def dummyEnsemble (A : ι → Matrix n n ℂ) : Option ι → Matrix n n ℂ
  | none => 1 - spectralSupport (∑ i, A i)
  | some i => A i

private def dummyLikelihood (lam : ι → ℝ) : Option ι → ℝ
  | none => 1
  | some i => lam i

private theorem dummyEnsemble_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (i : Option ι) :
    (dummyEnsemble A i).PosSemidef := by
  cases i with
  | none => exact (pgmEffects_isPOVM A hA).1 none
  | some i => exact hA i

private theorem dummyEnsemble_sum (A : ι → Matrix n n ℂ) :
    (∑ i, dummyEnsemble A i) = (∑ i, A i) + (1 - spectralSupport (∑ i, A i)) := by
  rw [Fintype.sum_option]
  exact add_comm _ _

private theorem dummyEnsemble_moment (A : ι → Matrix n n ℂ) (lam : ι → ℝ) :
    scoreMoment (dummyEnsemble A) (dummyLikelihood lam) =
      scoreMoment A lam + (1 - spectralSupport (∑ i, A i)) := by
  rw [scoreMoment, Fintype.sum_option]
  simp [dummyEnsemble, dummyLikelihood, scoreMoment, add_comm]

/-- Adding the identity on the kernel leaves a faithful total reference. -/
private theorem dummyEnsemble_sum_posDef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) : (∑ i, dummyEnsemble A i).PosDef := by
  rw [dummyEnsemble_sum]
  let Q := ∑ i, A i
  have hQ : Q.PosSemidef := Matrix.posSemidef_sum Finset.univ fun i _ => hA i
  let f : ℝ → ℝ := fun x => x + (1 - if x = 0 then 0 else 1)
  have he : cfc f Q = Q + (1 - spectralSupport Q) := by
    rw [show f = (fun x : ℝ => x + (1 - if x = 0 then 0 else 1)) from rfl,
      cfc_add Q _ _ (Q.finite_real_spectrum.continuousOn _) (Q.finite_real_spectrum.continuousOn _),
      cfc_id' ℝ Q hQ.isHermitian.isSelfAdjoint,
      cfc_sub _ _ Q (Q.finite_real_spectrum.continuousOn _) (Q.finite_real_spectrum.continuousOn _),
      cfc_const 1 Q hQ.isHermitian.isSelfAdjoint]
    rfl
  change (Q + (1 - spectralSupport Q)).PosDef
  rw [← he]
  apply Matrix.IsStrictlyPositive.posDef
  refine (cfc_isStrictlyPositive_iff f Q (Q.finite_real_spectrum.continuousOn f)
    hQ.isHermitian.isSelfAdjoint).2 ?_
  intro x hx
  have hx0 : 0 ≤ x := by
    rw [hQ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hQ.eigenvalues_nonneg i
  by_cases hz : x = 0
  · simp [f, hz]
  · simpa [f, hz] using lt_of_le_of_ne hx0 (Ne.symm hz)

private theorem dummyEnsemble_orthogonal (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (i : ι) :
    (1 - spectralSupport (∑ j, A j)) * A i = 0 ∧
      A i * (1 - spectralSupport (∑ j, A j)) = 0 := by
  let Q := ∑ j, A j
  obtain ⟨-, -, hP, -, -, -, hPQ, -⟩ := spectral_sqrt_normalization Q
    (Matrix.posSemidef_sum Finset.univ fun j _ => hA j)
  have hle : A i ≤ Q :=
    Finset.single_le_sum (fun j _ => (hA j).nonneg) (Finset.mem_univ i)
  obtain ⟨hPA, hAP⟩ := support_of_nonneg_le_smul Q (A i) (spectralSupport Q)
    hP hPQ (hA i) 1 (by simpa only [one_smul] using hle)
  change (1 - spectralSupport Q) * A i = 0 ∧ A i * (1 - spectralSupport Q) = 0
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hPA, hAP,
    sub_self, and_self]

private theorem dummy_orthogonal_moment (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (c : ι → ℝ) :
    (1 - spectralSupport (∑ j, A j)) * scoreMoment A c = 0 ∧
      scoreMoment A c * (1 - spectralSupport (∑ j, A j)) = 0 := by
  simp only [scoreMoment, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    (dummyEnsemble_orthogonal A hA _).1, (dummyEnsemble_orthogonal A hA _).2,
    smul_zero, Finset.sum_const_zero, and_self]

private theorem dummy_projection (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) :
    IsStarProjection (1 - spectralSupport (∑ i, A i)) := by
  obtain ⟨-, -, hP, hPP, -, -, -, -⟩ := spectral_sqrt_normalization (∑ i, A i)
    (Matrix.posSemidef_sum Finset.univ fun i _ => hA i)
  have hProj : IsStarProjection (spectralSupport (∑ i, A i)) := ⟨hPP, hP⟩
  exact hProj.one_sub

/-- The dummy label contributes zero input entropy. The two output logarithms
are unchanged, and the new block annihilates both of them. -/
theorem actualEntropyLoss_dummy (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hlam : ∀ i, 0 ≤ lam i) :
    actualEntropyLoss (dummyEnsemble A) (dummyLikelihood lam) = actualEntropyLoss A lam := by
  let Q := ∑ i, A i
  let p := scoreMoment A lam
  let E := 1 - spectralSupport Q
  have hProj : IsStarProjection E := dummy_projection A hA
  have hQ : Q.PosSemidef := Matrix.posSemidef_sum Finset.univ fun i _ => hA i
  have hp : p.PosSemidef := Matrix.posSemidef_sum Finset.univ fun i _ => (hA i).smul (hlam i)
  have hpm : E * p = 0 ∧ p * E = 0 := dummy_orthogonal_moment A hA lam
  have hQm : E * Q = 0 ∧ Q * E = 0 := by
    simpa only [scoreMoment, one_smul] using dummy_orthogonal_moment A hA (fun _ => 1)
  obtain ⟨hpLog, hpZero⟩ := cfc_add_orthogonal_projection p E hp.isHermitian hProj.2 hProj.1
    hpm.2 hpm.1 Real.log Real.log_zero
  obtain ⟨hQLog, hQZero⟩ := cfc_add_orthogonal_projection Q E hQ.isHermitian hProj.2 hProj.1
    hQm.2 hQm.1 Real.log Real.log_zero
  unfold actualEntropyLoss
  rw [Fintype.sum_option, dummyEnsemble_moment, dummyEnsemble_sum]
  change
    ((trace E).re * (1 * Real.log 1) +
      ∑ i, (trace (A i)).re * (lam i * Real.log (lam i))) -
        faithfulRelativeEntropy (p + E) (Q + E) =
    (∑ i, (trace (A i)).re * (lam i * Real.log (lam i))) - faithfulRelativeEntropy p Q
  simp only [faithfulRelativeEntropy, hpLog, hQLog, Real.log_one, zero_smul,
    add_zero, mul_zero, zero_add, Matrix.add_mul, Matrix.mul_sub, hpZero, hQZero]

private theorem dummy_pgmEffects (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) :
    pgmEffects (dummyEnsemble A) (some none) = 1 - spectralSupport (∑ i, A i) ∧
      ∀ j : ι, pgmEffects (dummyEnsemble A) (some (some j)) = pgmEffects A (some j) := by
  let Q := ∑ i, A i
  let E := 1 - spectralSupport Q
  let W := spectralInverseSqrt Q
  let W' := spectralInverseSqrt (Q + E)
  have hQ : Q.PosSemidef := Matrix.posSemidef_sum Finset.univ fun i _ => hA i
  have hProj : IsStarProjection E := dummy_projection A hA
  have hOrth : E * Q = 0 ∧ Q * E = 0 := by
    simpa only [scoreMoment, one_smul] using dummy_orthogonal_moment A hA (fun _ => 1)
  obtain ⟨hW', hEW⟩ := cfc_add_orthogonal_projection Q E hQ.isHermitian hProj.2 hProj.1
    hOrth.2 hOrth.1 (fun x => (Real.sqrt x)⁻¹) (by simp)
  have hW' : W' = W + E := by
    simpa [W', W, spectralInverseSqrt] using hW'
  have hEW : E * W = 0 := hEW
  have hWE : W * E = 0 := by
    obtain ⟨-, -, -, hWP⟩ := spectral_sqrt_inverse_products Q hQ
    change W * (1 - spectralSupport Q) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, hWP, sub_self]
  have hEE : E * E = E := hProj.1
  constructor
  · simp only [pgmEffects]
    rw [dummyEnsemble_sum]
    change W' * E * W' = E
    rw [hW', Matrix.add_mul, hWE, hEE, zero_add, Matrix.mul_add, hEW, hEE, zero_add]
  · intro j
    simp only [pgmEffects]
    rw [dummyEnsemble_sum]
    change W' * A j * W' = W * A j * W
    obtain ⟨hEA, hAE⟩ := dummyEnsemble_orthogonal A hA j
    rw [hW', Matrix.add_mul, hEA, add_zero, Matrix.mul_add, Matrix.mul_assoc W (A j) E,
      hAE, mul_zero, add_zero]

/-- The dummy is an isolated label in the PGM pair weights. Its diagonal
pair has zero squared score difference. -/
theorem geometricRisk_dummy (A : ι → Matrix n n ℂ) (c : ι → ℝ) (z : ℝ)
    (hA : ∀ i, (A i).PosSemidef) :
    geometricRisk (dummyEnsemble A) (fun i => i.elim z c) = geometricRisk A c := by
  let E := 1 - spectralSupport (∑ i, A i)
  obtain ⟨hDummy, hOld⟩ := dummy_pgmEffects A hA
  have hLeft (j : ι) :
      tracePair (1 - spectralSupport (∑ i, A i)) (pgmEffects A (some j)) = 0 := by
    change tracePair E (pgmEffects A (some j)) = 0
    obtain ⟨-, -, hPW, -⟩ := spectral_sqrt_inverse_products (∑ i, A i)
      (Matrix.posSemidef_sum Finset.univ fun i _ => hA i)
    have hEW : E * spectralInverseSqrt (∑ i, A i) = 0 := by
      simp only [E, Matrix.sub_mul, Matrix.one_mul, hPW, sub_self]
    simp only [pgmEffects, tracePair, ← Matrix.mul_assoc, hEW, zero_mul,
      Matrix.trace_zero, Complex.zero_re]
  have hRight (i : ι) : tracePair (A i) (1 - spectralSupport (∑ j, A j)) = 0 := by
    simp only [tracePair, (dummyEnsemble_orthogonal A hA i).2, Matrix.trace_zero,
      Complex.zero_re]
  rw [geometricRisk_eq_half_pairwise _ _ (dummyEnsemble_posSemidef A hA),
    geometricRisk_eq_half_pairwise A c hA]
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, dummyEnsemble,
    hDummy, hOld, hLeft, hRight,
    sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, Finset.sum_const_zero, zero_add]

/-- The actual entropy loss dominates two thirds of the geometric risk for
every finite PSD ensemble. Both total output matrices may be singular. -/
theorem two_thirds_geometricRisk_sqrt_le_actualEntropyLoss
    (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hlam : ∀ i, 0 ≤ lam i) :
    (2 / 3) * geometricRisk A (fun i => Real.sqrt (lam i)) ≤ actualEntropyLoss A lam := by
  have hlam' (i : Option ι) : 0 ≤ dummyLikelihood lam i := by
    cases i with
    | none => exact zero_le_one
    | some i => exact hlam i
  have h := two_thirds_geometricRisk_sqrt_le_actualEntropyLoss_of_posDef
    (dummyEnsemble A) (dummyLikelihood lam) (dummyEnsemble_posSemidef A hA) hlam'
    (dummyEnsemble_sum_posDef A hA)
  have hScores : (fun i => Real.sqrt (dummyLikelihood lam i)) =
      fun i : Option ι => i.elim (Real.sqrt 1) (fun j => Real.sqrt (lam j)) := by
    funext i
    cases i <;> rfl
  rw [hScores, geometricRisk_dummy _ _ _ hA, actualEntropyLoss_dummy A lam hA hlam] at h
  exact h

end PetzActualLikelihoodEntropy
