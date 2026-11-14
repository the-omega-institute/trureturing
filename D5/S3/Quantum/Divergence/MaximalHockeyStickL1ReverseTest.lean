/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest
   mirror-E: none(waiver:source-class-bridge)
   anchors: []
   utility: none
   digest: Actual L1 source atomization and finite-output operational equivalence. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickL1Preparation
import D5.S3.Analytic.Convexity.MeasurableFiniteMoments

universe u

noncomputable section

open Matrix MeasureTheory Set Filter
open scoped ComplexOrder ENNReal NNReal Matrix.Norms.Elementwise MatrixOrder
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open D5.S3.Quantum.Divergence.MaximalHockeyStickL1Preparation

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

local instance matrixMeasurableSpace (I : Type*) : MeasurableSpace (Matrix I I ℂ) :=
  inferInstanceAs (MeasurableSpace (I → I → ℂ))

local instance matrixContinuousENorm (I : Type*) [Fintype I] :
    ContinuousENorm (Matrix I I ℂ) :=
  inferInstanceAs (ContinuousENorm (I → I → ℂ))

local instance matrixPseudoMetrizable (I : Type*) [Fintype I] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix I I ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (I → I → ℂ))

variable {α n : Type*} [MeasurableSpace α] [Fintype n] [DecidableEq n]

private theorem finite_cost_real_moment {μ : Measure α} [SFinite μ]
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {p q : α → ℝ} (hpm : Measurable p) (hqm : Measurable q)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hpn : ∀ᵐ a ∂μ, 0 ≤ p a) (hqn : ∀ᵐ a ∂μ, 0 ≤ q a)
    (hc : closedPerspectiveCost hf μ p q ≠ ⊤) :
    ∃ c : α → ℝ, Integrable c μ ∧
      (∀ᵐ a ∂μ, closedPerspective hf (p a) (q a) = (c a : EReal)) ∧
      closedPerspectiveCost hf μ p q = ((∫ a, c a ∂μ : ℝ) : EReal) := by
  let a : α → ℝ := fun x => f 1 * q x + rightDeriv f 1 * (p x - q x)
  let R : α → ℝ≥0∞ := fun x => curvatureRemainder hf (p x) (q x)
  have hai : Integrable a μ := (hq.const_mul _).add ((hp.sub hq).const_mul _)
  have hRm : Measurable R := by
    have hn : Measurable (fun z : α × Positive =>
        ENNReal.ofReal ((z.2 : ℝ) * q z.1 - p z.1)) :=
      ((measurable_subtype_coe.comp measurable_snd).mul (hqm.comp measurable_fst) |>.sub
        (hpm.comp measurable_fst)).ennreal_ofReal
    have hp' : Measurable (fun z : α × Positive =>
        ENNReal.ofReal (p z.1 - (z.2 : ℝ) * q z.1)) :=
      ((hpm.comp measurable_fst).sub
        ((measurable_subtype_coe.comp measurable_snd).mul (hqm.comp measurable_fst))).ennreal_ofReal
    dsimp [R, curvatureRemainder]
    exact hn.lintegral_prod_right'.add hp'.lintegral_prod_right'
  have hRf : (∫⁻ x, R x ∂μ) ≠ ∞ := by
    intro h
    apply hc
    simp [closedPerspectiveCost, R, h]
  have hRae : ∀ᵐ x ∂μ, R x < ∞ := ae_lt_top hRm hRf
  have hRi : Integrable (fun x => (R x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hRm.aemeasurable hRf
  let c : α → ℝ := fun x => if R x = ∞ then 0 else a x + (R x).toReal
  have hceq : c =ᵐ[μ] (fun x => a x + (R x).toReal) :=
    hRae.mono fun x hx => by simp [c, hx.ne]
  have hci : Integrable c μ := (hai.add hRi).congr hceq.symm
  refine ⟨c, hci, ?_, ?_⟩
  · filter_upwards [hRae, hpn, hqn] with x hx hpx hqx
    rw [closedPerspective_eq_affine_add_curvature hf hpx hqx]
    change (a x : EReal) + (R x : EReal) = _
    rw [← EReal.coe_ennreal_toReal hx.ne, ← EReal.coe_add]
    simp [c, hx.ne]
  · change ((∫ x, a x ∂μ : ℝ) : EReal) + (∫⁻ x, R x ∂μ : ℝ≥0∞) = _
    rw [integral_congr_ae hceq, integral_add hai hRi,
      integral_toReal hRm.aemeasurable hRae, EReal.coe_add,
      EReal.coe_ennreal_toReal hRf]

/-- Exact atomization of two density-valued L1 moments and one specified real
closed-perspective cost. Selected points lie in the finite-cost conull set. -/
theorem finite_density_atomization {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {τ : α → Matrix n n ℂ} (hτm : Measurable τ)
    (hτ : ∀ a, (τ a).PosSemidef ∧ (τ a).trace = 1)
    {p q c : α → ℝ} (hp : Integrable p μ) (hq : Integrable q μ) (hc : Integrable c μ)
    (hpn : ∀ᵐ a ∂μ, 0 ≤ p a) (hqn : ∀ᵐ a ∂μ, 0 ≤ q a)
    (hcost : ∀ᵐ a ∂μ, closedPerspective hf (p a) (q a) = (c a : EReal)) :
    ∃ (k : ℕ) (R : ReverseTest (∫ a, p a • τ a ∂μ) (∫ a, q a • τ a ∂μ) k),
      ∑ i, closedPerspective hf (R.p i) (R.q i) = ((∫ a, c a ∂μ : ℝ) : EReal) := by
  classical
  have hb (a : α) : ‖τ a‖ ≤ 1 := by
    simpa [(hτ a).2] using psd_norm_le_trace (hτ a).1
  have hpi : Integrable (fun a => p a • τ a) μ :=
    hp.smul_bdd 1 hτm.aestronglyMeasurable (Eventually.of_forall hb)
  have hqi : Integrable (fun a => q a • τ a) μ :=
    hq.smul_bdd 1 hτm.aestronglyMeasurable (Eventually.of_forall hb)
  let F : α → (Matrix n n ℂ × Matrix n n ℂ) × ℝ :=
    fun a => ((p a • τ a, q a • τ a), c a)
  have hF : Integrable F μ := (hpi.prodMk hqi).prodMk hc
  let good : Set α := {a | 0 ≤ p a ∧ 0 ≤ q a ∧
    closedPerspective hf (p a) (q a) = (c a : EReal)}
  have hgood : ∀ᵐ a ∂μ, a ∈ good := by
    filter_upwards [hpn, hqn, hcost] with a hp hq hc
    exact ⟨hp, hq, hc⟩
  obtain ⟨k, w, a, hw, _, ha, he⟩ :=
    D5.S3.Analytic.Convexity.MeasurableFiniteMoments.finite_moments μ hF hgood
  have hleft : ∑ i, (w i * p (a i)) • τ (a i) = ∫ a, p a • τ a ∂μ := by
    have h := congrArg (fun z : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => z.1.1) he
    simpa only [F, Prod.fst_sum, Prod.smul_fst, fst_integral hF,
      fst_integral (hpi.prodMk hqi), mul_smul] using h
  have hright : ∑ i, (w i * q (a i)) • τ (a i) = ∫ a, q a • τ a ∂μ := by
    have h := congrArg (fun z : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => z.1.2) he
    simpa only [F, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      fst_integral hF, snd_integral (hpi.prodMk hqi), mul_smul] using h
  have hreal : ∑ i, w i * c (a i) = ∫ a, c a ∂μ := by
    have h := congrArg (fun z : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => z.2) he
    simpa only [F, Prod.snd_sum, Prod.smul_snd, snd_integral hF, smul_eq_mul] using h
  let R : ReverseTest (∫ a, p a • τ a ∂μ) (∫ a, q a • τ a ∂μ) k :=
    { p := fun i => w i * p (a i)
      q := fun i => w i * q (a i)
      p_nonneg := fun i => mul_nonneg (hw i) (ha i).1
      q_nonneg := fun i => mul_nonneg (hw i) (ha i).2.1
      state := fun i => ⟨CStarMatrix.ofMatrix (τ (a i)),
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (hτ (a i)).1.nonneg), (hτ (a i)).2⟩
      prepares_left := by simpa only [Equiv.symm_apply_apply] using hleft
      prepares_right := by simpa only [Equiv.symm_apply_apply] using hright }
  refine ⟨k, R, ?_⟩
  change (∑ i, closedPerspective hf (w i * p (a i)) (w i * q (a i))) = _
  simp_rw [closedPerspective_homogeneous hf _ _ _ (hw _), (ha _).2.2, ← EReal.coe_mul]
  exact_mod_cast hreal

/-- Every actual positive complex-linear trace-preserving test on a finite
measure source has a finite preparation preserving its two outputs and exactly
the one specified real-finite convex closed-perspective cost. -/
theorem finite_measure_atomization [Nonempty n] {μ : Measure α} [IsFiniteMeasure μ]
    (Γ : PositiveTracePreservingL1Map (n := n) μ)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {p q : α → ℝ} (hpm : Measurable p) (hqm : Measurable q)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hpn : ∀ᵐ a ∂μ, 0 ≤ p a) (hqn : ∀ᵐ a ∂μ, 0 ≤ q a)
    (hc : closedPerspectiveCost hf μ p q ≠ ⊤) :
    ∃ (k : ℕ) (R : ReverseTest
      (Γ.toLinearMap (hp.ofReal.toL1 (fun a => (p a : ℂ))))
      (Γ.toLinearMap (hq.ofReal.toL1 (fun a => (q a : ℂ)))) k),
      ∑ i, closedPerspective hf (R.p i) (R.q i) = closedPerspectiveCost hf μ p q := by
  classical
  let G := Γ.realRestriction
  have hpG (h : α →₁[μ] ℝ) (hh : ∀ᵐ a ∂μ, 0 ≤ h a) : (G h).PosSemidef := by
    apply Γ.positive
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL h, hh] with a ha hh
    simpa [ha] using hh
  have htG (h : α →₁[μ] ℝ) : (G h).trace = ((∫ a, h a ∂μ : ℝ) : ℂ) := by
    change (Γ.toLinearMap (Complex.ofRealCLM.compLpL 1 μ h)).trace = _
    rw [Γ.trace_preserving,
      integral_congr_ae (Complex.ofRealCLM.coeFn_compLpL h)]
    simpa only [Complex.ofRealCLM_apply] using (integral_complex_ofReal (f := fun a => h a) (μ := μ))
  let j₀ : n := Classical.choice inferInstance
  let base : Matrix n n ℂ := diagonal (Pi.single j₀ 1)
  have hb : base.PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hbt : base.trace = 1 := by simp [base, Matrix.trace_diagonal]
  obtain ⟨τ, hτm, _, hτ, he⟩ := finite_source_representation G hpG htG base hb hbt
  have hprepare (u : α → ℝ) (hu : Integrable u μ) :
      Γ.toLinearMap (hu.ofReal.toL1 (fun a => (u a : ℂ))) = ∫ a, u a • τ a ∂μ := by
    have hlift : Complex.ofRealCLM.compLpL 1 μ (hu.toL1 u) =
        hu.ofReal.toL1 (fun a => (u a : ℂ)) := by
      apply Lp.ext
      filter_upwards [Complex.ofRealCLM.coeFn_compLpL (hu.toL1 u), hu.coeFn_toL1,
        (hu.ofReal : Integrable (fun a => (u a : ℂ)) μ).coeFn_toL1] with a hcomp hu hcomplex
      exact hcomp.trans (by rw [hu]; exact hcomplex.symm)
    calc
      Γ.toLinearMap (hu.ofReal.toL1 (fun a => (u a : ℂ))) = G (hu.toL1 u) := by
        change _ = Γ.toLinearMap (Complex.ofRealCLM.compLpL 1 μ (hu.toL1 u))
        rw [hlift]
      _ = ∫ a, hu.toL1 u a • τ a ∂μ := he _
      _ = _ := integral_congr_ae (hu.coeFn_toL1.mono fun a ha => by dsimp only; rw [ha])
  obtain ⟨c, hci, hcr, hce⟩ := finite_cost_real_moment hf hpm hqm hp hq hpn hqn hc
  obtain ⟨k, R, hR⟩ := finite_density_atomization hf hτm hτ hp hq hci hpn hqn hcr
  rw [hprepare p hp, hprepare q hq]
  exact ⟨k, R, hR.trans hce.symm⟩

/-- Reweight by p+q to obtain a genuinely finite source, then atomize the
specified finite cost. No optimizer or positive-definiteness premise is used. -/
theorem source_atomization_nonempty [Nonempty n] {μ : Measure α}
    (Γ : PositiveTracePreservingL1Map (n := n) μ)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {p q : α → ℝ} (hpm : Measurable p) (hqm : Measurable q)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hpn : ∀ᵐ a ∂μ, 0 ≤ p a) (hqn : ∀ᵐ a ∂μ, 0 ≤ q a)
    (hc : closedPerspectiveCost hf μ p q ≠ ⊤) :
    ∃ (k : ℕ) (R : ReverseTest
      (Γ.toLinearMap (hp.ofReal.toL1 (fun a => (p a : ℂ))))
      (Γ.toLinearMap (hq.ofReal.toL1 (fun a => (q a : ℂ)))) k),
      ∑ i, closedPerspective hf (R.p i) (R.q i) = closedPerspectiveCost hf μ p q := by
  classical
  let r : α → ℝ≥0 := fun a => (p a).toNNReal + (q a).toNNReal
  have hrm : Measurable r := hpm.real_toNNReal.add hqm.real_toNNReal
  have hri : Integrable (fun a => (r a : ℝ)) μ :=
    hp.real_toNNReal.add hq.real_toNNReal
  have hrfin : (∫⁻ a, (r a : ℝ≥0∞) ∂μ) ≠ ∞ := by
    have he := ofReal_integral_eq_lintegral_ofReal hri
      (Eventually.of_forall fun a => (r a).coe_nonneg)
    simp only [ENNReal.ofReal_coe_nnreal] at he
    rw [← he]
    exact ENNReal.ofReal_ne_top
  let ν := μ.withDensity (fun a => (r a : ℝ≥0∞))
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hrfin
  let p' : α → ℝ := fun a => p a / (r a : ℝ)
  let q' : α → ℝ := fun a => q a / (r a : ℝ)
  have hp'm : Measurable p' := hpm.div hrm.coe_nnreal_real
  have hq'm : Measurable q' := hqm.div hrm.coe_nnreal_real
  have hrpq : ∀ᵐ a ∂μ, (r a : ℝ) = p a + q a := by
    filter_upwards [hpn, hqn] with a hpa hqa
    simp [r, Real.toNNReal_of_nonneg hpa, Real.toNNReal_of_nonneg hqa]
  have hmul : ∀ᵐ a ∂μ, (r a : ℝ) * p' a = p a ∧ (r a : ℝ) * q' a = q a := by
    filter_upwards [hrpq, hpn, hqn] with a hr hpa hqa
    by_cases hr0 : (r a : ℝ) = 0
    · have hp0 : p a = 0 := by linarith
      have hq0 : q a = 0 := by linarith
      simp [hp0, hq0, hr0, p', q']
    · simp [p', q', mul_div_cancel₀ _ hr0]
  have hp'i : Integrable p' ν := by
    apply (integrable_withDensity_iff_integrable_smul hrm).mpr
    exact hp.congr (hmul.mono fun a ha => ha.1.symm)
  have hq'i : Integrable q' ν := by
    apply (integrable_withDensity_iff_integrable_smul hrm).mpr
    exact hq.congr (hmul.mono fun a ha => ha.2.symm)
  have hp'n : ∀ᵐ a ∂ν, 0 ≤ p' a :=
    (withDensity_absolutelyContinuous μ (fun a => (r a : ℝ≥0∞))).ae_le
      (hpn.mono fun a ha => div_nonneg ha (r a).coe_nonneg)
  have hq'n : ∀ᵐ a ∂ν, 0 ≤ q' a :=
    (withDensity_absolutelyContinuous μ (fun a => (r a : ℝ≥0∞))).ae_le
      (hqn.mono fun a ha => div_nonneg ha (r a).coe_nonneg)
  have hcost : closedPerspectiveCost hf ν p' q' = closedPerspectiveCost hf μ p q := by
    rw [closedPerspectiveCost_withDensity hf hrm]
    unfold closedPerspectiveCost
    congr 1
    · apply congrArg (fun a : ℝ => (a : EReal))
      apply integral_congr_ae
      filter_upwards [hmul] with a ha
      rw [ha.1, ha.2]
    · apply congrArg (fun a : ℝ≥0∞ => (a : EReal))
      apply lintegral_congr_ae
      filter_upwards [hmul] with a ha
      rw [ha.1, ha.2]
  have hprepare (u u' : α → ℝ) (hu : Integrable u μ) (hu' : Integrable u' ν)
      (hmul : ∀ᵐ a ∂μ, (r a : ℝ) * u' a = u a) :
      (Γ.withDensity hrm).toLinearMap (hu'.ofReal.toL1 (fun a => (u' a : ℂ))) =
        Γ.toLinearMap (hu.ofReal.toL1 (fun a => (u a : ℂ))) := by
    let huC : Integrable (fun a => (u a : ℂ)) μ := hu.ofReal
    let huC' : Integrable (fun a => (u' a : ℂ)) ν := hu'.ofReal
    change Γ.toLinearMap (PositiveTracePreservingL1Map.weightMap hrm (huC'.toL1 _)) =
      Γ.toLinearMap (huC.toL1 _)
    apply congrArg Γ.toLinearMap
    apply Lp.ext
    have hν := (ae_withDensity_iff hrm.coe_nnreal_ennreal).1 huC'.coeFn_toL1
    filter_upwards [PositiveTracePreservingL1Map.weightMap_coe hrm
      (huC'.toL1 _), huC.coeFn_toL1, hν, hmul] with a hJ hu hν hm
    rw [hJ, hu]
    by_cases hr0 : r a = 0
    · have hu0 : u a = 0 := by simpa [hr0] using hm.symm
      simp [hr0, hu0]
    · rw [hν (by simpa using hr0)]
      change ((r a : ℝ) : ℂ) * (u' a : ℂ) = (u a : ℂ)
      exact_mod_cast hm

  obtain ⟨k, R, hR⟩ := finite_measure_atomization (Γ.withDensity hrm) hf hp'm hq'm
    hp'i hq'i hp'n hq'n (hcost ▸ hc)
  have heL := hprepare p p' hp hp'i (hmul.mono fun a ha => ha.1)
  have heR := hprepare q q' hq hq'i (hmul.mono fun a ha => ha.2)
  rw [← heL, ← heR]
  exact ⟨k, R, hR.trans hcost⟩

private theorem cost_congr_ae {μ : Measure α} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) {p q p' q' : α → ℝ}
    (hp : p =ᵐ[μ] p') (hq : q =ᵐ[μ] q') :
    closedPerspectiveCost hf μ p q = closedPerspectiveCost hf μ p' q' := by
  unfold closedPerspectiveCost
  congr 1
  · congr 1
    apply integral_congr_ae
    filter_upwards [hp, hq] with a ha hb
    rw [ha, hb]
  · congr 1
    apply lintegral_congr_ae
    filter_upwards [hp, hq] with a ha hb
    rw [ha, hb]

private theorem cost_zero {μ : Measure α} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) :
    closedPerspectiveCost hf μ (fun _ => 0) (fun _ => 0) = 0 := by
  simp [closedPerspectiveCost, curvatureRemainder]

/-- Exact finite-cost atomization for actual positive TP complex L1 maps.
The output index type may be empty and the source measure need only be s-finite.
No cardinality bound or optimizer is assumed. -/
theorem source_atomization {μ : Measure α} [SFinite μ]
    (Γ : PositiveTracePreservingL1Map (n := n) μ)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {p q : α → ℝ} (hpm : Measurable p) (hqm : Measurable q)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hpn : ∀ᵐ a ∂μ, 0 ≤ p a) (hqn : ∀ᵐ a ∂μ, 0 ≤ q a)
    (hc : closedPerspectiveCost hf μ p q ≠ ⊤) :
    ∃ (k : ℕ) (R : ReverseTest
      (Γ.toLinearMap (hp.ofReal.toL1 (fun a => (p a : ℂ))))
      (Γ.toLinearMap (hq.ofReal.toL1 (fun a => (q a : ℂ)))) k),
      ∑ i, closedPerspective hf (R.p i) (R.q i) = closedPerspectiveCost hf μ p q := by
  classical
  cases isEmpty_or_nonempty n with
  | inr hn => exact source_atomization_nonempty Γ hf hpm hqm hp hq hpn hqn hc
  | inl hn =>
    letI := hn
    have hz (u : α → ℝ) (hu : Integrable u μ) (hun : ∀ᵐ a ∂μ, 0 ≤ u a) :
        u =ᵐ[μ] 0 := by
      let huC : Integrable (fun a => (u a : ℂ)) μ := hu.ofReal
      have ht := Γ.trace_preserving (huC.toL1 _)
      have heC : (∫ a, huC.toL1 _ a ∂μ) = ((∫ a, u a ∂μ : ℝ) : ℂ) :=
        (integral_congr_ae huC.coeFn_toL1).trans integral_complex_ofReal
      rw [heC] at ht
      have he : (∫ a, u a ∂μ) = 0 := by
        have := congrArg Complex.re ht
        simpa [Matrix.trace] using this.symm
      exact (integral_eq_zero_iff_of_nonneg_ae hun hu).mp he
    have he : closedPerspectiveCost hf μ p q = 0 :=
      (cost_congr_ae hf (hz p hp hpn) (hz q hq hqn)).trans (cost_zero hf)
    let R : ReverseTest
        (Γ.toLinearMap (hp.ofReal.toL1 (fun a => (p a : ℂ))))
        (Γ.toLinearMap (hq.ofReal.toL1 (fun a => (q a : ℂ)))) 0 :=
      { p := Fin.elim0
        q := Fin.elim0
        p_nonneg := fun i => i.elim0
        q_nonneg := fun i => i.elim0
        state := Fin.elim0
        prepares_left := Subsingleton.elim _ _
        prepares_right := Subsingleton.elim _ _ }
    refine ⟨0, R, ?_⟩
    simpa using he.symm

section FiniteEmbedding

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Counting-measure preparation acts on every complex L1 input, including
signed and nonreal inputs. It realizes a finite family of genuine states. -/
def finitePreparationL1Map (state : β → DensityState n) :
    PositiveTracePreservingL1Map (n := n) (Measure.count : Measure β) where
  toLinearMap :=
    { toFun := fun h => ∑ i, h i • CStarMatrix.ofMatrix.symm (state i).1
      map_add' := fun h k => by
        have he := Measure.ae_count_iff.mp (Lp.coeFn_add h k)
        simp only [he, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c h => by
        have he := Measure.ae_count_iff.mp (Lp.coeFn_smul c h)
        simp only [he, Pi.smul_apply, Finset.smul_sum, mul_smul, smul_eq_mul, RingHom.id_apply] }
  positive h hh := by
    apply Matrix.posSemidef_sum
    intro i _
    exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (state i).2.1).posSemidef.smul (Measure.ae_count_iff.mp hh i)
  trace_preserving h := by
    change (∑ i, h i • CStarMatrix.ofMatrix.symm (state i).1).trace = _
    have ht (i : β) : (CStarMatrix.ofMatrix.symm (state i).1).trace = 1 := (state i).2.2
    simp only [Matrix.trace_sum, Matrix.trace_smul, ht, smul_eq_mul, mul_one, integral_count]

/-- The finite-alphabet perspective sum is exactly the actual unnormalized
closed-perspective integral for counting measure, including infinite terms. -/
theorem finite_cost_count {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (p q : β → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    closedPerspectiveCost hf Measure.count p q = ∑ i, closedPerspective hf (p i) (q i) := by
  classical
  simp only [closedPerspectiveCost, integral_count, lintegral_count, tsum_fintype]
  simp_rw [closedPerspective_eq_affine_add_curvature hf (hp _) (hq _)]
  induction (Finset.univ : Finset β) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [EReal.coe_add, EReal.coe_ennreal_add, ← ih]
    exact add_add_add_comm _ _ _ _

end FiniteEmbedding

/-- An actual reverse test on a specified source measure. Its preparation is a
positive complex-linear TP map on the whole L1 space, with measurable L1 densities. -/
structure L1ReverseTest (A B : Matrix n n ℂ) (μ : Measure α) where
  preparation : PositiveTracePreservingL1Map (n := n) μ
  p : α → ℝ
  q : α → ℝ
  p_measurable : Measurable p
  q_measurable : Measurable q
  p_integrable : Integrable p μ
  q_integrable : Integrable q μ
  p_nonneg : ∀ᵐ a ∂μ, 0 ≤ p a
  q_nonneg : ∀ᵐ a ∂μ, 0 ≤ q a
  prepares_left : preparation.toLinearMap
    (p_integrable.ofReal.toL1 (fun a => (p a : ℂ))) = A
  prepares_right : preparation.toLinearMap
    (q_integrable.ofReal.toL1 (fun a => (q a : ℂ))) = B

/-- The actual all-source class at a fixed universe: every s-finite measurable
space and every positive complex-linear TP L1 preparation is quantified. -/
def allL1Costs {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) : Set EReal :=
  {z | ∃ (X : Type u) (m : MeasurableSpace X),
    letI : MeasurableSpace X := m
    ∃ (μ : Measure X), SFinite μ ∧ ∃ R : L1ReverseTest A B μ,
      z = closedPerspectiveCost hf μ R.p R.q}

/-- Finite costs use every finite alphabet and the same closed perspective. -/
def finiteCosts {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) : Set EReal :=
  {z | ∃ k, ∃ R : ReverseTest A B k, z = ∑ i, closedPerspective hf (R.p i) (R.q i)}

private theorem measurable_positive_L1_input {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (h : X →₁[μ] ℂ) (hn : ∀ᵐ a ∂μ, 0 ≤ h a) :
    ∃ (p : X → ℝ) (hp : Integrable p μ), Measurable p ∧
      (∀ᵐ a ∂μ, 0 ≤ p a) ∧
      hp.ofReal.toL1 (fun a => (p a : ℂ)) = h ∧
      p =ᵐ[μ] (fun a => (h a).re) := by
  let hi := (L1.integrable_coeFn h).re
  let p := hi.aestronglyMeasurable.mk (fun a => (h a).re)
  have hpeq : p =ᵐ[μ] (fun a => (h a).re) := hi.aestronglyMeasurable.ae_eq_mk.symm
  have hp : Integrable p μ := hi.congr hpeq.symm
  refine ⟨p, hp, hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable, ?_, ?_, hpeq⟩
  · filter_upwards [hpeq, hn] with a ha hb
    rw [ha]
    exact (Complex.nonneg_iff.mp hb).1
  · let hpC : Integrable (fun a => (p a : ℂ)) μ := hp.ofReal
    change hpC.toL1 _ = h
    apply Lp.ext
    filter_upwards [hpC.coeFn_toL1, hpeq, hn] with a hc ha hb
    rw [hc]
    apply Complex.ext
    · simpa only [Complex.ofReal_re] using ha
    · exact (Complex.nonneg_iff.mp hb).2

/-- Measurable representatives do not narrow the actual source class: any two
nonnegative elements of the original complex L1 space occur with their original
preparations and their exact representative-independent perspective cost. -/
theorem allL1Costs_of_positive_L1 {X : Type u} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] (Γ : PositiveTracePreservingL1Map (n := n) μ)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (p q : X →₁[μ] ℂ) (hp : ∀ᵐ a ∂μ, 0 ≤ p a) (hq : ∀ᵐ a ∂μ, 0 ≤ q a) :
    closedPerspectiveCost hf μ (fun a => (p a).re) (fun a => (q a).re) ∈
      allL1Costs.{u} hf (Γ.toLinearMap p) (Γ.toLinearMap q) := by
  obtain ⟨p', hp', hpm, hpn, hpe, hpr⟩ := measurable_positive_L1_input p hp
  obtain ⟨q', hq', hqm, hqn, hqe, hqr⟩ := measurable_positive_L1_input q hq
  let R : L1ReverseTest (Γ.toLinearMap p) (Γ.toLinearMap q) μ :=
    { preparation := Γ
      p := p'
      q := q'
      p_measurable := hpm
      q_measurable := hqm
      p_integrable := hp'
      q_integrable := hq'
      p_nonneg := hpn
      q_nonneg := hqn
      prepares_left := congrArg Γ.toLinearMap hpe
      prepares_right := congrArg Γ.toLinearMap hqe }
  exact ⟨X, inferInstance, μ, inferInstance, R, (cost_congr_ae hf hpr hqr).symm⟩

/-- The counting-measure embedding uses the existing preparation on the whole
complex L1 space, with source universe independent of the matrix carrier. -/
def finiteL1ReverseTest {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) :
    L1ReverseTest A B (Measure.count : Measure (ULift.{u} (Fin k))) := by
  classical
  let X := ULift.{u} (Fin k)
  let p : X → ℝ := fun i => R.p i.down
  let q : X → ℝ := fun i => R.q i.down
  have hp : Integrable p Measure.count := integrable_count_iff.mpr Summable.of_finite
  have hq : Integrable q Measure.count := integrable_count_iff.mpr Summable.of_finite
  let Γ := finitePreparationL1Map (fun i : X => R.state i.down)
  have hprepare (v : Fin k → ℝ) (hi : Integrable (fun i : X => v i.down) Measure.count) :
      Γ.toLinearMap (hi.ofReal.toL1 (fun i : X => (v i.down : ℂ))) =
        ∑ i, v i • CStarMatrix.ofMatrix.symm (R.state i).1 := by
    let hiC : Integrable (fun i : X => (v i.down : ℂ)) Measure.count := hi.ofReal
    change (∑ i : X, (hiC.toL1 _) i •
      CStarMatrix.ofMatrix.symm (R.state i.down).1) = _
    have he := Measure.ae_count_iff.mp hiC.coeFn_toL1
    calc
      _ = ∑ i : X, v i.down • CStarMatrix.ofMatrix.symm (R.state i.down).1 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [he i]
        exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
      _ = _ := Equiv.ulift.sum_comp
        (fun i : Fin k => v i • CStarMatrix.ofMatrix.symm (R.state i).1)

  exact
    { preparation := Γ
      p := p
      q := q
      p_measurable := measurable_of_finite _
      q_measurable := measurable_of_finite _
      p_integrable := hp
      q_integrable := hq
      p_nonneg := Measure.ae_count_iff.mpr (fun i => R.p_nonneg i.down)
      q_nonneg := Measure.ae_count_iff.mpr (fun i => R.q_nonneg i.down)
      prepares_left := (hprepare R.p hp).trans R.prepares_left
      prepares_right := (hprepare R.q hq).trans R.prepares_right }

/-- Counting embedding preserves the exact closed-perspective cost. -/
theorem finiteL1ReverseTest_cost {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) :
    closedPerspectiveCost hf Measure.count (finiteL1ReverseTest.{u} R).p
      (finiteL1ReverseTest.{u} R).q = ∑ i, closedPerspective hf (R.p i) (R.q i) := by
  change closedPerspectiveCost hf Measure.count (fun i : ULift.{u} (Fin k) => R.p i.down)
    (fun i => R.q i.down) = _
  rw [finite_cost_count hf (fun i : ULift.{u} (Fin k) => R.p i.down)
    (fun i => R.q i.down) (fun i => R.p_nonneg i.down) (fun i => R.q_nonneg i.down)]
  exact Equiv.ulift.sum_comp (fun i : Fin k => closedPerspective hf (R.p i) (R.q i))

/-- Each finite reverse test embeds in the actual all-L1 class, with exactly its
extended cost. Universe lifting changes only the names of the finite labels. -/
theorem finiteCosts_subset_allL1Costs {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) : finiteCosts hf A B ⊆ allL1Costs.{u} hf A B := by
  rintro z ⟨k, R, rfl⟩
  exact ⟨ULift.{u} (Fin k), inferInstance, Measure.count, inferInstance,
    finiteL1ReverseTest R, (finiteL1ReverseTest_cost hf R).symm⟩

/-- Every finite-valued actual source cost is exactly a finite-alphabet cost. -/
theorem allL1Costs_finite {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) {z : EReal} (hz : z ∈ allL1Costs.{u} hf A B) (hzt : z ≠ ⊤) :
    z ∈ finiteCosts hf A B := by
  rcases hz with ⟨X, m, hz⟩
  letI : MeasurableSpace X := m
  rcases hz with ⟨μ, hμ, R, rfl⟩
  letI : SFinite μ := hμ
  obtain ⟨k, T, hT⟩ := source_atomization R.preparation hf R.p_measurable R.q_measurable
    R.p_integrable R.q_integrable R.p_nonneg R.q_nonneg hzt
  let U : ReverseTest A B k :=
    { T with prepares_left := T.prepares_left.trans R.prepares_left
             prepares_right := T.prepares_right.trans R.prepares_right }
  exact ⟨k, U, hT.symm⟩

/-- The infimum over all s-finite L1 sources equals the finite-alphabet infimum
for the one specified convex generator. The proof uses exact atomization for each
finite-cost test separately; it never assumes an optimal test exists. -/
theorem source_class_infimum_eq {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) :
    sInf (allL1Costs.{u} hf A B) = sInf (finiteCosts hf A B) := by
  apply le_antisymm
  · exact sInf_le_sInf (finiteCosts_subset_allL1Costs hf A B)
  · apply le_sInf
    intro z hz
    by_cases ht : z = ⊤
    · simp [ht]
    · exact sInf_le (allL1Costs_finite hf A B hz ht)

namespace L1ReverseTest

variable {A B : Matrix n n ℂ} {μ : Measure α}

/-- The actual positive L1 hockey profile, as a Bochner integral. -/
def hockey (R : L1ReverseTest A B μ) (t : ℝ) : ℝ :=
  ∫ a, max (R.p a - t * R.q a) 0 ∂μ

/-- The actual negative L1 hockey profile, as a Bochner integral. -/
def negativeHockey (R : L1ReverseTest A B μ) (t : ℝ) : ℝ :=
  ∫ a, max (t * R.q a - R.p a) 0 ∂μ

/-- Actual integrable inputs give a finite positive profile at every threshold. -/
theorem hockey_integrable (R : L1ReverseTest A B μ) (t : ℝ) :
    Integrable (fun a => max (R.p a - t * R.q a) 0) μ :=
  (R.p_integrable.sub (R.q_integrable.const_mul t)).pos_part

/-- Actual integrable inputs give a finite negative profile at every threshold. -/
theorem negative_hockey_integrable (R : L1ReverseTest A B μ) (t : ℝ) :
    Integrable (fun a => max (t * R.q a - R.p a) 0) μ :=
  ((R.q_integrable.const_mul t).sub R.p_integrable).pos_part

private theorem input_trace (Γ : PositiveTracePreservingL1Map (n := n) μ)
    (v : α → ℝ) (hv : Integrable v μ) :
    (Γ.toLinearMap (hv.ofReal.toL1 (fun a => (v a : ℂ)))).trace.re = ∫ a, v a ∂μ := by
  rw [Γ.trace_preserving,
    integral_congr_ae hv.ofReal.coeFn_toL1, integral_complex_ofReal]
  rfl

/-- TP preserves the two unnormalized input masses. -/
theorem input_masses (R : L1ReverseTest A B μ) :
    (∫ a, R.p a ∂μ) = A.trace.re ∧ (∫ a, R.q a ∂μ) = B.trace.re := by
  constructor
  · exact (input_trace R.preparation R.p R.p_integrable).symm.trans
      (congrArg (fun M : Matrix n n ℂ => M.trace.re) R.prepares_left)
  · exact (input_trace R.preparation R.q R.q_integrable).symm.trans
      (congrArg (fun M : Matrix n n ℂ => M.trace.re) R.prepares_right)

/-- The negative and positive profiles differ by the original trace masses. -/
theorem negative_hockey_eq (R : L1ReverseTest A B μ) (t : ℝ) :
    R.negativeHockey t = R.hockey t - A.trace.re + t * B.trace.re := by
  have he (a : α) : max (t * R.q a - R.p a) 0 =
      max (R.p a - t * R.q a) 0 - R.p a + t * R.q a := by
    rcases le_total (R.p a) (t * R.q a) with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]; ring
    · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]; ring
  unfold negativeHockey hockey
  simp_rw [he]
  rw [integral_add (f := fun a => max (R.p a - t * R.q a) 0 - R.p a)
      (g := fun a => t * R.q a) ((R.hockey_integrable t).sub R.p_integrable)
      (R.q_integrable.const_mul t),
    integral_sub (f := fun a => max (R.p a - t * R.q a) 0)
      (g := R.p) (R.hockey_integrable t) R.p_integrable, integral_const_mul,
    R.input_masses.1, R.input_masses.2]

/-- HMT Proposition V.1's direct three-component construction preserves both
actual profiles at one specified positive threshold. No hypothesis on the source
measure, density factorization or continuity is used. -/
theorem finite_hockey_realization (R : L1ReverseTest A B μ) (t : ℝ) (ht : 0 < t) :
    ∃ (k : ℕ) (T : ReverseTest A B k), T.hockey t = R.hockey t ∧
      MaximalHockeyStickOperational.negativeHockey T t = R.negativeHockey t := by
  classical
  suffices hpos : ∃ (k : ℕ) (T : ReverseTest A B k), T.hockey t = R.hockey t by
    obtain ⟨k, T, he⟩ := hpos
    refine ⟨k, T, he, ?_⟩
    rw [MaximalHockeyStickOperational.negative_hockey_eq, he, R.negative_hockey_eq]
  by_cases hn : Nonempty n
  · let i₀ : n := Classical.choice hn
    let r : α → ℝ := fun a => max (R.p a - t * R.q a) 0
    let h : α → ℝ := fun a => R.p a - r a
    let s : α → ℝ := fun a => t * R.q a - h a
    have hr : Integrable r μ := R.hockey_integrable t
    have hh : Integrable h μ := R.p_integrable.sub hr
    have hse (a : α) : s a = max (t * R.q a - R.p a) 0 := by
      dsimp [s, h, r]
      rcases le_total (R.p a) (t * R.q a) with he | he
      · rw [max_eq_right (sub_nonpos.mpr he), max_eq_left (sub_nonneg.mpr he)]
        ring
      · rw [max_eq_left (sub_nonneg.mpr he), max_eq_right (sub_nonpos.mpr he)]
        ring
    have hs : Integrable s μ := (R.negative_hockey_integrable t).congr
      (Eventually.of_forall fun a => (hse a).symm)
    have hhn : ∀ᵐ a ∂μ, 0 ≤ h a := by
      filter_upwards [R.p_nonneg, R.q_nonneg] with a hp hq
      dsimp [h, r]
      exact sub_nonneg.mpr (max_le (by nlinarith) hp)
    have hsn : ∀ᵐ a ∂μ, 0 ≤ s a := by
      filter_upwards [] with a
      dsimp [s, h, r]
      have := le_max_left (R.p a - t * R.q a) 0
      linarith
    let Γ := R.preparation
    let action (v : α → ℝ) (hv : Integrable v μ) : Matrix n n ℂ :=
      Γ.toLinearMap (hv.ofReal.toL1 (fun a => (v a : ℂ)))
    have hsub (v w : α → ℝ) (hv : Integrable v μ) (hw : Integrable w μ) :
        action (fun a => v a - w a) (hv.sub hw) = action v hv - action w hw := by
      dsimp only [action]
      rw [← map_sub, ← Integrable.toL1_sub]
      apply congrArg Γ.toLinearMap
      apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
      exact Eventually.of_forall fun a => by simp
    have hsmul (v : α → ℝ) (hv : Integrable v μ) :
        action (fun a => t * v a) (hv.const_mul t) = t • action v hv := by
      dsimp only [action]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), ← map_smul, ← Integrable.toL1_smul']
      apply congrArg Γ.toLinearMap
      apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
      exact Eventually.of_forall fun a => by simp [smul_eq_mul]
    have hpositive (v : α → ℝ) (hv : Integrable v μ)
        (hvn : ∀ᵐ a ∂μ, 0 ≤ v a) : (action v hv).PosSemidef := by
      apply Γ.positive
      have he := (show Integrable (fun a => (v a : ℂ)) μ from hv.ofReal).coeFn_toL1
      filter_upwards [he, hvn] with a ha hb
      rw [ha]
      exact_mod_cast hb
    let X := action h hh
    have hp : action R.p R.p_integrable = A := R.prepares_left
    have hq : action R.q R.q_integrable = B := R.prepares_right
    have hAX : A - X = action r hr := by
      have he := hsub R.p r R.p_integrable hr
      change X = action R.p R.p_integrable - action r hr at he
      rw [hp] at he
      rw [he]; abel
    have htBX : t • B - X = action s hs := by
      change _ = action (fun a => t * R.q a - h a) hs
      rw [hsub (fun a => t * R.q a) h (R.q_integrable.const_mul t) hh,
        hsmul R.q R.q_integrable, hq]
    let G : Fin 3 → Matrix n n ℂ := ![X, A - X, t • B - X]
    have hG : ∀ i, (G i).PosSemidef := by
      intro i
      fin_cases i
      · exact hpositive h hh hhn
      · change (A - X).PosSemidef
        rw [hAX]
        exact hpositive r hr (Eventually.of_forall fun a => le_max_right _ _)
      · change (t • B - X).PosSemidef
        rw [htBX]
        exact hpositive s hs hsn
    let a : Fin 3 → ℝ := ![1, 1, 0]
    let b : Fin 3 → ℝ := ![t⁻¹, 0, t⁻¹]
    have ha : ∀ i, 0 ≤ a i := by intro i; fin_cases i <;> norm_num [a]
    have hb : ∀ i, 0 ≤ b i := by
      intro i; fin_cases i <;> simp [b, inv_nonneg.mpr ht.le]
    have hleft : (∑ i, a i • G i) = A := by simp [a, G, Fin.sum_univ_succ]
    have hright : (∑ i, b i • G i) = B := by
      simp [b, G, Fin.sum_univ_succ]
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      abel
    have hex := MaximalHockeyStickComponents.reverse_test_from_weighted_components
      (fun _ => i₀) G hG a b ha hb
    rw [hleft, hright] at hex
    obtain ⟨T, hT⟩ := hex
    refine ⟨_, T, ?_⟩
    have hprofile : T.hockey t = A.trace.re - X.trace.re := by
      rw [hT]
      simp [a, b, G, Fin.sum_univ_succ, mul_inv_cancel₀ ht.ne',
        Matrix.trace_sub, Complex.sub_re]
    rw [hprofile]
    have htrace : X.trace.re = ∫ a, h a ∂μ := input_trace Γ h hh
    rw [htrace]
    dsimp only [h]
    rw [integral_sub R.p_integrable hr, R.input_masses.1]
    dsimp only [hockey, r]
    ring
  · letI : IsEmpty n := not_nonempty_iff.mp hn
    have hp : R.p =ᵐ[μ] 0 := by
      apply (integral_eq_zero_iff_of_nonneg_ae R.p_nonneg R.p_integrable).mp
      simpa [Matrix.trace] using R.input_masses.1
    have hq : R.q =ᵐ[μ] 0 := by
      apply (integral_eq_zero_iff_of_nonneg_ae R.q_nonneg R.q_integrable).mp
      simpa [Matrix.trace] using R.input_masses.2
    let T : ReverseTest A B 0 :=
      { p := Fin.elim0
        q := Fin.elim0
        p_nonneg := fun i => i.elim0
        q_nonneg := fun i => i.elim0
        state := Fin.elim0
        prepares_left := Subsingleton.elim _ _
        prepares_right := Subsingleton.elim _ _ }
    refine ⟨0, T, ?_⟩
    have hz : R.hockey t = 0 := by
      unfold hockey
      calc
        _ = ∫ _ : α, (0 : ℝ) ∂μ := integral_congr_ae (by
          filter_upwards [hp, hq] with a ha hb
          simp [ha, hb])
        _ = 0 := integral_zero _ _
    simpa [ReverseTest.hockey] using hz.symm

end L1ReverseTest

/-- Universe-lifted counting embedding preserves both actual hockey integrals. -/
theorem finiteL1ReverseTest_profiles {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : ℝ) :
    (finiteL1ReverseTest.{u} R).hockey t = R.hockey t ∧
    (finiteL1ReverseTest.{u} R).negativeHockey t =
      MaximalHockeyStickOperational.negativeHockey R t := by
  constructor
  · change (∫ i : ULift.{u} (Fin k), max (R.p i.down - t * R.q i.down) 0
      ∂Measure.count) = ∑ i, max (R.p i - t * R.q i) 0
    rw [integral_count]
    exact Equiv.ulift.sum_comp (fun i : Fin k => max (R.p i - t * R.q i) 0)
  · change (∫ i : ULift.{u} (Fin k), max (t * R.q i.down - R.p i.down) 0
      ∂Measure.count) = ∑ i, max (t * R.q i - R.p i) 0
    rw [integral_count]
    exact Equiv.ulift.sum_comp (fun i : Fin k => max (t * R.q i - R.p i) 0)

/-- Measurable representatives preserve the original positive complex L1 inputs
and both actual integral profiles, at every threshold. No measure-class premise
is needed for this representative change. -/
theorem positive_L1_profiles {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (Γ : PositiveTracePreservingL1Map (n := n) μ)
    (p q : X →₁[μ] ℂ) (hp : ∀ᵐ a ∂μ, 0 ≤ p a) (hq : ∀ᵐ a ∂μ, 0 ≤ q a) :
    ∃ R : L1ReverseTest (Γ.toLinearMap p) (Γ.toLinearMap q) μ,
      ∀ t : ℝ,
        R.hockey t = (∫ a, max ((p a).re - t * (q a).re) 0 ∂μ) ∧
        R.negativeHockey t = (∫ a, max (t * (q a).re - (p a).re) 0 ∂μ) := by
  obtain ⟨p', hp', hpm, hpn, hpe, hpr⟩ := measurable_positive_L1_input p hp
  obtain ⟨q', hq', hqm, hqn, hqe, hqr⟩ := measurable_positive_L1_input q hq
  let R : L1ReverseTest (Γ.toLinearMap p) (Γ.toLinearMap q) μ :=
    { preparation := Γ
      p := p'
      q := q'
      p_measurable := hpm
      q_measurable := hqm
      p_integrable := hp'
      q_integrable := hq'
      p_nonneg := hpn
      q_nonneg := hqn
      prepares_left := congrArg Γ.toLinearMap hpe
      prepares_right := congrArg Γ.toLinearMap hqe }
  refine ⟨R, fun t => ⟨?_, ?_⟩⟩ <;>
    apply integral_congr_ae <;>
    filter_upwards [hpr, hqr] with a ha hb <;>
    simp only [R, ha, hb]

/-- Raw positive complex L1 inputs admit the same fixed-threshold finite
realization; representative choice preserves the literal original integrals. -/
theorem positive_L1_finite_hockey_realization {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (Γ : PositiveTracePreservingL1Map (n := n) μ)
    (p q : X →₁[μ] ℂ) (hp : ∀ᵐ a ∂μ, 0 ≤ p a) (hq : ∀ᵐ a ∂μ, 0 ≤ q a)
    (t : ℝ) (ht : 0 < t) :
    ∃ (k : ℕ) (T : ReverseTest (Γ.toLinearMap p) (Γ.toLinearMap q) k),
      T.hockey t = (∫ a, max ((p a).re - t * (q a).re) 0 ∂μ) ∧
      MaximalHockeyStickOperational.negativeHockey T t =
        (∫ a, max (t * (q a).re - (p a).re) 0 ∂μ) := by
  obtain ⟨R, he⟩ := positive_L1_profiles Γ p q hp hq
  obtain ⟨k, T, hT, hN⟩ := R.finite_hockey_realization t ht
  exact ⟨k, T, hT.trans (he t).1, hN.trans (he t).2⟩

/-- The original HMT source class: all sigma-finite spaces in any fixed source
universe, with both actual integral orientations recorded for the same test. -/
def sigmaFiniteHockeyProfiles (A B : Matrix n n ℂ) (t : ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ (X : Type u) (m : MeasurableSpace X),
    letI : MeasurableSpace X := m
    ∃ (μ : Measure X), SigmaFinite μ ∧ ∃ R : L1ReverseTest A B μ,
      z = (R.hockey t, R.negativeHockey t)}

/-- The existing s-finite source class, using the very same actual integrals. -/
def sFiniteHockeyProfiles (A B : Matrix n n ℂ) (t : ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ (X : Type u) (m : MeasurableSpace X),
    letI : MeasurableSpace X := m
    ∃ (μ : Measure X), SFinite μ ∧ ∃ R : L1ReverseTest A B μ,
      z = (R.hockey t, R.negativeHockey t)}

/-- The paired finite profile values at the one specified threshold. -/
def finiteHockeyProfiles (A B : Matrix n n ℂ) (t : ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ k, ∃ R : ReverseTest A B k,
    z = (R.hockey t, MaximalHockeyStickOperational.negativeHockey R t)}

/-- Every original sigma-finite profile pair is realized by a finite test, and
counting measure embeds every finite test back into the original source class. -/
theorem sigmaFiniteHockeyProfiles_eq (A B : Matrix n n ℂ) (t : ℝ) (ht : 0 < t) :
    sigmaFiniteHockeyProfiles.{u} A B t = finiteHockeyProfiles A B t := by
  ext z
  constructor
  · rintro ⟨X, m, hz⟩
    letI : MeasurableSpace X := m
    rcases hz with ⟨μ, _, R, rfl⟩
    obtain ⟨k, T, hp, hq⟩ := R.finite_hockey_realization t ht
    exact ⟨k, T, by rw [hp, hq]⟩
  · rintro ⟨k, T, rfl⟩
    refine ⟨ULift.{u} (Fin k), inferInstance, Measure.count, inferInstance,
      finiteL1ReverseTest T, ?_⟩
    rw [(finiteL1ReverseTest_profiles T t).1, (finiteL1ReverseTest_profiles T t).2]

/-- The same exact paired profile equality holds for every s-finite source. -/
theorem sFiniteHockeyProfiles_eq (A B : Matrix n n ℂ) (t : ℝ) (ht : 0 < t) :
    sFiniteHockeyProfiles.{u} A B t = finiteHockeyProfiles A B t := by
  ext z
  constructor
  · rintro ⟨X, m, hz⟩
    letI : MeasurableSpace X := m
    rcases hz with ⟨μ, _, R, rfl⟩
    obtain ⟨k, T, hp, hq⟩ := R.finite_hockey_realization t ht
    exact ⟨k, T, by rw [hp, hq]⟩
  · rintro ⟨k, T, rfl⟩
    refine ⟨ULift.{u} (Fin k), inferInstance, Measure.count, inferInstance,
      finiteL1ReverseTest T, ?_⟩
    rw [(finiteL1ReverseTest_profiles T t).1, (finiteL1ReverseTest_profiles T t).2]

/-- Original sigma-finite positive hockey infimum of the actual L1 integrals. -/
def operationalL1Hockey (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  sInf (Prod.fst '' sigmaFiniteHockeyProfiles.{u} A B t)

/-- Original sigma-finite negative hockey infimum of the actual L1 integrals. -/
def operationalL1NegativeHockey (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  sInf (Prod.snd '' sigmaFiniteHockeyProfiles.{u} A B t)

/-- Positive hockey infimum over every s-finite actual L1 source. -/
def sFiniteOperationalHockey (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  sInf (Prod.fst '' sFiniteHockeyProfiles.{u} A B t)

/-- Negative hockey infimum over every s-finite actual L1 source. -/
def sFiniteOperationalNegativeHockey (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  sInf (Prod.snd '' sFiniteHockeyProfiles.{u} A B t)

private theorem finite_profile_fst (A B : Matrix n n ℂ) (t : ℝ) :
    Prod.fst '' finiteHockeyProfiles A B t =
      {z : ℝ | ∃ k, ∃ R : ReverseTest A B k, z = R.hockey t} := by
  ext z
  constructor
  · rintro ⟨v, ⟨k, R, rfl⟩, rfl⟩
    exact ⟨k, R, rfl⟩
  · rintro ⟨k, R, rfl⟩
    exact ⟨_, ⟨k, R, rfl⟩, rfl⟩

private theorem finite_profile_snd (A B : Matrix n n ℂ) (t : ℝ) :
    Prod.snd '' finiteHockeyProfiles A B t =
      {z : ℝ | ∃ k, ∃ R : ReverseTest A B k,
        z = MaximalHockeyStickOperational.negativeHockey R t} := by
  ext z
  constructor
  · rintro ⟨v, ⟨k, R, rfl⟩, rfl⟩
    exact ⟨k, R, rfl⟩
  · rintro ⟨k, R, rfl⟩
    exact ⟨_, ⟨k, R, rfl⟩, rfl⟩

/-- Original and s-finite operational infima both equal the actual finite
infima. Equality of the profile sets precedes taking these infima. -/
theorem operationalL1_eq_finite (A B : Matrix n n ℂ) (t : ℝ) (ht : 0 < t) :
    operationalL1Hockey.{u} A B t = MaximalHockeyStickOperational.operationalHockey A B t ∧
    operationalL1NegativeHockey.{u} A B t =
      MaximalHockeyStickOperational.operationalNegativeHockey A B t ∧
    sFiniteOperationalHockey.{u} A B t = MaximalHockeyStickOperational.operationalHockey A B t ∧
    sFiniteOperationalNegativeHockey.{u} A B t =
      MaximalHockeyStickOperational.operationalNegativeHockey A B t := by
  simp only [operationalL1Hockey, operationalL1NegativeHockey,
    sFiniteOperationalHockey, sFiniteOperationalNegativeHockey,
    sigmaFiniteHockeyProfiles_eq A B t ht, sFiniteHockeyProfiles_eq A B t ht,
    finite_profile_fst, finite_profile_snd,
    MaximalHockeyStickOperational.operationalHockey,
    MaximalHockeyStickOperational.operationalNegativeHockey, and_self]

/-- HMT Proposition V.1 for the original sigma-finite and the full s-finite L1
source classes, with arbitrary unnormalized finite PSD outputs. -/
theorem operationalL1_hockey_eq (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ) (ht : 0 < t) :
    operationalL1Hockey.{u} A B t = MaximalHockeyStickOverlap.maximalHockey A B t ∧
    operationalL1NegativeHockey.{u} A B t =
      t * B.trace.re - MaximalHockeyStickOverlap.overlapValue A (t • B) ∧
    sFiniteOperationalHockey.{u} A B t = MaximalHockeyStickOverlap.maximalHockey A B t ∧
    sFiniteOperationalNegativeHockey.{u} A B t =
      t * B.trace.re - MaximalHockeyStickOverlap.overlapValue A (t • B) := by
  rcases operationalL1_eq_finite.{u} A B t ht with ⟨hp, hn, hsp, hsn⟩
  rw [hp, hn, hsp, hsn, MaximalHockeyStickOperational.operational_hockey_eq A B hA hB t ht,
    MaximalHockeyStickOperational.operational_negative_hockey_eq A B hA hB t ht]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The original sigma-finite class for the same actual closed-perspective cost. -/
def sigmaFiniteL1Costs {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) : Set EReal :=
  {z | ∃ (X : Type u) (m : MeasurableSpace X),
    letI : MeasurableSpace X := m
    ∃ (μ : Measure X), SigmaFinite μ ∧ ∃ R : L1ReverseTest A B μ,
      z = closedPerspectiveCost hf μ R.p R.q}

/-- Finite counting sources lie in the original class, which lies in the
s-finite class. Their already proved extreme infima agree, so the original
sigma-finite maximal value has that same faithful extended value. -/
theorem sigma_finite_source_infimum_eq {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) :
    sInf (sigmaFiniteL1Costs.{u} hf A B) = sInf (finiteCosts hf A B) := by
  have hfinite : finiteCosts hf A B ⊆ sigmaFiniteL1Costs.{u} hf A B := by
    rintro z ⟨k, R, rfl⟩
    exact ⟨ULift.{u} (Fin k), inferInstance, Measure.count, inferInstance,
      finiteL1ReverseTest R, (finiteL1ReverseTest_cost hf R).symm⟩
  have hall : sigmaFiniteL1Costs.{u} hf A B ⊆ allL1Costs.{u} hf A B := by
    rintro z ⟨X, m, hz⟩
    letI : MeasurableSpace X := m
    rcases hz with ⟨μ, hμ, R, he⟩
    letI : SigmaFinite μ := hμ
    exact ⟨X, m, μ, inferInstance, R, he⟩
  apply le_antisymm (sInf_le_sInf hfinite)
  rw [← source_class_infimum_eq.{u} hf A B]
  exact sInf_le_sInf hall

#print axioms L1ReverseTest.finite_hockey_realization
#print axioms positive_L1_finite_hockey_realization
#print axioms operationalL1_hockey_eq
#print axioms sigma_finite_source_infimum_eq
#print axioms finite_density_atomization
#print axioms source_atomization
#print axioms finiteCosts_subset_allL1Costs
#print axioms source_class_infimum_eq

end D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest
