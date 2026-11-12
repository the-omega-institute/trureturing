/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest
   mirror-E: none(waiver:source-class-bridge)
   anchors: []
   utility: none
   digest: Positive trace-preserving maps on actual complex L1 sources. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
import D5.S3.Quantum.Measurement.MeasurableInstrumentHistory
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Analytic.Convexity.CurvaturePerspectiveEndpoints
import D5.S3.Analytic.Convexity.MeasurableFiniteMoments
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.VectorMeasure.AddContent

noncomputable section

open Matrix MeasureTheory Set Filter
open scoped ComplexOrder ENNReal

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

attribute [local instance] Matrix.normedAddCommGroup Matrix.seminormedAddCommGroup

variable {α n : Type*} [MeasurableSpace α] [Fintype n] [DecidableEq n]

/-- The map acts on the entire complex L1 space. Continuity is a consequence,
not a premise. Positivity is on the actual a.e. nonnegative cone. -/
structure PositiveTracePreservingL1Map (μ : Measure α) where
  toLinearMap : (α →₁[μ] ℂ) →ₗ[ℂ] Matrix n n ℂ
  positive : ∀ h, (∀ᵐ a ∂μ, 0 ≤ h a) → (toLinearMap h).PosSemidef
  trace_preserving : ∀ h, (toLinearMap h).trace = ∫ a, h a ∂μ

private theorem psd_norm_le_trace {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    ‖A‖ ≤ A.trace.re := by
  have ht : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hd (i : n) : (A i i).re ≤ A.trace.re := by
    simpa [Matrix.trace, Complex.re_sum] using
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
        (Complex.nonneg_iff.mp (hA.diag_nonneg (i := j))).1) (Finset.mem_univ i))
  apply (Matrix.norm_le_iff ht).mpr
  intro i j
  have he := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hA i j
  rw [Complex.normSq_eq_norm_sq] at he
  have hprod := mul_le_mul (hd i) (hd j)
    (Complex.nonneg_iff.mp (hA.diag_nonneg (i := j))).1 ht
  nlinarith [norm_nonneg (A i j)]

namespace PositiveTracePreservingL1Map

variable {μ : Measure α} (Γ : PositiveTracePreservingL1Map (n := n) μ)

private theorem nonneg_norm_bound {h : α → ℝ} (hi : Integrable h μ)
    (hn : ∀ᵐ a ∂μ, 0 ≤ h a) :
    ‖Γ.toLinearMap (hi.ofReal.toL1 (fun a => (h a : ℂ)))‖ ≤ ∫ a, h a ∂μ := by
  have hp := Γ.positive (hi.ofReal.toL1 (fun a => (h a : ℂ))) (by
    filter_upwards [hi.ofReal.coeFn_toL1, hn] with a ha hn
    simpa [ha] using hn)
  have hb := psd_norm_le_trace hp
  rw [Γ.trace_preserving] at hb
  rw [integral_congr_ae hi.ofReal.coeFn_toL1, integral_complex_ofReal] at hb
  simpa using hb

/-- Positivity and trace preservation imply boundedness on the full complex L1
space, including arbitrary finite matrix size and the empty output space. -/
theorem norm_bound (h : α →₁[μ] ℂ) : ‖Γ.toLinearMap h‖ ≤ 4 * ‖h‖ := by
  let u : α → ℝ := fun a => max (h a).re 0
  let v : α → ℝ := fun a => max (-(h a).re) 0
  let s : α → ℝ := fun a => max (h a).im 0
  let t : α → ℝ := fun a => max (-(h a).im) 0
  have hi := L1.integrable_coeFn h
  have hu : Integrable u μ := hi.re.max (integrable_zero _ _ _)
  have hv : Integrable v μ := hi.re.neg.max (integrable_zero _ _ _)
  have hs : Integrable s μ := hi.im.max (integrable_zero _ _ _)
  have ht : Integrable t μ := hi.im.neg.max (integrable_zero _ _ _)
  let U := hu.ofReal.toL1 (fun a => (u a : ℂ))
  let V := hv.ofReal.toL1 (fun a => (v a : ℂ))
  let S := hs.ofReal.toL1 (fun a => (s a : ℂ))
  let T := ht.ofReal.toL1 (fun a => (t a : ℂ))
  have he : U - V + Complex.I • (S - T) = h := by
    change hu.ofReal.toL1 _ - hv.ofReal.toL1 _ + Complex.I •
      (hs.ofReal.toL1 _ - ht.ofReal.toL1 _) = h
    rw [← Integrable.toL1_sub, ← Integrable.toL1_sub, ← Integrable.toL1_smul',
      ← Integrable.toL1_add]
    rw [← Integrable.toL1_coeFn h hi]
    apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
    exact Eventually.of_forall fun a => by
      apply Complex.ext <;> simp [u, v, s, t, max_zero_sub_max_neg_zero_eq_self, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im]
  have bU := Γ.nonneg_norm_bound hu (Eventually.of_forall fun a => le_max_right _ _)
  have bV := Γ.nonneg_norm_bound hv (Eventually.of_forall fun a => le_max_right _ _)
  have bS := Γ.nonneg_norm_bound hs (Eventually.of_forall fun a => le_max_right _ _)
  have bT := Γ.nonneg_norm_bound ht (Eventually.of_forall fun a => le_max_right _ _)
  have bound (g : α → ℝ) (hg : Integrable g μ) (hb : ∀ a, g a ≤ ‖h a‖) :
      (∫ a, g a ∂μ) ≤ ‖h‖ := by
    rw [L1.norm_eq_integral_norm]
    exact integral_mono_ae hg hi.norm (Eventually.of_forall hb)
  have bu := bound u hu (fun a => max_le (Complex.re_le_norm _) (norm_nonneg _))
  have bv := bound v hv (fun a => max_le (neg_le_of_abs_le (Complex.abs_re_le_norm _))
    (norm_nonneg _))
  have bs := bound s hs (fun a => max_le (Complex.im_le_norm _) (norm_nonneg _))
  have bt := bound t ht (fun a => max_le (neg_le_of_abs_le (Complex.abs_im_le_norm _))
    (norm_nonneg _))
  calc
    ‖Γ.toLinearMap h‖ = ‖Γ.toLinearMap U - Γ.toLinearMap V +
        Complex.I • (Γ.toLinearMap S - Γ.toLinearMap T)‖ := by
      rw [← he, map_add, map_sub, map_smul, map_sub]
    _ ≤ ‖Γ.toLinearMap U‖ + ‖Γ.toLinearMap V‖ +
        (‖Γ.toLinearMap S‖ + ‖Γ.toLinearMap T‖) := by
      calc
        _ ≤ ‖Γ.toLinearMap U - Γ.toLinearMap V‖ +
            ‖Complex.I • (Γ.toLinearMap S - Γ.toLinearMap T)‖ := norm_add_le _ _
        _ ≤ _ := by simpa only [norm_smul, Complex.norm_I, one_mul] using
          add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ ≤ 4 * ‖h‖ := by change _ ≤ _; dsimp [U, V, S, T] at *; linarith

/-- The continuous realization has precisely the original action. -/
def toContinuousLinearMap : (α →₁[μ] ℂ) →L[ℂ] Matrix n n ℂ :=
  Γ.toLinearMap.mkContinuous 4 Γ.norm_bound

/-- Restriction to real inputs retains the actual complex-linear preparation. -/
def realRestriction : (α →₁[μ] ℝ) →L[ℝ] Matrix n n ℂ :=
  (Γ.toContinuousLinearMap.restrictScalars ℝ).comp (Complex.ofRealCLM.compLpL 1 μ)

end PositiveTracePreservingL1Map

/-- Construction of the coordinate measures from the actual linear action on
L1 indicators. Countable additivity follows from finite trace domination. The
Radon--Nikodym step is the frozen positive-history density theorem. -/
theorem finite_source_density {μ : Measure α} [IsFiniteMeasure μ]
    (G : (α →₁[μ] ℝ) →ₗ[ℝ] Matrix n n ℂ)
    (hpositive : ∀ h, (∀ᵐ a ∂μ, 0 ≤ h a) → (G h).PosSemidef)
    (htrace : ∀ h, (G h).trace = ((∫ a, h a ∂μ : ℝ) : ℂ))
    (base : Matrix n n ℂ) (hbase : base.PosSemidef) (hbase_trace : base.trace = 1) :
    ∃ τ : α → Matrix n n ℂ,
      Measurable τ ∧ Integrable τ μ ∧
      (∀ a, (τ a).PosSemidef ∧ (τ a).trace = 1) ∧
      ∀ E (hE : MeasurableSet E), ∀ i j,
        (∫ a in E, τ a i j ∂μ) =
          G (indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℝ)) i j := by
  classical
  let m : Set α → Matrix n n ℂ := fun E =>
    if hE : MeasurableSet E then G (indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℝ))
    else 0
  have mp (E : Set α) : (m E).PosSemidef := by
    by_cases hE : MeasurableSet E
    · dsimp [m]
      rw [dif_pos hE]
      apply hpositive
      filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hE)
        (hμs := measure_ne_top μ E) (c := (1 : ℝ))] with a ha
      rw [ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · simp [m, hE, Matrix.PosSemidef.zero]
  have mt (E : Set α) (hE : MeasurableSet E) : (m E).trace = (μ.real E : ℂ) := by
    simp only [m, dif_pos hE, htrace, integral_indicatorConstLp, smul_eq_mul, mul_one]
  have mb (E : Set α) : ‖m E‖ₑ ≤ μ E := by
    by_cases hE : MeasurableSet E
    · have h := psd_norm_le_trace (mp E)
      rw [mt E hE, Complex.ofReal_re] at h
      have h' := ENNReal.ofReal_le_ofReal h
      simpa only [ENNReal.ofReal_norm_eq_enorm, Measure.real,
        ENNReal.ofReal_toReal (measure_ne_top μ E)] using h'
    · simp [m, hE]
  let V : VectorMeasure α (Matrix n n ℂ) := VectorMeasure.of_additive_of_le_measure m mb
    (by
      intro E F hE hF hEF
      simp only [m, dif_pos hE, dif_pos hF, dif_pos (hE.union hF)]
      rw [indicatorConstLp_disjoint_union hE hF (measure_ne_top μ E)
        (measure_ne_top μ F) hEF, map_add])
    (fun E hE => by simp [m, hE])
  let coordinate : n → n → ComplexMeasure α := fun i j =>
    VectorMeasure.mapRangeL ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.proj i) : Matrix n n ℂ →L[ℝ] ℂ) V
  have hc (E : Set α) (i j : n) : coordinate i j E = m E i j := rfl
  let M : D5.S3.Quantum.Measurement.MeasurableInstrumentHistory.PositiveHistoryMeasure α n :=
    { coordinate := coordinate
      traceMeasure := μ
      finite_trace := inferInstance
      positive := fun E _ => by simpa only [hc] using mp E
      trace_eq := fun E hE => by simpa only [hc, Measure.real] using mt E hE }
  obtain ⟨τ, hm, hi, hp, he, _⟩ :=
    D5.S3.Quantum.Measurement.MeasurableInstrumentHistory.positive_history_density
      M base hbase hbase_trace
  refine ⟨τ, hm, hi, hp, ?_⟩
  intro E hE i j
  simpa only [M, hc, m, dif_pos hE] using he E hE i j

private def densityIntegralMap {μ : Measure α} {τ : α → Matrix n n ℂ}
    (hm : AEStronglyMeasurable τ μ) (hb : ∀ a, ‖τ a‖ ≤ 1) :
    (α →₁[μ] ℝ) →L[ℝ] Matrix n n ℂ := by
  have hi (h : α →₁[μ] ℝ) : Integrable (fun a => h a • τ a) μ :=
    (L1.integrable_coeFn h).smul_bdd 1 hm (Eventually.of_forall hb)
  let K : (α →₁[μ] ℝ) →ₗ[ℝ] Matrix n n ℂ :=
    { toFun := fun h => ∫ a, h a • τ a ∂μ
      map_add' := fun h k => by
        calc
          _ = ∫ a, h a • τ a + k a • τ a ∂μ := integral_congr_ae
            ((Lp.coeFn_add h k).mono fun a ha => by simp [ha, add_smul])
          _ = _ := integral_add (hi h) (hi k)
      map_smul' := fun c h => by
        calc
          _ = ∫ a, c • (h a • τ a) ∂μ := integral_congr_ae
            ((Lp.coeFn_smul c h).mono fun a ha => by simp [ha, mul_smul])
          _ = _ := integral_smul c _ }
  apply K.mkContinuous 1
  intro h
  change ‖∫ a, h a • τ a ∂μ‖ ≤ 1 * ‖h‖
  rw [one_mul, L1.norm_eq_integral_norm]
  apply norm_integral_le_of_norm_le (L1.integrable_coeFn h).norm
  exact Eventually.of_forall fun a => by
    rw [norm_smul]
    simpa using mul_le_mul_of_nonneg_left (hb a) (norm_nonneg (h a))

/-- Indicator identities of an actual continuous L1 map extend to all integrable
real inputs. The density is proved from the map, rather than postulated. -/
theorem finite_source_representation {μ : Measure α} [IsFiniteMeasure μ]
    (G : (α →₁[μ] ℝ) →L[ℝ] Matrix n n ℂ)
    (hpositive : ∀ h, (∀ᵐ a ∂μ, 0 ≤ h a) → (G h).PosSemidef)
    (htrace : ∀ h, (G h).trace = ((∫ a, h a ∂μ : ℝ) : ℂ))
    (base : Matrix n n ℂ) (hbase : base.PosSemidef) (hbase_trace : base.trace = 1) :
    ∃ τ : α → Matrix n n ℂ,
      Measurable τ ∧ Integrable τ μ ∧
      (∀ a, (τ a).PosSemidef ∧ (τ a).trace = 1) ∧
      ∀ h : α →₁[μ] ℝ, G h = ∫ a, h a • τ a ∂μ := by
  classical
  obtain ⟨τ, hm, hi, hp, he⟩ := finite_source_density G.toLinearMap
    hpositive htrace base hbase hbase_trace
  have hb (a : α) : ‖τ a‖ ≤ 1 := by
    simpa [(hp a).2] using psd_norm_le_trace (hp a).1
  let K := densityIntegralMap hm.aestronglyMeasurable hb
  have hK (h : α →₁[μ] ℝ) : K h = ∫ a, h a • τ a ∂μ := rfl
  have hset (E : Set α) (hE : MeasurableSet E) :
      G (indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℝ)) = ∫ a in E, τ a ∂μ := by
    ext i j
    rw [eval_integral (fun i => hi.integrableOn.eval i) i,
      eval_integral (fun j => (hi.integrableOn.eval i).eval j) j]
    exact (he E hE i j).symm
  refine ⟨τ, hm, hi, hp, ?_⟩
  intro h
  change G h = K h
  apply Lp.induction (hp_ne_top := (by simp : (1 : ℝ≥0∞) ≠ ∞))
    (motive := fun h : α →₁[μ] ℝ => G h = K h) ?_ ?_ ?_ h
  · intro c E hE hμE
    change G (indicatorConstLp 1 hE hμE.ne c) = K (indicatorConstLp 1 hE hμE.ne c)
    have hind : indicatorConstLp 1 hE hμE.ne c =
        c • indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℝ) := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hE) (hμs := hμE.ne) (c := c),
        indicatorConstLp_coeFn (p := 1) (hs := hE) (hμs := measure_ne_top μ E)
          (c := (1 : ℝ)), Lp.coeFn_smul c
            (indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℝ))] with a hc h1 hs
      simp only [hc, hs, Pi.smul_apply, h1]
      by_cases ha : a ∈ E <;> simp [ha]
    rw [hind, map_smul, map_smul, hset E hE, hK]
    congr 1
    calc
      (∫ a, indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℝ) a • τ a ∂μ) =
          ∫ a, E.indicator τ a ∂μ := by
            apply integral_congr_ae
            filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hE)
              (hμs := measure_ne_top μ E) (c := (1 : ℝ))] with a ha
            rw [ha]
            by_cases h : a ∈ E <;> simp [h]
      _ = _ := integral_indicator hE
  · intro f g hf hg _ hfh hgh
    simp only [map_add, hfh, hgh]
  · exact isClosed_eq G.continuous K.continuous

open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest

private theorem closedPerspective_homogeneous {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) (w p q : ℝ) (hw : 0 ≤ w) :
    closedPerspective hf (w * p) (w * q) = (w : EReal) * closedPerspective hf p q := by
  rcases hw.eq_or_lt with hw | hw
  · subst w
    simp [closedPerspective_origin]
  by_cases hq : q = 0
  · simp [closedPerspective, hq, EReal.coe_mul, mul_assoc]
  have hwq : w * q ≠ 0 := mul_ne_zero hw.ne' hq
  by_cases hp : p = 0
  · simp [closedPerspective, hq, hp, hwq, EReal.coe_mul, mul_assoc]
  have hwp : w * p ≠ 0 := mul_ne_zero hw.ne' hp
  simp only [closedPerspective, if_neg hq, if_neg hp, if_neg hwq, if_neg hwp,
    mul_div_mul_left _ _ hw.ne', ← EReal.coe_mul, mul_assoc]

private theorem curvatureRemainder_homogeneous {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) (w p q : ℝ) (hw : 0 ≤ w) :
    curvatureRemainder hf (w * p) (w * q) =
      ENNReal.ofReal w * curvatureRemainder hf p q := by
  have hn (t : Positive) : ENNReal.ofReal ((t : ℝ) * (w * q) - w * p) =
      ENNReal.ofReal w * ENNReal.ofReal ((t : ℝ) * q - p) := by
    rw [← ENNReal.ofReal_mul hw]
    congr 1
    ring
  have hp (t : Positive) : ENNReal.ofReal (w * p - (t : ℝ) * (w * q)) =
      ENNReal.ofReal w * ENNReal.ofReal (p - (t : ℝ) * q) := by
    rw [← ENNReal.ofReal_mul hw]
    congr 1
    ring
  simp only [curvatureRemainder, hn, hp]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_add]

/-- Changing to a measure with a finite-valued nonnegative density preserves
the actual unnormalized perspective integral, including infinite axis costs. -/
theorem closedPerspectiveCost_withDensity {μ : Measure α}
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {r : α → ℝ≥0} (hr : Measurable r) (p q : α → ℝ) :
    closedPerspectiveCost hf (μ.withDensity (fun a => (r a : ℝ≥0∞))) p q =
      closedPerspectiveCost hf μ (fun a => (r a : ℝ) * p a) (fun a => (r a : ℝ) * q a) := by
  unfold closedPerspectiveCost
  rw [integral_withDensity_eq_integral_smul hr,
    lintegral_withDensity_eq_lintegral_mul_non_measurable μ hr.coe_nnreal_ennreal
      (Eventually.of_forall fun a => ENNReal.coe_lt_top)]
  congr 1
  · apply congrArg (fun v : ℝ => (v : EReal))
    apply integral_congr_ae
    exact Eventually.of_forall fun a => by simp only [NNReal.smul_def, smul_eq_mul]; ring
  · apply congrArg (fun v : ℝ≥0∞ => (v : EReal))
    apply lintegral_congr_ae
    exact Eventually.of_forall fun a => by
      rw [curvatureRemainder_homogeneous hf _ _ _ (r a).coe_nonneg]
      simp

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
    simpa only [F, Prod.fst_sum, Prod.smul_fst, integral_fst hF,
      integral_fst (hpi.prodMk hqi), mul_smul] using h
  have hright : ∑ i, (w i * q (a i)) • τ (a i) = ∫ a, q a • τ a ∂μ := by
    have h := congrArg (fun z : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => z.1.2) he
    simpa only [F, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      integral_fst hF, integral_snd (hpi.prodMk hqi), mul_smul] using h
  have hreal : ∑ i, w i * c (a i) = ∫ a, c a ∂μ := by
    have h := congrArg (fun z : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => z.2) he
    simpa only [F, Prod.snd_sum, Prod.smul_snd, integral_snd hF, smul_eq_mul] using h
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
  rw [← EReal.coe_sum, hreal]

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
      integral_congr_ae (Complex.ofRealCLM.coeFn_compLpL h), integral_complex_ofReal]
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
        hu.ofReal.coeFn_toL1] with a hcomp hu hcomplex
      simp only [hcomp, Complex.ofRealCLM_apply, hu, hcomplex]
    calc
      Γ.toLinearMap (hu.ofReal.toL1 (fun a => (u a : ℂ))) = G (hu.toL1 u) := by
        change _ = Γ.toLinearMap (Complex.ofRealCLM.compLpL 1 μ (hu.toL1 u))
        rw [hlift]
      _ = ∫ a, hu.toL1 u a • τ a ∂μ := he _
      _ = _ := integral_congr_ae (hu.coeFn_toL1.mono fun a ha => by rw [ha])
  obtain ⟨c, hci, hcr, hce⟩ := finite_cost_real_moment hf hpm hqm hp hq hpn hqn hc
  obtain ⟨k, R, hR⟩ := finite_density_atomization hf hτm hτ hp hq hci hpn hqn hcr
  rw [← hprepare p hp, ← hprepare q hq] at R
  exact ⟨k, R, hR.trans hce.symm⟩

#print axioms PositiveTracePreservingL1Map.norm_bound
#print axioms finite_source_density
#print axioms finite_source_representation
#print axioms finite_density_atomization
#print axioms finite_measure_atomization

end D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest
