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

universe u

noncomputable section

open Matrix MeasureTheory Set Filter
open scoped ComplexOrder ENNReal NNReal Matrix.Norms.Elementwise MatrixOrder

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
  let hiC : Integrable (fun a => (h a : ℂ)) μ := hi.ofReal
  change ‖Γ.toLinearMap (hiC.toL1 _)‖ ≤ _
  have hcoe := hiC.coeFn_toL1
  have hp := Γ.positive (hiC.toL1 _) (by
    filter_upwards [hcoe, hn] with a ha hna
    rw [ha]
    exact_mod_cast hna)
  have he : (∫ a, hiC.toL1 _ a ∂μ) = ((∫ a, h a ∂μ : ℝ) : ℂ) :=
    (integral_congr_ae hcoe).trans integral_complex_ofReal
  have hb := psd_norm_le_trace hp
  rw [Γ.trace_preserving, he] at hb
  exact hb

/-- Positivity and trace preservation imply boundedness on the full complex L1
space, including arbitrary finite matrix size and the empty output space. -/
theorem norm_bound (h : α →₁[μ] ℂ) : ‖Γ.toLinearMap h‖ ≤ 4 * ‖h‖ := by
  let u : α → ℝ := fun a => max (h a).re 0
  let v : α → ℝ := fun a => max (-(h a).re) 0
  let s : α → ℝ := fun a => max (h a).im 0
  let t : α → ℝ := fun a => max (-(h a).im) 0
  have hi := L1.integrable_coeFn h
  have hu : Integrable u μ := hi.re.pos_part
  have hv : Integrable v μ := hi.re.neg.pos_part
  have hs : Integrable s μ := hi.im.pos_part
  have ht : Integrable t μ := hi.im.neg.pos_part
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
  have bv := bound v hv (fun a => max_le ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
    (norm_nonneg _))
  have bs := bound s hs (fun a => max_le (Complex.im_le_norm _) (norm_nonneg _))
  have bt := bound t ht (fun a => max_le ((neg_le_abs _).trans (Complex.abs_im_le_norm _))
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

private def weightMap {r : α → ℝ≥0} (hr : Measurable r) :
    (α →₁[μ.withDensity (fun a => (r a : ℝ≥0∞))] ℂ) →L[ℂ] (α →₁[μ] ℂ) := by
  let J := withDensitySMulLI μ (E := ℂ) hr
  have hJ (h : α →₁[μ.withDensity (fun a => (r a : ℝ≥0∞))] ℂ) :
      J h =ᵐ[μ] (fun a => r a • h a) :=
    (memL1_smul_of_L1_withDensity hr h).coeFn_toLp
  refine { toFun := J
           map_add' := J.map_add
           map_smul' := ?_
           cont := J.continuous }
  intro z h
  apply Lp.ext
  have hzh := (ae_withDensity_iff hr.coe_nnreal_ennreal).1 (Lp.coeFn_smul z h)
  filter_upwards [hJ (z • h), hJ h, Lp.coeFn_smul z (J h), hzh] with a h1 h2 h3 h4
  change J (z • h) a = (z • J h) a
  rw [h1, h3, Pi.smul_apply, h2]
  by_cases ha : r a = 0
  · simp [ha]
  · rw [h4 (by simpa using ha), Pi.smul_apply, smul_comm]

private theorem weightMap_coe {r : α → ℝ≥0} (hr : Measurable r)
    (h : α →₁[μ.withDensity (fun a => (r a : ℝ≥0∞))] ℂ) :
    weightMap hr h =ᵐ[μ] (fun a => r a • h a) :=
  (memL1_smul_of_L1_withDensity hr h).coeFn_toLp

/-- Reweighting constructs another actual complex-linear positive TP L1 map.
No density-state interface is assumed in the construction. -/
def withDensity {r : α → ℝ≥0} (hr : Measurable r) :
    PositiveTracePreservingL1Map (n := n) (μ.withDensity (fun a => (r a : ℝ≥0∞))) where
  toLinearMap := Γ.toLinearMap.comp (weightMap hr).toLinearMap
  positive h hh := by
    apply Γ.positive
    have hh' := (ae_withDensity_iff hr.coe_nnreal_ennreal).1 hh
    filter_upwards [weightMap_coe hr h, hh'] with a hJ ha
    change 0 ≤ (weightMap hr h) a
    rw [hJ]
    by_cases hr0 : r a = 0
    · simp [hr0]
    · exact smul_nonneg (r a).coe_nonneg (ha (by simpa using hr0))
  trace_preserving h := by
    change (Γ.toLinearMap (weightMap hr h)).trace = _
    rw [Γ.trace_preserving, integral_congr_ae (weightMap_coe hr h)]
    exact (integral_withDensity_eq_integral_smul hr h).symm

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
      simpa only [ofReal_norm, Measure.real,
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
    VectorMeasure.mapRangeL
      ((ContinuousLinearMap.proj j : (n → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj i : Matrix n n ℂ →L[ℝ] (n → ℂ))) V
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
            ((Lp.coeFn_add h k).mono fun a ha =>
              (congrArg (fun r : ℝ => r • τ a) ha).trans (add_smul _ _ _))
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
  let K := densityIntegralMap (μ := μ) hm.aestronglyMeasurable hb
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
    symm
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
      change (r a : ℝ≥0∞) * curvatureRemainder hf (p a) (q a) =
        curvatureRemainder hf ((r a : ℝ) * p a) ((r a : ℝ) * q a)
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

/-- Each finite reverse test embeds in the actual all-L1 class, with exactly its
extended cost. Universe lifting changes only the names of the finite labels. -/
theorem finiteCosts_subset_allL1Costs {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) : finiteCosts hf A B ⊆ allL1Costs.{u} hf A B := by
  classical
  rintro z ⟨k, R, rfl⟩
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

  let T : L1ReverseTest A B (Measure.count : Measure X) :=
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
  refine ⟨X, inferInstance, Measure.count, inferInstance, T, ?_⟩
  change _ = closedPerspectiveCost hf Measure.count p q
  rw [finite_cost_count hf p q (fun i => R.p_nonneg i.down) (fun i => R.q_nonneg i.down)]
  exact (Equiv.ulift.sum_comp _).symm

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

#print axioms PositiveTracePreservingL1Map.norm_bound
#print axioms finite_source_density
#print axioms finite_source_representation
#print axioms finite_density_atomization
#print axioms source_atomization
#print axioms finiteCosts_subset_allL1Costs
#print axioms source_class_infimum_eq

end D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest
