/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation
   mirror-E: none(waiver:source-class-bridge)
   anchors: []
   utility: none
   digest: Positive trace-preserving maps on actual complex L1 sources. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickOperational
import D5.S3.Quantum.Measurement.MeasurableInstrumentHistory
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Analytic.Convexity.CurvaturePerspectiveEndpoints
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.VectorMeasure.AddContent

universe u

noncomputable section

open Matrix MeasureTheory Set Filter
open scoped ComplexOrder ENNReal NNReal Matrix.Norms.Elementwise MatrixOrder

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickL1Preparation

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

theorem psd_norm_le_trace {A : Matrix n n ℂ} (hA : A.PosSemidef) :
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

def weightMap {r : α → ℝ≥0} (hr : Measurable r) :
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

theorem weightMap_coe {r : α → ℝ≥0} (hr : Measurable r)
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

theorem closedPerspective_homogeneous {f : ℝ → ℝ}
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

#print axioms PositiveTracePreservingL1Map.norm_bound
#print axioms finite_source_density
#print axioms finite_source_representation
#print axioms closedPerspectiveCost_withDensity

end D5.S3.Quantum.Divergence.MaximalHockeyStickL1Preparation
