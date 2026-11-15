/- GID: D5/S3/Quantum/Divergence/NormalOverlapOperational
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/NormalOverlapOperational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original whole-complex-L1 hockey infima and optimal normal overlaps. -/

import D5.S3.Quantum.Divergence.NormalOverlapCurvatureEquality

/-! The operational hinge class uses arbitrary positive elements of the entire
complex L1 space, with the source universe independent of the concrete algebra.
Its preparation has independently defined coefficient-series outputs. -/

noncomputable section
universe u v
open Set MeasureTheory
open scoped ComplexOrder Topology ENNReal
open D5.S3.Quantum.Analysis.NormalMomentFamily
open D5.S3.Quantum.Analysis.NormalFunctionals
open D5.S3.Quantum.Analysis.ConcreteCoefficientPredual
open D5.S3.Quantum.Analysis.ConcreteCoefficientSeries
open D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment
open D5.S3.Quantum.Divergence.NormalOverlapCompatibility
open D5.S3.Quantum.Divergence.NormalOverlapCurvatureEquality
open D5.S3.Quantum.Divergence.PosteriorSourceNormalization
open D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation

namespace D5.S3.Quantum.Divergence.NormalOverlapOperational

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem source_overlap_integral {ρ σ : StrongDual ℂ A}
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (R : NormalL1ReverseTest ρ σ μ) (t : ℝ) :
    (overlap (posteriorFamily R) t 1).re = ∫ x, min (R.p x) (t * R.q x) ∂μ := by
  have hw := pullContinuous_moments R.p_measurable R.q_measurable
    R.p_integrable R.q_integrable R.p_nonneg R.q_nonneg
  have hwp := pullContinuous_coe R.p_measurable R.q_measurable
    R.p_integrable R.q_integrable coordinate
  have hwq := pullContinuous_coe R.p_measurable R.q_measurable
    R.p_integrable R.q_integrable (1 - coordinate)
  rw [hw.2.1] at hwp
  rw [hw.2.2] at hwq
  have hpC := R.p_integrable.ofReal.coeFn_toL1
  have hqC := R.q_integrable.ofReal.coeFn_toL1
  have he := R.preparation.mass
    (pullContinuous R.p_measurable R.q_measurable R.p_integrable R.q_integrable
      (overlapFunction t))
  change overlap (posteriorFamily R) t 1 = _ at he
  have hfun : pullContinuous R.p_measurable R.q_measurable
      R.p_integrable R.q_integrable (overlapFunction t) =ᵐ[μ]
      (fun x => ((min (R.p x) (t * R.q x) : ℝ) : ℂ)) := by
    filter_upwards [pullContinuous_coe R.p_measurable R.q_measurable
      R.p_integrable R.q_integrable (overlapFunction t), hwp, hwq, hpC, hqC]
      with x hx hpx hqx hpc hqc
    rw [hx]
    have hp : (mass R.p R.q x : ℝ) * (theta R.p R.q x : ℝ) = R.p x := by
      have hh := congrArg Complex.re (hpc.symm.trans hpx)
      simpa [coordinate, Complex.real_smul] using hh.symm
    have hq : (mass R.p R.q x : ℝ) * (1 - (theta R.p R.q x : ℝ)) = R.q x := by
      have hh := congrArg Complex.re (hqc.symm.trans hqx)
      simpa [coordinate, Complex.real_smul] using hh.symm
    change ((mass R.p R.q x : ℝ) : ℂ) *
      ((min (theta R.p R.q x : ℝ) (t * (1 - (theta R.p R.q x : ℝ))) : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul, mul_min_of_nonneg _ _ (mass R.p R.q x).coe_nonneg,
      hp, ← mul_assoc, mul_comm (mass R.p R.q x : ℝ) t, mul_assoc, hq]
  rw [integral_congr_ae hfun, integral_complex_ofReal] at he
  exact congrArg Complex.re he

/-- Actual original source hinge integrals equal deficits of the functional
overlap of that source's actual posterior family. -/
theorem source_hinges {ρ σ : StrongDual ℂ A}
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (R : NormalL1ReverseTest ρ σ μ) (t : ℝ) :
    (∫ x, max (t * R.q x - R.p x) 0 ∂μ) =
        t * (σ 1).re - (overlap (posteriorFamily R) t 1).re ∧
    (∫ x, max (R.p x - t * R.q x) 0 ∂μ) =
        (ρ 1).re - (overlap (posteriorFamily R) t 1).re := by
  have hm (w : X → ℝ) (hi : Integrable w μ) := R.preparation.mass
    (hi.ofReal.toL1 (fun x => (w x : ℂ)))
  have hp := hm R.p R.p_integrable
  have hq := hm R.q R.q_integrable
  rw [R.prepares_left, integral_congr_ae R.p_integrable.ofReal.coeFn_toL1,
    integral_complex_ofReal] at hp
  rw [R.prepares_right, integral_congr_ae R.q_integrable.ofReal.coeFn_toL1,
    integral_complex_ofReal] at hq
  have hpi : (∫ x, R.p x ∂μ) = (ρ 1).re := (congrArg Complex.re hp).symm
  have hqi : (∫ x, R.q x ∂μ) = (σ 1).re := (congrArg Complex.re hq).symm
  have hi := R.p_integrable.min (R.q_integrable.const_mul t)
  have hn (a b : ℝ) : max (a - b) 0 = a - min a b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, sub_self, max_eq_right (sub_nonpos.mpr h)]
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  constructor
  · simp_rw [hn, min_comm (t * R.q _) (R.p _)]
    rw [integral_sub (R.q_integrable.const_mul t) hi,
      integral_const_mul, hqi, ← source_overlap_integral]
  · simp_rw [hn]
    rw [integral_sub R.p_integrable hi, hpi, ← source_overlap_integral]

section Concrete
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)

/-- The actual original single-hinge cost set, before infima. True selects
the negative hinge (tq-p)+ and false selects the positive hinge (p-tq)+. -/
def standardHingeCosts (negative : Bool) (t : ℝ) : Set ℝ :=
  {z | ∃ (X : Type u) (m : MeasurableSpace X),
    letI := m
    ∃ μ : Measure X, SigmaFinite μ ∧ ∃ Γ : StandardL1Preparation M μ,
      ∃ p q : X →₁[μ] ℂ,
        (∀ᵐ x ∂μ, 0 ≤ p x) ∧ (∀ᵐ x ∂μ, 0 ≤ q x) ∧
        Γ.toLinearMap p = ρ ∧ Γ.toLinearMap q = σ ∧
        z = ∫ x, if negative then max (t * (q x).re - (p x).re) 0
          else max ((p x).re - t * (q x).re) 0 ∂μ}

/-- The original operational infimum, over sigma-finite sources in Type u. -/
def operationalHinge (negative : Bool) (t : ℝ) : ℝ :=
  sInf (standardHingeCosts.{u} M ρ σ negative t)

private theorem hinge_mem_of_test {X : Type u} [MeasurableSpace X]
    {μ : Measure X} [SigmaFinite μ] (R : NormalL1ReverseTest ρ σ μ)
    (hs : ∀ h, IsCoefficientSeries M (R.preparation.toLinearMap h))
    (b : Bool) (t : ℝ) :
    (∫ x, if b then max (t * R.q x - R.p x) 0 else max (R.p x - t * R.q x) 0 ∂μ) ∈
      standardHingeCosts.{u} M ρ σ b t := by
  let Γ : StandardL1Preparation M μ :=
    { toLinearMap := R.preparation.toLinearMap
      positive := R.preparation.positive, mass := R.preparation.mass, series := hs }
  let P := R.p_integrable.ofReal.toL1 (fun x => (R.p x : ℂ))
  let Q := R.q_integrable.ofReal.toL1 (fun x => (R.q x : ℂ))
  have hP := R.p_integrable.ofReal.coeFn_toL1
  have hQ := R.q_integrable.ofReal.coeFn_toL1
  refine ⟨X, inferInstance, μ, inferInstance, Γ, P, Q, ?_, ?_,
    R.prepares_left, R.prepares_right, ?_⟩
  · filter_upwards [hP, R.p_nonneg] with x hx hn
    rw [hx]; exact_mod_cast hn
  · filter_upwards [hQ, R.q_nonneg] with x hx hn
    rw [hx]; exact_mod_cast hn
  · apply integral_congr_ae
    filter_upwards [hP, hQ] with x hx hy
    simp only [hx, hy, Complex.ofReal_re]

variable (hρ : Positive ρ) (hσ : Positive σ)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)
include hρ hσ hρs hσs

private theorem hinge_lower_bound (b : Bool) (t : ℝ) (ht : 0 < t)
    {z : ℝ} (hz : z ∈ standardHingeCosts.{u} M ρ σ b t) :
    (if b then t * (σ 1).re else (ρ 1).re) - overlapValue M ρ σ t ≤ z := by
  obtain ⟨X, m, μ, hμ, Γ, p, q, hp, hq, hl, hr, rfl⟩ := hz
  letI := m
  obtain ⟨p', hp', hpm, hpn, hpe, hpr⟩ := measurable_positive_L1_input p hp
  obtain ⟨q', hq', hqm, hqn, hqe, hqr⟩ := measurable_positive_L1_input q hq
  let R : NormalL1ReverseTest ρ σ μ :=
    { preparation := Γ.toNormal, p := p', q := q',
      p_measurable := hpm, q_measurable := hqm,
      p_integrable := hp', q_integrable := hq', p_nonneg := hpn, q_nonneg := hqn,
      prepares_left := (congrArg Γ.toLinearMap hpe).trans hl,
      prepares_right := (congrArg Γ.toLinearMap hqe).trans hr }
  have he : (∫ x, if b then max (t * (q x).re - (p x).re) 0
      else max ((p x).re - t * (q x).re) 0 ∂μ) =
      ∫ x, if b then max (t * R.q x - R.p x) 0 else max (R.p x - t * R.q x) 0 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hpr, hqr] with x hx hy
    simp only [R, hx, hy]
  rw [he]
  obtain ⟨_, _, hmax⟩ := value_attained M ρ σ hρ hσ hρs hσs t ht
  obtain ⟨hpO, hlO, hrO⟩ := overlap_feasible (posteriorFamily R) t ht.le
  have hv := hmax _ hpO hlO hrO
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [(source_hinges R t).2]
    exact sub_le_sub_left hv _
  · simp only [↓reduceIte]
    rw [(source_hinges R t).1]
    exact sub_le_sub_left hv _


private theorem family_real_hinges (F : Family ρ σ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : Interval, max (t * (1 - x.val) - x.val) 0 ∂scalarMeasure F) =
        t * (σ 1).re - (overlap F t 1).re ∧
    (∫ x : Interval, max (x.val - t * (1 - x.val)) 0 ∂scalarMeasure F) =
        (ρ 1).re - (overlap F t 1).re := by
  have hi (w : C(Interval, ℝ)) : Integrable w (scalarMeasure F) :=
    w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr {z w : ℂ} (h : z ≤ w) : z.re ≤ w.re := by
    have hh := (Complex.nonneg_iff.mp (sub_nonneg.mpr h)).1
    simpa only [Complex.sub_re, sub_nonneg] using hh
  obtain ⟨_, hleft, hright⟩ := overlap_feasible F t ht
  have hdn : 0 ≤ t * (σ 1).re - (overlap F t 1).re := by
    have hh := hr (hright 1 zero_le_one)
    simpa only [smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, sub_nonneg] using hh
  have hdp : 0 ≤ (ρ 1).re - (overlap F t 1).re :=
    sub_nonneg.mpr (hr (hleft 1 zero_le_one))
  have hn := ofReal_integral_eq_lintegral_ofReal
    (hi ⟨fun x => max (t * (1 - x.val) - x.val) 0, by fun_prop⟩)
    (Filter.Eventually.of_forall (fun _ => le_max_right _ _))
  have hp := ofReal_integral_eq_lintegral_ofReal
    (hi ⟨fun x => max (x.val - t * (1 - x.val)) 0, by fun_prop⟩)
    (Filter.Eventually.of_forall (fun _ => le_max_right _ _))
  have hn' : ENNReal.ofReal
      (∫ x : Interval, max (t * (1 - x.val) - x.val) 0 ∂scalarMeasure F) =
      ENNReal.ofReal (t * (σ 1).re - (overlap F t 1).re) := by
    simpa using hn.trans (family_hinge_integrals F t).1
  have hp' : ENNReal.ofReal
      (∫ x : Interval, max (x.val - t * (1 - x.val)) 0 ∂scalarMeasure F) =
      ENNReal.ofReal ((ρ 1).re - (overlap F t 1).re) := by
    simpa using hp.trans (family_hinge_integrals F t).2
  constructor
  · have he := congrArg ENNReal.toReal hn'
    simpa only [ENNReal.toReal_ofReal hdn,
      ENNReal.toReal_ofReal (integral_nonneg (fun _ => le_max_right _ _))] using he
  · have he := congrArg ENNReal.toReal hp'
    simpa only [ENNReal.toReal_ofReal hdp,
      ENNReal.toReal_ofReal (integral_nonneg (fun _ => le_max_right _ _))] using he

private theorem optimal_hinge_mem (b : Bool) (t : ℝ) (ht : 0 < t) :
    (if b then t * (σ 1).re else (ρ 1).re) - overlapValue M ρ σ t ∈
      standardHingeCosts.{u} M ρ σ b t := by
  obtain ⟨F, hF, _⟩ := value_attained M ρ σ hρ hσ hρs hσs t ht
  obtain ⟨Γ, _, hn, hp, hm, _, hl, hr, hΓE, _⟩ :=
    standard_posterior_realization M ρ σ hρ hσ hρs hσs F
  let R := liftedReverseTest.{u} F Γ hn hp hm hl hr
  have hs (h) : IsCoefficientSeries M (R.preparation.toLinearMap h) :=
    coefficientSpace_series M ⟨_, hΓE _⟩
  have hmem := hinge_mem_of_test.{u} M ρ σ R hs b t
  have he : (∫ x, if b then max (t * R.q x - R.p x) 0
      else max (R.p x - t * R.q x) 0 ∂liftedMeasure.{u} (scalarMeasure F)) =
      (if b then t * (σ 1).re else (ρ 1).re) - overlapValue M ρ σ t := by
    change (∫ x : ULift.{u} Interval, if b then max (t * (1 - x.down.val) - x.down.val) 0
      else max (x.down.val - t * (1 - x.down.val)) 0 ∂(scalarMeasure F).map ULift.up) = _
    rw [integral_map measurable_up.aemeasurable (by fun_prop)]
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte, ULift.down_up, hF] using
        (family_real_hinges M ρ σ hρ hσ hρs hσs F t ht.le).2
    · simpa only [↓reduceIte, ULift.down_up, hF] using
        (family_real_hinges M ρ σ hρ hσ hρs hσs F t ht.le).1
  rwa [he] at hmem

/-- The actual original operational single-hinge infima are attained and equal
the optimal normal-overlap deficits. No finite alphabet, trace or normalization
of the two prescribed functionals is imposed. -/
theorem operational_hinge_eq (b : Bool) (t : ℝ) (ht : 0 < t) :
    IsLeast (standardHingeCosts.{u} M ρ σ b t)
      ((if b then t * (σ 1).re else (ρ 1).re) - overlapValue M ρ σ t) ∧
    operationalHinge.{u} M ρ σ b t =
      (if b then t * (σ 1).re else (ρ 1).re) - overlapValue M ρ σ t := by
  have hl : IsLeast (standardHingeCosts.{u} M ρ σ b t)
      ((if b then t * (σ 1).re else (ρ 1).re) - overlapValue M ρ σ t) :=
    ⟨optimal_hinge_mem.{u} M ρ σ hρ hσ hρs hσs b t ht,
      fun _ hz => hinge_lower_bound.{u} M ρ σ hρ hσ hρs hσs b t ht hz⟩
  exact ⟨hl, hl.csInf_eq⟩

/-- Literal original maximal-hockey curvature value. The branch at one is
the negative original operational single-hinge infimum. -/
def originalHockeyValue {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) : EReal :=
  (affineCost f ρ σ : EReal) +
    (∫⁻ t : Positive, ENNReal.ofReal
      (if (t : ℝ) ≤ 1 then operationalHinge.{u} M ρ σ true t
        else operationalHinge.{u} M ρ σ false t) ∂curvature hf : ℝ≥0∞)

/-- Identifies the actual original operational curvature quantity, before the
classification is applied, with the actual optimal-normal-overlap formula. -/
theorem originalHockeyValue_eq_overlap {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    originalHockeyValue.{u} M ρ σ hf = hockeyValue M ρ σ hf := by
  rw [originalHockeyValue, hockeyValue]
  have he (t : Positive) := (operational_hinge_eq.{u} M ρ σ hρ hσ hρs hσs true t t.property).2
  have he' (t : Positive) := (operational_hinge_eq.{u} M ρ σ hρ hσ hρs hσs false t t.property).2
  simp only [↓reduceIte] at he he'
  simp_rw [he, he']
  congr 1
  congr 1
  have hm : MeasurableSet (Iic (⟨1, by norm_num⟩ : Positive)) := measurableSet_Iic
  rw [← lintegral_piecewise hm.nullMeasurableSet, compl_Iic]
  rfl

/-- Exact arbitrary-curvature-support equality classification over the actual
original standard-predual whole-L1 source class, assuming only that the literal
original maximal infimum is real finite. -/
theorem original_operational_equality_iff_finite_compatibility
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hfinite : ∃ c : ℝ, maximalValue.{u} M ρ σ hf = (c : EReal)) :
    maximalValue.{u} M ρ σ hf = originalHockeyValue.{u} M ρ σ hf ↔
      FiniteCompatibility M ρ σ (curvature hf).support := by
  rw [originalHockeyValue_eq_overlap M ρ σ hρ hσ hρs hσs hf]
  exact original_equality_iff_finite_compatibility.{u} M ρ σ hρ hσ hρs hσs hf hfinite

end Concrete

#print axioms source_hinges
#print axioms operational_hinge_eq
#print axioms originalHockeyValue_eq_overlap
#print axioms original_operational_equality_iff_finite_compatibility

end D5.S3.Quantum.Divergence.NormalOverlapOperational
