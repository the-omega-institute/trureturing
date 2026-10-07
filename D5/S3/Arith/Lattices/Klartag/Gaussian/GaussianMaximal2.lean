/- GID: D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian moments, independence and operator norm tails. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Gaussian.GaussianMaximal
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped2
import D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStep
import D5.S3.Arith.Lattices.Klartag.Walk.ChainWalk
import D5.S3.Arith.Lattices.Klartag.State.StateInvariant4
import D5.S3.Arith.Lattices.Klartag.Contact.ContactIntegrated
import D5.S3.Arith.Lattices.Klartag.State.StepGlue
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped4
import D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open ProbabilityTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι]

variable {ξ : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℝ≥0} {σ : ℝ}

theorem integrable_maxNorm_of_laws (hσ : 0 < σ) (hv : 0 < (v : ℝ))
    (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) :
    Integrable (maxNorm ξ N) P := by
  refine ⟨(measurable_maxNorm hξ N).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => maxNorm_nonneg N ω)]
  exact lt_of_le_of_lt (lintegral_maxNorm_le hσ hv hσ2 hlaw hξ N one_pos) ENNReal.ofReal_lt_top

omit [MeasurableSpace Ω] in
theorem maxNorm_sq_set (hσ : 0 < σ) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    {ω | t < maxNorm ξ N ω ^ 2 / (2 * σ ^ 2)}
      = {ω | Real.sqrt (2 * t) < maxNorm ξ N ω / σ} := by
  ext ω
  simp only [Set.mem_ofPred_eq]
  have hM : 0 ≤ maxNorm ξ N ω / σ := div_nonneg (maxNorm_nonneg N ω) hσ.le
  have hx : Real.sqrt ((maxNorm ξ N ω / σ) ^ 2) = maxNorm ξ N ω / σ := Real.sqrt_sq hM
  have hrw : maxNorm ξ N ω ^ 2 / (2 * σ ^ 2) = (maxNorm ξ N ω / σ) ^ 2 / 2 := by
    field_simp
  rw [hrw]
  constructor
  · intro h
    have h2 : 2 * t < (maxNorm ξ N ω / σ) ^ 2 := by linarith
    calc Real.sqrt (2 * t) < Real.sqrt ((maxNorm ξ N ω / σ) ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) h2
      _ = maxNorm ξ N ω / σ := hx
  · intro h
    have hsq : Real.sqrt (2 * t) ^ 2 = 2 * t := Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (2 * t), h, hsq]

/-- The square's tail is **exponential**: `P{maxNorm²/(2σ²) > t} ≤ 2dN·e^{−t}`. -/
theorem maxNorm_sq_tail (hσ : 0 < σ) (hv : 0 < (v : ℝ))
    (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v) (N : ℕ) {t : ℝ}
    (ht : 0 < t) :
    P.real {ω | t < maxNorm ξ N ω ^ 2 / (2 * σ ^ 2)}
      ≤ (N : ℝ) * ((Fintype.card ι : ℝ) * (2 * Real.exp (-t))) := by
  rw [maxNorm_sq_set hσ N ht]
  have h := maxNorm_tail hσ hv hσ2 hlaw N (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 2 * t))
  have harg : -Real.sqrt (2 * t) ^ 2 / 2 = -t := by
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * t)]; ring
  rwa [harg] at h

/-- **The second moment, in `lintegral` form.** -/
theorem lintegral_maxNorm_sq_le (hσ : 0 < σ) (hv : 0 < (v : ℝ))
    (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫⁻ ω, ENNReal.ofReal (maxNorm ξ N ω ^ 2) ∂P
      ≤ ENNReal.ofReal (2 * σ ^ 2
          * (a + (N : ℝ) * (Fintype.card ι : ℝ) * 2 * Real.exp (-a))) := by
  classical
  set C : ℝ := (N : ℝ) * (Fintype.card ι : ℝ) * 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hmm : Measurable (maxNorm ξ N) := measurable_maxNorm hξ N
  set g : Ω → ℝ := fun ω => maxNorm ξ N ω ^ 2 / (2 * σ ^ 2) with hg
  have hgm : Measurable g := (hmm.pow_const 2).div_const _
  have hgnn : 0 ≤ᵐ[P] g :=
    Filter.Eventually.of_forall fun ω => by positivity
  have hlc : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P = ∫⁻ t in Ioi (0 : ℝ), P {ω | t < g ω} :=
    lintegral_eq_lintegral_meas_lt P hgnn hgm.aemeasurable
  have hsmall : ∫⁻ t in Ioc (0 : ℝ) a, P {ω | t < g ω} ≤ ENNReal.ofReal a := by
    refine le_trans (setLIntegral_mono measurable_const (fun t _ => prob_le_one)) ?_
    rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]
  have hcont : Continuous fun t : ℝ => C * Real.exp (-t) := by fun_prop
  have hintC : IntegrableOn (fun t : ℝ => C * Real.exp (-t)) (Ioi a) :=
    (integrableOn_exp_neg_Ioi a).const_mul C
  have hbig : ∫⁻ t in Ioi a, P {ω | t < g ω} ≤ ENNReal.ofReal (C * Real.exp (-a)) := by
    have hstep : ∫⁻ t in Ioi a, P {ω | t < g ω}
        ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (C * Real.exp (-t)) := by
      refine setLIntegral_mono hcont.measurable.ennreal_ofReal (fun t ht => ?_)
      rw [measure_eq_ofReal_measureReal]
      refine ENNReal.ofReal_le_ofReal ?_
      have h := maxNorm_sq_tail hσ hv hσ2 hlaw N (lt_trans ha ht)
      calc P.real {ω | t < g ω}
          ≤ (N : ℝ) * ((Fintype.card ι : ℝ) * (2 * Real.exp (-t))) := h
        _ = C * Real.exp (-t) := by rw [hC]; ring
    calc ∫⁻ t in Ioi a, P {ω | t < g ω}
        ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (C * Real.exp (-t)) := hstep
      _ = ENNReal.ofReal (∫ t in Ioi a, C * Real.exp (-t)) :=
          (ofReal_integral_eq_lintegral_ofReal hintC
            (Filter.Eventually.of_forall fun t => by positivity)).symm
      _ = ENNReal.ofReal (C * Real.exp (-a)) := by
          rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) a) (Ioi a) :=
    Set.disjoint_left.2 (fun t h1 h2 => absurd h2 (not_lt.2 h1.2))
  have hgle : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P ≤ ENNReal.ofReal (a + C * Real.exp (-a)) := by
    rw [hlc, hsplit, lintegral_union measurableSet_Ioi hdisj,
      ENNReal.ofReal_add ha.le (by positivity)]
    exact add_le_add hsmall hbig
  have hscale : ∀ ω, ENNReal.ofReal (maxNorm ξ N ω ^ 2)
      = ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (g ω) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity), hg]
    congr 1
    field_simp
  calc ∫⁻ ω, ENNReal.ofReal (maxNorm ξ N ω ^ 2) ∂P
      = ENNReal.ofReal (2 * σ ^ 2) * ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := by
        simp_rw [hscale]
        exact lintegral_const_mul _ hgm.ennreal_ofReal
    _ ≤ ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (a + C * Real.exp (-a)) := by gcongr
    _ = ENNReal.ofReal (2 * σ ^ 2 * (a + C * Real.exp (-a))) :=
        (ENNReal.ofReal_mul (by positivity)).symm

theorem integrable_maxNorm_sq (hσ : 0 < σ) (hv : 0 < (v : ℝ))
    (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) :
    Integrable (fun ω => maxNorm ξ N ω ^ 2) P := by
  refine ⟨((measurable_maxNorm hξ N).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => by positivity)]
  exact lt_of_le_of_lt (lintegral_maxNorm_sq_le hσ hv hσ2 hlaw hξ N one_pos)
    ENNReal.ofReal_lt_top

/-- **The second moment, in Bochner form, at the optimal level `a = log(2dN)`.** -/
theorem expectation_max_norm_sq_le_log (hσ : 0 < σ) (hv : 0 < (v : ℝ))
    (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ)
    (hK : Real.exp 1 ≤ 2 * (Fintype.card ι : ℝ) * (N : ℝ)) :
    ∫ ω, maxNorm ξ N ω ^ 2 ∂P
      ≤ σ ^ 2 * (2 * Real.log (2 * (Fintype.card ι : ℝ) * (N : ℝ)) + 2) := by
  set K : ℝ := 2 * (Fintype.card ι : ℝ) * (N : ℝ) with hKdef
  have hK1 : (1 : ℝ) < K := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hK
  have hK0 : 0 < K := by linarith
  have hlogK : (1 : ℝ) ≤ Real.log K := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) hK
  have ha : 0 < Real.log K := by linarith
  have hexp : Real.exp (-Real.log K) = 1 / K := by
    rw [Real.exp_neg, Real.exp_log hK0, one_div]
  have hCK : (N : ℝ) * (Fintype.card ι : ℝ) * 2 = K := by rw [hKdef]; ring
  have hint : Integrable (fun ω => maxNorm ξ N ω ^ 2) P :=
    integrable_maxNorm_sq hσ hv hσ2 hlaw hξ N
  have hbridge := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => by positivity)
  have h := lintegral_maxNorm_sq_le hσ hv hσ2 hlaw hξ N ha
  rw [← hbridge, hCK, hexp] at h
  have hval : 2 * σ ^ 2 * (Real.log K + K * (1 / K))
      = σ ^ 2 * (2 * Real.log K + 2) := by field_simp
  rw [hval] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

omit [Fintype ι] in
/-- An increment read at a measurable random index is measurable: `ℕ` is countable. -/
theorem measurable_at_index (hξ : ∀ k, Measurable (ξ k)) {f : Ω → ℕ} (hf : Measurable f) :
    Measurable fun ω => ξ (f ω) ω := by
  have h : Measurable fun p : ℕ × Ω => ξ p.1 p.2 :=
    measurable_from_prod_countable_right (fun k => hξ k)
  exact h.comp (hf.prodMk measurable_id)

/-- **Both moments at a random index are integrable.**  Domination by `maxNorm` and `maxNorm²`. -/
def IntegrableAtIndex (P : Measure Ω) (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (N : ℕ) : Prop :=
  ∀ f : Ω → ℕ, Measurable f → (∀ ω, f ω < N) →
    Integrable (fun ω => ‖ξ (f ω) ω‖) P ∧ Integrable (fun ω => ‖ξ (f ω) ω‖ ^ 2) P

theorem integrableAtIndex_of_laws (hσ : 0 < σ) (hv : 0 < (v : ℝ))
    (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card ι : ℝ))
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) :
    IntegrableAtIndex P ξ N := by
  intro f hf hfN
  have hmeas : Measurable fun ω => ξ (f ω) ω := measurable_at_index hξ hf
  have h1 : Integrable (maxNorm ξ N) P := integrable_maxNorm_of_laws hσ hv hσ2 hlaw hξ N
  have h2 : Integrable (fun ω => maxNorm ξ N ω ^ 2) P := integrable_maxNorm_sq hσ hv hσ2 hlaw hξ N
  constructor
  · refine Integrable.mono' h1 hmeas.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_at_index_le_maxNorm f hfN ω
  · refine Integrable.mono' h2 ((hmeas.norm.pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_at_index_le_maxNorm f hfN ω) 2

/-- **`DriftStopped4.MaximalHyp2`, both moments, with one constant.** -/
theorem maximalHyp2_of_laws {n : ℕ} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {v : ℝ≥0} {σ : ℝ}
    (hσ : 0 < σ) (hv : 0 < (v : ℝ)) (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card (UT n) : ℝ))
    (hlaw : ∀ k, ∀ p : UT n, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (N : ℕ)
    (hK : Real.exp 1 ≤ 2 * (Fintype.card (UT n) : ℝ) * (N : ℝ)) :
    DriftStopped4.MaximalHyp2 ξ P N
      (max (σ * (Real.sqrt (2 * Real.log (2 * (Fintype.card (UT n) : ℝ) * (N : ℝ))) + 1))
        (σ ^ 2 * (2 * Real.log (2 * (Fintype.card (UT n) : ℝ) * (N : ℝ)) + 2))) := by
  have hi1 : Integrable (maxNorm ξ N) P := integrable_maxNorm_of_laws hσ hv hσ2 hlaw hξ N
  have hi2 : Integrable (fun ω => maxNorm ξ N ω ^ 2) P :=
    integrable_maxNorm_sq hσ hv hσ2 hlaw hξ N
  have hm1 : ∫ ω, maxNorm ξ N ω ∂P
      ≤ σ * (Real.sqrt (2 * Real.log (2 * (Fintype.card (UT n) : ℝ) * (N : ℝ))) + 1) :=
    expectation_max_norm_le_log hσ hv hσ2 hlaw hξ N hK hi1
  have hm2 : ∫ ω, maxNorm ξ N ω ^ 2 ∂P
      ≤ σ ^ 2 * (2 * Real.log (2 * (Fintype.card (UT n) : ℝ) * (N : ℝ)) + 2) :=
    expectation_max_norm_sq_le_log hσ hv hσ2 hlaw hξ N hK
  intro f hf h1 h2
  have hle1 : ∫ ω, ‖ξ (f ω) ω‖ ∂P ≤ ∫ ω, maxNorm ξ N ω ∂P :=
    integral_mono h1 hi1 fun ω => norm_at_index_le_maxNorm f hf ω
  have hle2 : ∫ ω, ‖ξ (f ω) ω‖ ^ 2 ∂P ≤ ∫ ω, maxNorm ξ N ω ^ 2 ∂P :=
    integral_mono h2 hi2 fun ω =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_at_index_le_maxNorm f hf ω) 2
  exact ⟨le_trans (le_trans hle1 hm1) (le_max_left _ _),
    le_trans (le_trans hle2 hm2) (le_max_right _ _)⟩

/-- **`DriftStopped4.MaximalAtAdopted` at the drift lane's own increments.**  `ChainSetup.step c`
is `c • coord k`, whose coordinates are `N(0, c²)` by `ChainSetup.step_coord_law`; so `v = c²` and
`σ = c·√d` with `d = card (UT n)`. -/
theorem maximalAtAdopted_step {n : ℕ} {c : ℝ} (hc : 0 < c)
    (hd : 0 < Fintype.card (UT n))
    (hK : Real.exp 1 ≤ 2 * (Fintype.card (UT n) : ℝ)
      * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) :
    DriftStopped4.MaximalAtAdopted (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      (ChainSetup.step c)
      (max (c * Real.sqrt (Fintype.card (UT n) : ℝ)
          * (Real.sqrt (2 * Real.log (2 * (Fintype.card (UT n) : ℝ)
              * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ))) + 1))
        ((c * Real.sqrt (Fintype.card (UT n) : ℝ)) ^ 2
          * (2 * Real.log (2 * (Fintype.card (UT n) : ℝ)
              * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) + 2))) := by
  have hdR : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by exact_mod_cast hd
  have hvcoe : ((Real.toNNReal (c ^ 2) : ℝ≥0) : ℝ) = c ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg c)
  have hσpos : 0 < c * Real.sqrt (Fintype.card (UT n) : ℝ) := by positivity
  have hvpos : (0 : ℝ) < ((Real.toNNReal (c ^ 2) : ℝ≥0) : ℝ) := by
    rw [hvcoe]; positivity
  have hσ2 : (c * Real.sqrt (Fintype.card (UT n) : ℝ)) ^ 2
      = ((Real.toNNReal (c ^ 2) : ℝ≥0) : ℝ) * (Fintype.card (UT n) : ℝ) := by
    rw [hvcoe, mul_pow, Real.sq_sqrt hdR.le]
  exact maximalHyp2_of_laws hσpos hvpos hσ2
    (fun k p => ChainSetup.step_coord_law c k p)
    (fun k => ChainSetup.measurable_step c k) _ hK

/-- `log n ≥ 6` at the gate's threshold: `e⁶ < 404 < 2 073 600`. -/
theorem six_le_log {n : ℕ} (hn : 2073600 ≤ n) : (6 : ℝ) ≤ Real.log n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  rw [Real.le_log_iff_exp_le hn0]
  have h6 : Real.exp 6 = Real.exp 1 ^ (6 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  calc Real.exp 6 = Real.exp 1 ^ (6 : ℕ) := h6
    _ ≤ (2.7182818286 : ℝ) ^ (6 : ℕ) := by
        exact pow_le_pow_left₀ (Real.exp_pos 1).le he 6
    _ ≤ 2073600 := by norm_num
    _ ≤ (n : ℝ) := hnR

/-- **The majorant.**  `√(2·log K) + 1 ≤ 5·√(log n)` whenever `log K ≤ 10·log n + 3` and
`log n ≥ 6`.  The slack is real but not large: at `n = 2 073 600` the left side is `17.51` and the
right `19.07`. -/
theorem sqrt_log_majorant {n : ℕ} (hn : 2073600 ≤ n) {K : ℝ}
    (hKle : Real.log K ≤ 10 * Real.log n + 3) :
    Real.sqrt (2 * Real.log K) + 1 ≤ 5 * Real.sqrt (Real.log n) := by
  set L : ℝ := Real.log n with hL
  have hL6 : (6 : ℝ) ≤ L := six_le_log hn
  set s : ℝ := Real.sqrt L with hs
  have hs2 : s ^ 2 = L := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg L
  have hsge : (2.449 : ℝ) ≤ s := by
    rw [hs, show (2.449 : ℝ) = Real.sqrt (2.449 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)

  have hkey : 2 * s + 1 ≤ s ^ 2 := by nlinarith
  have hrhs : 0 ≤ 5 * s - 1 := by nlinarith
  have hsq : 2 * Real.log K ≤ (5 * s - 1) ^ 2 := by
    have : (5 * s - 1) ^ 2 = 25 * L - 10 * s + 1 := by rw [← hs2]; ring
    rw [this]
    nlinarith
  have hfin : Real.sqrt (2 * Real.log K) ≤ 5 * s - 1 := by
    rw [show (5 * s - 1) = Real.sqrt ((5 * s - 1) ^ 2) by rw [Real.sqrt_sq hrhs]]
    exact Real.sqrt_le_sqrt hsq
  linarith

/-- `log (2·d·N) ≤ 10·log n + 3` at the adopted parameters: `d ≤ n²` and
`N = ⌈16·n⁷·log n⌉ ≤ 17·n⁷·log n`, so `2dN ≤ 34·n⁹·log n`, and `log 34 ≤ 4`,
`log (log n) ≤ log n − 1`. -/
theorem log_two_card_numSteps_le {n : ℕ} (hn : 2073600 ≤ n) :
    Real.log (2 * (Fintype.card (UT n) : ℝ)
      * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) ≤ 10 * Real.log n + 3 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL6 : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hd : (Fintype.card (UT n) : ℝ) ≤ (n : ℝ) ^ 2 := Discharge.card_UT_le_sq (by omega)
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have hx0 : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 7 * Real.log n := by positivity
  have hN : ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) ≤ 17 * (n : ℝ) ^ 7 * Real.log n := by
    have hc : ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) < 16 * (n : ℝ) ^ 7 * Real.log n + 1 :=
      Nat.ceil_lt_add_one hx0
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ 7 * Real.log n := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ (n:ℝ)) 7]
    linarith
  have hN0 : (0 : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hprod : 2 * (Fintype.card (UT n) : ℝ) * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
      ≤ 34 * (n : ℝ) ^ 9 * Real.log n := by
    have h1 : 2 * (Fintype.card (UT n) : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by linarith
    calc 2 * (Fintype.card (UT n) : ℝ) * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        ≤ 2 * (n : ℝ) ^ 2 * (17 * (n : ℝ) ^ 7 * Real.log n) := by
          apply mul_le_mul h1 hN hN0 (by positivity)
      _ = 34 * (n : ℝ) ^ 9 * Real.log n := by ring
  have hpos : (0 : ℝ) < 34 * (n : ℝ) ^ 9 * Real.log n := by positivity
  have hlogle : Real.log (2 * (Fintype.card (UT n) : ℝ)
      * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ))
      ≤ Real.log (34 * (n : ℝ) ^ 9 * Real.log n) := by
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ 2 * (Fintype.card (UT n) : ℝ)
        * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) with heq | hlt
    · rw [← heq, Real.log_zero]
      refine Real.log_nonneg ?_
      have h9 : (1 : ℝ) ≤ (n : ℝ) ^ 9 := one_le_pow₀ (by linarith)
      nlinarith [h9, hL6]
    · exact Real.log_le_log hlt hprod
  have hnne : (n : ℝ) ≠ 0 := by linarith
  have h9ne : ((n : ℝ) ^ 9) ≠ 0 := pow_ne_zero 9 hnne
  have hlne : Real.log n ≠ 0 := by linarith
  have hsplit : Real.log (34 * (n : ℝ) ^ 9 * Real.log n)
      = Real.log 34 + 9 * Real.log n + Real.log (Real.log n) := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) h9ne) hlne,
      Real.log_mul (by norm_num) h9ne, Real.log_pow]
    push_cast; ring
  have hlog34 : Real.log 34 ≤ 4 := by
    have h4 : (34 : ℝ) ≤ Real.exp 4 := by
      have h1 : Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have h2 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
      calc (34 : ℝ) ≤ (2.7182818283 : ℝ) ^ (4 : ℕ) := by norm_num
        _ ≤ Real.exp 1 ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 4
        _ = Real.exp 4 := h1.symm
    rw [show (4 : ℝ) = Real.log (Real.exp 4) by rw [Real.log_exp]]
    exact Real.log_le_log (by norm_num) h4
  have hloglog : Real.log (Real.log n) ≤ Real.log n - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  linarith

end D5.S3.Arith.Lattices.Klartag
