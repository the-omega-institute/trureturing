/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid
   mirror-E: none(waiver:general-integral-estimates)
   anchors: []
   utility: none
   digest: Cost and entropy estimates for right-endpoint logistic grids directly using the I-class FermiMellin results. -/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic
import D5.S3.Weil.ZetaBridge.FermiMellin

/-! Finite quadrature bounds for logistic occupancy and its binary entropy. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Set MeasureTheory Finset Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid

/-- The cost of the two symmetric families of logistic bins. -/
def rightEndpointCost (t : ℕ → ℝ) (m : ℕ) : ℝ :=
  2 * ∑ i ∈ range m, (t (i + 1) - t i) * (t (i + 1) * sigmoid (-t (i + 1)))

/-- The binary entropy of the two symmetric families of logistic bins. -/
def rightEndpointEntropy (t : ℕ → ℝ) (m : ℕ) : ℝ :=
  2 * ∑ i ∈ range m, (t (i + 1) - t i) * binEntropy (sigmoid (-t (i + 1)))

/-- On a grid starting at zero, the right-endpoint cost has a one-sided mesh error,
and the entropy deficit is bounded by the mesh times the total entropy drop. -/
theorem rightEndpoint_bounds {t : ℕ → ℝ} {m : ℕ} {U δ : ℝ} (hm : 0 < m)
    (hzero : t 0 = 0) (hend : t m = U)
    (hstep : ∀ i < m, 0 < t (i + 1) - t i)
    (hwidth : ∀ i < m, t (i + 1) - t i ≤ δ) :
    rightEndpointCost t m ≤
      2 * (∫ u in (0 : ℝ)..U, u * sigmoid (-u)) + 2 * δ * (∫ u in (0 : ℝ)..U, sigmoid (-u)) ∧
    0 ≤ 2 * (∫ u in (0 : ℝ)..U, binEntropy (sigmoid (-u))) - rightEndpointEntropy t m ∧
    2 * (∫ u in (0 : ℝ)..U, binEntropy (sigmoid (-u))) - rightEndpointEntropy t m ≤
      2 * δ * (log 2 - binEntropy (sigmoid (-U))) ∧
    2 * δ * (log 2 - binEntropy (sigmoid (-U))) ≤ 2 * δ * log 2 := by
  let q (u : ℝ) := sigmoid (-u)
  let f (u : ℝ) := binEntropy (q u)
  let width (i : ℕ) := t (i + 1) - t i
  have hq : Continuous q := continuous_sigmoid.comp continuous_neg
  have hf : Continuous f := binEntropy_continuous.comp hq
  have hmoment : Continuous (fun u => u * q u) := continuous_id.mul hq
  have hqanti : Antitone q := fun _ _ hab => sigmoid_monotone (neg_le_neg hab)
  have hqhalf {u : ℝ} (hu : 0 ≤ u) : q u ∈ Icc 0 (2⁻¹ : ℝ) := by
    refine ⟨sigmoid_nonneg _, ?_⟩
    simpa only [q, neg_zero, sigmoid_zero] using hqanti hu
  have hfanti : AntitoneOn f (Ici 0) := fun _ ha _ hb hab =>
    binEntropy_strictMonoOn.monotoneOn (hqhalf hb) (hqhalf ha) (hqanti hab)
  have ht_nonneg : ∀ i ≤ m, 0 ≤ t i := by
    intro i
    induction i with
    | zero => intro _; rw [hzero]
    | succ i ih =>
      intro hi
      exact (ih (Nat.le_of_succ_le hi)).trans (sub_pos.mp (hstep i hi)).le
  have hcost (i : ℕ) (hi : i < m) :
      width i * (t (i + 1) * q (t (i + 1))) ≤
        (∫ u in t i..t (i + 1), u * q u) + δ * (∫ u in t i..t (i + 1), q u) := by
    have hle : t i ≤ t (i + 1) := (sub_pos.mp (hstep i hi)).le
    have hmul : Continuous (fun u => δ * q u) := continuous_const.mul hq
    have hpoint (u : ℝ) (hu : u ∈ Icc (t i) (t (i + 1))) :
        t (i + 1) * q (t (i + 1)) ≤ u * q u + δ * q u := by
      calc
        _ ≤ t (i + 1) * q u :=
          mul_le_mul_of_nonneg_left (hqanti hu.2) (ht_nonneg (i + 1) hi)
        _ ≤ (u + δ) * q u :=
          mul_le_mul_of_nonneg_right (by linarith [hwidth i hi, hu.1]) (sigmoid_nonneg _)
        _ = _ := add_mul _ _ _
    have h := intervalIntegral.integral_mono_on (μ := volume) hle intervalIntegrable_const
      ((hmoment.add hmul).intervalIntegrable _ _) hpoint
    change (∫ _ in t i..t (i + 1), t (i + 1) * q (t (i + 1))) ≤
      (∫ u in t i..t (i + 1), u * q u + δ * q u) at h
    rwa [intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_add (hmoment.intervalIntegrable _ _)
        (hmul.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at h
  have hentropy (i : ℕ) (hi : i < m) :
      0 ≤ (∫ u in t i..t (i + 1), f u) - width i * f (t (i + 1)) ∧
      (∫ u in t i..t (i + 1), f u) - width i * f (t (i + 1)) ≤
        δ * (f (t i) - f (t (i + 1))) := by
    have ha := ht_nonneg i hi.le
    have hb := ht_nonneg (i + 1) hi
    have hle := (sub_pos.mp (hstep i hi)).le
    have hl := intervalIntegral.integral_mono_on (μ := volume) hle intervalIntegrable_const
      (hf.intervalIntegrable _ _) (fun _ hu => hfanti (ha.trans hu.1) hb hu.2)
    have hh := intervalIntegral.integral_mono_on (μ := volume) hle (hf.intervalIntegrable _ _)
      intervalIntegrable_const (fun _ hu => hfanti ha (ha.trans hu.1) hu.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hl hh
    refine ⟨sub_nonneg.mpr hl, ?_⟩
    calc
      _ ≤ width i * f (t i) - width i * f (t (i + 1)) := sub_le_sub_right hh _
      _ = width i * (f (t i) - f (t (i + 1))) := (mul_sub _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hwidth i hi)
        (sub_nonneg.mpr (hfanti ha hb hle))
  have hsum_cost := sum_le_sum fun i hi => hcost i (mem_range.mp hi)
  rw [sum_add_distrib, ← mul_sum,
    intervalIntegral.sum_integral_adjacent_intervals
      (fun _ _ => hmoment.intervalIntegrable _ _),
    intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hq.intervalIntegrable _ _),
    hzero, hend] at hsum_cost
  have hsum_lower := sum_nonneg fun i hi => (hentropy i (mem_range.mp hi)).1
  have hsum_upper := sum_le_sum fun i hi => (hentropy i (mem_range.mp hi)).2
  have hsum_f : (∑ i ∈ range m, ∫ u in t i..t (i + 1), f u) = ∫ u in (0 : ℝ)..U, f u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hf.intervalIntegrable _ _),
      hzero, hend]
  rw [sum_sub_distrib, hsum_f] at hsum_lower hsum_upper
  have hdrop : (∑ i ∈ range m, (f (t i) - f (t (i + 1)))) = f 0 - f U := by
    rw [Finset.sum_range_sub' (fun i => f (t i)), hzero, hend]
  rw [← mul_sum, hdrop] at hsum_upper
  have hfzero : f 0 = log 2 := by simp [f, q]
  rw [hfzero] at hsum_upper
  have hδ : 0 ≤ δ := (hstep 0 hm).le.trans (hwidth 0 hm)
  have hfU : 0 ≤ f U := binEntropy_nonneg (sigmoid_nonneg _) (sigmoid_le_one _)
  change 2 * (∑ i ∈ range m, width i * (t (i + 1) * q (t (i + 1)))) ≤ _ ∧
    0 ≤ 2 * (∫ u in (0 : ℝ)..U, f u) - 2 * (∑ i ∈ range m, width i * f (t (i + 1))) ∧
    2 * (∫ u in (0 : ℝ)..U, f u) - 2 * (∑ i ∈ range m, width i * f (t (i + 1))) ≤
      2 * δ * (log 2 - f U) ∧ 2 * δ * (log 2 - f U) ≤ 2 * δ * log 2
  refine ⟨?_, by linarith, ?_, ?_⟩
  · change _ ≤ 2 * (∫ u in (0 : ℝ)..U, u * q u) + 2 * δ * (∫ u in (0 : ℝ)..U, q u)
    linarith
  · linarith
  · exact mul_le_mul_of_nonneg_left (sub_le_self _ hfU) (by positivity)


private abbrev occupancy (u : ℝ) : ℝ := sigmoid (-u)
private abbrev entropy (u : ℝ) : ℝ := binEntropy (occupancy u)
private abbrev potential (u : ℝ) : ℝ := log (1 + exp (-u))
private abbrev tailShape (u : ℝ) : ℝ := (u + 2) * exp (-u)

/-- The logarithmic potential and the occupancy moment add up to the binary entropy. -/
private theorem entropy_eq_potential (u : ℝ) : entropy u = potential u + u * occupancy u := by
  have hx : 1 + exp (-u) ≠ 0 := by positivity
  have hfactor : 1 + exp u = exp u * (1 + exp (-u)) := by
    rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, exp_zero, add_comm]
  have hlog : log (1 + exp u) = u + potential u := by
    rw [hfactor, Real.log_mul (exp_pos _).ne' hx, Real.log_exp]
  unfold entropy binEntropy
  have hcompl : log (1 - occupancy u)⁻¹ = potential u := by
    rw [occupancy, sigmoid_neg, sub_sub_cancel, sigmoid_def, inv_inv]
  have hocc : log (occupancy u)⁻¹ = u + potential u := by
    simpa [occupancy, sigmoid_def] using hlog
  rw [hcompl, hocc]
  ring

private theorem potential_bounds (u : ℝ) : 0 ≤ potential u ∧ potential u ≤ exp (-u) := by
  constructor
  · exact Real.log_nonneg (by linarith [exp_pos (-u)])
  · simpa only [add_sub_cancel_left] using Real.log_le_sub_one_of_pos
      (show 0 < 1 + exp (-u) by positivity)

private theorem hasDerivAt_potential (u : ℝ) : HasDerivAt potential (-occupancy u) u := by
  have h := (((hasDerivAt_id u).neg.exp).const_add 1).log (by
    change 1 + exp (-u) ≠ 0
    positivity)
  convert h using 1
  · rfl
  · change -occupancy u = (exp (-u) * -1) / (1 + exp (-u))
    rw [occupancy, sigmoid_def, neg_neg, Real.exp_neg]
    field_simp
    ring

private theorem tendsto_tailShape : Tendsto tailShape atTop (𝓝 0) := by
  have h : Tendsto (fun u : ℝ => u * exp (-u)) atTop (𝓝 0) := by
    simpa using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  change Tendsto (fun u : ℝ => (u + 2) * exp (-u)) atTop (𝓝 0)
  simpa only [add_mul, add_zero, mul_zero] using
    h.add (tendsto_exp_neg_atTop_nhds_zero.const_mul 2)

private theorem entropy_integrable_mass_tail :
    IntegrableOn occupancy (Ioi 0) ∧ (∫ u in Ioi (0 : ℝ), occupancy u) = log 2 ∧
    IntegrableOn (fun u => u * occupancy u) (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), u * occupancy u) = π ^ 2 / 12 ∧
    IntegrableOn entropy (Ioi 0) ∧ (∫ u in Ioi (0 : ℝ), entropy u) = π ^ 2 / 6 ∧
    ∀ U : ℝ, 0 ≤ U → (∫ u in Ioi U, entropy u) ≤ tailShape U := by
  have hqcont : Continuous occupancy := continuous_sigmoid.comp continuous_neg
  have hJcont : Continuous potential :=
    (continuous_const.add continuous_neg.rexp).log (fun u => by
      change 1 + exp (-u) ≠ 0
      positivity)
  have hqInt : IntegrableOn occupancy (Ioi 0) := by
    refine (integrableOn_exp_neg_Ioi 0).mono' hqcont.aestronglyMeasurable ?_
    exact Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (sigmoid_nonneg _)]
      simpa only [occupancy, sigmoid_def, neg_neg, Weil.ZetaBridge.FermiMellin.fermi] using
        Weil.ZetaBridge.FermiMellin.fermi_le_exp_neg u
  have hJInt : IntegrableOn potential (Ioi 0) := by
    refine (integrableOn_exp_neg_Ioi 0).mono' hJcont.aestronglyMeasurable ?_
    exact Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (potential_bounds u).1]
      exact (potential_bounds u).2
  have hmajor : IntegrableOn (fun u : ℝ => u * exp (-u)) (Ioi 0) := by
    have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm] using h
  have hMInt : IntegrableOn (fun u => u * occupancy u) (Ioi 0) := by
    refine hmajor.mono' (continuous_id.mul hqcont).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    rw [Real.norm_of_nonneg (mul_nonneg hu0 (sigmoid_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ hu0
    simpa only [occupancy, sigmoid_def, neg_neg, Weil.ZetaBridge.FermiMellin.fermi] using
      Weil.ZetaBridge.FermiMellin.fermi_le_exp_neg u
  have hqMass : (∫ u in Ioi (0 : ℝ), occupancy u) = log 2 := by
    have h := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_at_one 1 one_pos
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simpa [occupancy, sigmoid_def, add_comm (1 : ℝ), Complex.ofReal_inv,
      Complex.ofReal_add, one_div] using h
  have hMMass : (∫ u in Ioi (0 : ℝ), u * occupancy u) = π ^ 2 / 12 := by
    have h := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_eq_of_ne_one
      1 one_pos 2 (by norm_num) (by norm_num)
    have hGamma : Complex.Gamma 2 = 1 := by
      simp
    have hexp : (1 : ℂ) - 2 = -1 := by norm_num
    have hc : (∫ u in Ioi (0 : ℝ), ((u * occupancy u : ℝ) : ℂ)) =
        ((π ^ 2 / 12 : ℝ) : ℂ) := by
      rw [hexp, Complex.cpow_neg_one, hGamma, riemannZeta_two] at h
      rw [show (2 : ℂ) - 1 = 1 by norm_num] at h
      push_cast
      calc
        _ = (1 - (2 : ℂ)⁻¹) * ((π : ℂ) ^ 2 / 6) := by
          simpa [occupancy, sigmoid_def, Complex.ofReal_mul, Complex.ofReal_inv,
            Complex.ofReal_add, add_comm (1 : ℝ), div_eq_mul_inv] using h
        _ = _ := by ring
    rw [integral_complex_ofReal] at hc
    exact Complex.ofReal_injective hc
  have hJlimit : Tendsto (fun u => -(u * potential u)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun u : ℝ => u * exp (-u)) atTop (𝓝 0) := by
      simpa using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hj : Tendsto (fun u => u * potential u) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
        exact mul_nonneg hu (potential_bounds u).1
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
        exact mul_le_mul_of_nonneg_left (potential_bounds u).2 hu
    simpa using hj.neg
  have hJMass : (∫ u in Ioi (0 : ℝ), potential u) = π ^ 2 / 12 := by
    have hderiv (u : ℝ) : HasDerivAt (fun v => -(v * potential v))
        (u * occupancy u - potential u) u := by
      convert ((hasDerivAt_id u).mul (hasDerivAt_potential u)).neg using 1
      · rfl
      · change u * occupancy u - potential u = -(1 * potential u + u * -occupancy u)
        ring
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := 0) (fun u _ => hderiv u) (hMInt.sub hJInt) hJlimit
    change (∫ u in Ioi (0 : ℝ), u * occupancy u - potential u) = _ at h
    rw [integral_sub hMInt hJInt, hMMass] at h
    simpa using (sub_eq_zero.mp (by simpa using h : π ^ 2 / 12 - _ = 0)).symm
  have hentropy : entropy = fun u => potential u + u * occupancy u :=
    funext entropy_eq_potential
  have hEInt : IntegrableOn entropy (Ioi 0) := by
    rw [hentropy]
    exact hJInt.add hMInt
  refine ⟨hqInt, hqMass, hMInt, hMMass, hEInt, ?_, ?_⟩
  · rw [hentropy, integral_add hJInt hMInt, hJMass, hMMass]
    ring
  · intro U hU
    have hderiv (u : ℝ) : HasDerivAt (fun v => -tailShape v)
        ((1 + u) * exp (-u)) u := by
      convert (((hasDerivAt_id u).add_const 2).mul ((hasDerivAt_id u).neg.exp)).neg
        using 1
      · rfl
      · change (1 + u) * exp (-u) = -(1 * exp (-u) + (u + 2) * (exp (-u) * -1))
        ring
    have hpos (u : ℝ) (hu : u ∈ Ioi U) : 0 ≤ (1 + u) * exp (-u) :=
      mul_nonneg (by linarith [show U < u from hu]) (exp_pos _).le
    have hlim : Tendsto (fun u => -tailShape u) atTop (𝓝 0) := by
      simpa using tendsto_tailShape.neg
    have hboundInt := integrableOn_Ioi_deriv_of_nonneg'
      (fun u (_ : u ∈ Ici U) => hderiv u) hpos hlim
    calc
      _ ≤ ∫ u in Ioi U, (1 + u) * exp (-u) := by
        apply setIntegral_mono_on (hEInt.mono_set (Ioi_subset_Ioi hU))
          hboundInt measurableSet_Ioi
        intro u hu
        rw [entropy_eq_potential, add_mul, one_mul]
        refine add_le_add (potential_bounds u).2
          (mul_le_mul_of_nonneg_left ?_ (hU.trans (le_of_lt hu)))
        simpa only [occupancy, sigmoid_def, neg_neg, Weil.ZetaBridge.FermiMellin.fermi] using
          Weil.ZetaBridge.FermiMellin.fermi_le_exp_neg u
      _ = tailShape U := by
        simpa using integral_Ioi_of_hasDerivAt_of_nonneg'
          (fun u (_ : u ∈ Ici U) => hderiv u) hpos hlim

/-- The explicit cost and entropy bounds for a finite grid with mesh at most δ. -/
theorem rightEndpoint_explicit_bounds {t : ℕ → ℝ} {m : ℕ} {U δ : ℝ} (hm : 0 < m)
    (hzero : t 0 = 0) (hend : t m = U)
    (hstep : ∀ i < m, 0 < t (i + 1) - t i)
    (hwidth : ∀ i < m, t (i + 1) - t i ≤ δ) :
    rightEndpointCost t m ≤ π ^ 2 / 6 + 2 * δ * log 2 ∧
    (2 : ℝ) * (π ^ 2 / 6) - 2 * (U + 2) * exp (-U) - 2 * δ * log 2 ≤
      rightEndpointEntropy t m := by
  have hδ := (hstep 0 hm).le.trans (hwidth 0 hm)
  have hnonneg : ∀ i ≤ m, 0 ≤ t i := by
    intro i
    induction i with
    | zero => intro _; rw [hzero]
    | succ i ih =>
      intro hi
      exact (ih (Nat.le_of_succ_le hi)).trans (sub_pos.mp (hstep i hi)).le
  have hU : 0 ≤ U := hend ▸ hnonneg m le_rfl
  obtain ⟨hq, hqMass, hM, hMMass, hE, hEMass, htail⟩ := entropy_integrable_mass_tail
  have split {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) :=
    intervalIntegral.integral_interval_add_Ioi hg (hg.mono_set (Ioi_subset_Ioi hU))
  have hqBound : (∫ u in (0 : ℝ)..U, occupancy u) ≤ log 2 := by
    have hnonneg : 0 ≤ ∫ u in Ioi U, occupancy u :=
      integral_nonneg fun _ => sigmoid_nonneg _
    linarith [split hq]
  have hMBound : (∫ u in (0 : ℝ)..U, u * occupancy u) ≤ π ^ 2 / 12 := by
    have hnonneg : 0 ≤ ∫ u in Ioi U, u * occupancy u :=
      setIntegral_nonneg measurableSet_Ioi fun u hu =>
        mul_nonneg (hU.trans (le_of_lt hu)) (sigmoid_nonneg _)
    linarith [split hM]
  have hEBound : π ^ 2 / 6 - tailShape U ≤ ∫ u in (0 : ℝ)..U, entropy u := by
    linarith [split hE, htail U hU]
  obtain ⟨hc, _, he, he'⟩ := rightEndpoint_bounds hm hzero hend hstep hwidth
  have hmesh := mul_le_mul_of_nonneg_left hqBound (show 0 ≤ 2 * δ by positivity)
  change rightEndpointCost t m ≤
    2 * (∫ u in (0 : ℝ)..U, u * occupancy u) + 2 * δ * (∫ u in (0 : ℝ)..U, occupancy u) at hc
  have he'' := he.trans he'
  change 2 * (∫ u in (0 : ℝ)..U, entropy u) - rightEndpointEntropy t m ≤ 2 * δ * log 2 at he''
  constructor
  · linarith
  · unfold tailShape at hEBound
    linarith

/-- For any two positive tolerances, one fixed uniform grid achieves both bounds. -/
theorem exists_uniform_rightEndpoint_grid {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ (U : ℝ) (m : ℕ),
      1 ≤ U ∧ 0 < m ∧
      rightEndpointCost (fun i => (i : ℝ) * (U / m)) m ≤ (π ^ 2 / 6) * (1 + η / 2) ∧
      (2 : ℝ) * (π ^ 2 / 6) - ρ ≤ rightEndpointEntropy (fun i => (i : ℝ) * (U / m)) m := by
  have hA : 0 < π ^ 2 / 6 := by positivity
  have hlog : 0 < log 2 := Real.log_pos (by norm_num)
  have hsmall := (tendsto_order.1 tendsto_tailShape).2 _ (show 0 < ρ / 4 by positivity)
  obtain ⟨U, hU, htail⟩ := ((eventually_ge_atTop (1 : ℝ)).and hsmall).exists
  let δ := min ((π ^ 2 / 6) * η / (4 * log 2)) (ρ / (4 * log 2))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_gt (U / δ)
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hmR : 0 < (m : ℝ) := (div_pos hUpos hδ).trans hm
  have hmN : 0 < m := by exact_mod_cast hmR
  have hmesh : U / (m : ℝ) ≤ δ := by
    apply (div_le_iff₀ hmR).2
    exact (mul_comm (m : ℝ) δ) ▸ ((div_lt_iff₀ hδ).1 hm).le
  let t (i : ℕ) : ℝ := (i : ℝ) * (U / m)
  have hzero : t 0 = 0 := by simp [t]
  have hend : t m = U := by dsimp [t]; field_simp
  have hwidth (i : ℕ) : t (i + 1) - t i = U / m := by
    push_cast [t]
    ring
  obtain ⟨hc, he⟩ := rightEndpoint_explicit_bounds hmN hzero hend
    (fun i _ => hwidth i ▸ div_pos hUpos hmR) (fun i _ => hwidth i ▸ hmesh)
  have hcost := (le_div_iff₀ (by positivity : 0 < 4 * log 2)).1
    (min_le_left ((π ^ 2 / 6) * η / (4 * log 2)) (ρ / (4 * log 2)))
  have hent := (le_div_iff₀ (by positivity : 0 < 4 * log 2)).1
    (min_le_right ((π ^ 2 / 6) * η / (4 * log 2)) (ρ / (4 * log 2)))
  refine ⟨U, m, hU, hmN, ?_, ?_⟩
  · calc
      _ ≤ _ := hc
      _ ≤ _ := by linarith
  · change tailShape U < ρ / 4 at htail
    unfold tailShape at htail
    exact (show (2 : ℝ) * (π ^ 2 / 6) - ρ ≤
      (2 : ℝ) * (π ^ 2 / 6) - 2 * (U + 2) * exp (-U) - 2 * δ * log 2 by linarith).trans he

end D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid
