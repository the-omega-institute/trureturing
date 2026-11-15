/- GID: D5/S3/Entropy/LopesOliveiraFullTail
   generality: G
   mirror-B: D5/B/S3/Entropy/LopesOliveiraFullTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full-future binary entropy attains all-law pressure away from every invariant law. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30545. -/

import D5.S3.Entropy.LopesOliveiraSource
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open MeasureTheory
noncomputable section
namespace D5.S3.Entropy.LopesOliveiraFullTail
/-- The source alphabet {1,2}, with its inherited discrete topology. -/
abbrev Symbol := LopesOliveiraSource.Symbol 2
/-- Source coordinates are numbered 1,2,... . -/
abbrev Omega := LopesOliveiraSource.Omega 2

private def symbolEquiv : Bool ≃ᵐ Symbol where
  toFun b := if b then ⟨2, by simp⟩ else ⟨1, by simp⟩
  invFun j := decide (j.val = 2)
  left_inv b := by cases b <;> rfl
  right_inv j := by
    rcases j with ⟨j, hj⟩
    have h : j = 1 ∨ j = 2 := by simp only [Finset.mem_Icc] at hj; omega
    rcases h with rfl | rfl <;> rfl
  measurable_toFun := measurable_of_finite _
  measurable_invFun := measurable_of_finite _

/-- Index and symbol reencoding, with both directions measurable. -/
def coordinateEquiv : (ℕ → Bool) ≃ᵐ Omega :=
  MeasurableEquiv.arrowCongr' Equiv.pnatEquivNat.symm symbolEquiv

private abbrev code (x : Omega) : ℕ → Bool := coordinateEquiv.symm x

def shift (x : Omega) : Omega := fun i => x ⟨i.val + 1, by omega⟩
private def point (b : Bool) : Omega := coordinateEquiv (fun n => if n = 0 then b else false)

@[simp] private lemma code_point (b : Bool) :
    code (point b) = (fun n => if n = 0 then b else false) :=
  coordinateEquiv.symm_apply_apply _

def tailSigma : MeasurableSpace Omega := (inferInstance : MeasurableSpace Omega).comap shift
def law : Measure Omega := (2 : ENNReal)⁻¹ • Measure.dirac (point false) +
  (2 : ENNReal)⁻¹ • Measure.dirac (point true)
instance instProbabilityLaw : IsProbabilityMeasure law := by
  constructor
  simp only [law, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  simpa only [one_div] using ENNReal.add_halves 1
private lemma shift_measurable : Measurable shift :=
  Measurable.of_eval fun (i : ℕ+) =>
    measurable_pi_apply (⟨i.val + 1, by omega⟩ : ℕ+)
private lemma integrable_law (f : Omega → ℝ) : Integrable f law := by
  apply integrable_add_measure.mpr
  constructor <;> exact (integrable_dirac (by simp)).smul_measure (by norm_num)
private lemma integral_law (f : Omega → ℝ) :
    ∫ x, f x ∂law = (f (point false) + f (point true)) / 2 := by
  unfold law
  rw [integral_add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))
    ((integrable_dirac (by simp)).smul_measure (by norm_num))]
  simp [integral_smul_measure]
  ring
private lemma tail_membership (s : Set Omega) (hs : MeasurableSet[tailSigma] s) :
    point false ∈ s ↔ point true ∈ s := by
  rcases hs with ⟨t, ht, rfl⟩
  have h : shift (point false) = shift (point true) := by
    apply coordinateEquiv.symm.injective
    funext n
    change code (point false) (n + 1) = code (point true) (n + 1)
    simp
  simp only [Set.mem_preimage, h]
def firstIndicator (b : Bool) (x : Omega) : ℝ := if code x 0 = b then 1 else 0
private lemma conditional_first (b : Bool) :
    law[firstIndicator b | tailSigma] =ᵐ[law] (fun _ => (1/2 : ℝ)) := by
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq shift_measurable.comap_le (integrable_law _)
  · intro s hs hfin
    exact (integrable_const _).integrableOn
  · intro s hs hfin
    rw [← integral_indicator (shift_measurable.comap_le s hs),
      ← integral_indicator (shift_measurable.comap_le s hs), integral_law, integral_law]
    have h := tail_membership s hs
    by_cases h0 : point false ∈ s
    · have h1 := h.mp h0
      cases b <;> simp [h0, h1, firstIndicator, code_point]
    · have h1 : point true ∉ s := mt h.mpr h0
      simp [h0, h1]
  · exact stronglyMeasurable_const.aestronglyMeasurable

/-- The source first-coordinate indicator, indexed by the original symbols. -/
def sourceIndicator (j : Symbol) (x : Omega) : ℝ := if x 1 = j then 1 else 0

/-- Unrestricted conditional-first entropy, using the entire future sigma-algebra. -/
def niEntropy (rho : Measure Omega) : ℝ :=
  ∫ x, ∑ j : Symbol, Real.negMulLog ((rho[sourceIndicator j | tailSigma]) x) ∂rho

private lemma indicator_reindex (b : Bool) :
    sourceIndicator (symbolEquiv b) = firstIndicator b := by
  funext x
  change (if x 1 = symbolEquiv b then (1 : ℝ) else 0) =
    (if symbolEquiv.symm (x 1) = b then 1 else 0)
  simp only [symbolEquiv.symm_apply_eq]

private lemma entropy_integrand_reindex (rho : Measure Omega) (x : Omega) :
    (∑ j : Symbol, Real.negMulLog ((rho[sourceIndicator j | tailSigma]) x)) =
      ∑ b : Bool, Real.negMulLog ((rho[firstIndicator b | tailSigma]) x) := by
  rw [← Equiv.sum_comp symbolEquiv.toEquiv]
  simp only [MeasurableEquiv.coe_toEquiv, indicator_reindex]

private lemma entropy_reindex (rho : Measure Omega) :
    niEntropy rho = ∫ x, ∑ b : Bool,
      Real.negMulLog ((rho[firstIndicator b | tailSigma]) x) ∂rho := by
  unfold niEntropy
  simp_rw [entropy_integrand_reindex]

private lemma law_entropy : niEntropy law = Real.log 2 := by
  have h0 := conditional_first false
  have h1 := conditional_first true
  rw [entropy_reindex]
  calc
    _ = ∫ _ : Omega, (2 * Real.negMulLog (1/2 : ℝ)) ∂law := by
      apply integral_congr_ae
      filter_upwards [h0, h1] with x hx0 hx1
      simp [hx0, hx1]
      ring
    _ = Real.log 2 := by
      simp [Real.negMulLog]
private lemma firstIndicator_measurable (b : Bool) : Measurable (firstIndicator b) := by
  have hm : Measurable (fun x : Omega => code x 0) :=
    (measurable_pi_apply 0).comp coordinateEquiv.symm.measurable
  have hs : MeasurableSet {x : Omega | code x 0 = b} := hm (measurableSet_singleton b)
  unfold firstIndicator
  exact Measurable.ite hs measurable_const measurable_const

private def gapTest (x : Omega) : ℝ :=
  (firstIndicator false (shift x) - firstIndicator false x) / 4
private lemma law_gapTest : ∫ x, gapTest x ∂law = 1/8 := by
  rw [integral_law]
  change (((if code (point false) 1 = false then 1 else 0) -
      (if code (point false) 0 = false then 1 else 0)) / 4 +
    ((if code (point true) 1 = false then 1 else 0) -
      (if code (point true) 0 = false then 1 else 0)) / 4) / 2 = 1/8
  norm_num
private lemma firstIndicator_integrable (rho : Measure Omega) [IsProbabilityMeasure rho] (b : Bool) :
    Integrable (firstIndicator b) rho := by
  apply Integrable.of_bound (firstIndicator_measurable b).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    unfold firstIndicator
    split_ifs <;> norm_num
private lemma entropy_integrand_bounds (rho : Measure Omega) [IsProbabilityMeasure rho] :
    ∀ᵐ x ∂rho,
      0 ≤ (∑ b : Bool, Real.negMulLog ((rho[firstIndicator b | tailSigma]) x)) ∧
      (∑ b : Bool, Real.negMulLog ((rho[firstIndicator b | tailSigma]) x)) ≤ Real.log 2 := by
  have hi : firstIndicator false + firstIndicator true = (fun _ : Omega => (1 : ℝ)) := by
    funext x
    cases h : code x 0 <;> simp [firstIndicator, h]
  have hadd := condExp_add (firstIndicator_integrable rho false)
    (firstIndicator_integrable rho true) tailSigma
  rw [hi] at hadd
  have hm : tailSigma ≤ (inferInstance : MeasurableSpace Omega) := shift_measurable.comap_le
  rw [condExp_const hm] at hadd
  have h0 := condExp_nonneg (m := tailSigma) (μ := rho)
    (Filter.Eventually.of_forall (fun x => show 0 ≤ firstIndicator false x by unfold firstIndicator; split_ifs <;> norm_num))
  have h1 := condExp_nonneg (m := tailSigma) (μ := rho)
    (Filter.Eventually.of_forall (fun x => show 0 ≤ firstIndicator true x by unfold firstIndicator; split_ifs <;> norm_num))
  have hp : ∀ᵐ x ∂rho,
      0 ≤ (∑ b : Bool, Real.negMulLog ((rho[firstIndicator b | tailSigma]) x)) ∧
      (∑ b : Bool, Real.negMulLog ((rho[firstIndicator b | tailSigma]) x)) ≤ Real.log 2 := by
    filter_upwards [hadd, h0, h1] with x hx hx0 hx1
    simp only [Pi.add_apply] at hx
    simp only [Pi.zero_apply] at hx0 hx1
    have heq : (rho[firstIndicator true | tailSigma]) x =
        1 - (rho[firstIndicator false | tailSigma]) x := by linarith
    have hid : (∑ b : Bool, Real.negMulLog ((rho[firstIndicator b | tailSigma]) x)) =
        Real.binEntropy ((rho[firstIndicator false | tailSigma]) x) := by
      rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      simp [heq, add_comm]
    rw [hid]
    exact ⟨Real.binEntropy_nonneg hx0 (by linarith), Real.binEntropy_le_log_two⟩
  exact hp

private lemma entropy_integrable (rho : Measure Omega) [IsProbabilityMeasure rho] :
    Integrable (fun x => ∑ b : Bool,
      Real.negMulLog ((rho[firstIndicator b | tailSigma]) x)) rho := by
  have hm : tailSigma ≤ (inferInstance : MeasurableSpace Omega) :=
    shift_measurable.comap_le
  have hs : StronglyMeasurable (fun x => ∑ b : Bool,
      Real.negMulLog ((rho[firstIndicator b | tailSigma]) x)) := by
    have hc (b : Bool) : StronglyMeasurable (rho[firstIndicator b | tailSigma]) :=
      stronglyMeasurable_condExp.mono hm
    exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun b _ =>
        Real.continuous_negMulLog.comp_stronglyMeasurable (hc b))
  apply Integrable.of_bound hs.aestronglyMeasurable (Real.log 2)
  filter_upwards [entropy_integrand_bounds rho] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

private lemma entropy_le_log_two (rho : Measure Omega) [IsProbabilityMeasure rho] :
    niEntropy rho ≤ Real.log 2 := by
  have hp := entropy_integrand_bounds rho
  rw [entropy_reindex]
  calc
    (∫ x, ∑ b : Bool, Real.negMulLog ((rho[firstIndicator b | tailSigma]) x) ∂rho) ≤ ∫ _ : Omega, Real.log 2 ∂rho :=
      integral_mono_of_nonneg (hp.mono fun x hx => hx.1) (integrable_const _)
        (hp.mono fun x hx => hx.2)
    _ = Real.log 2 := by simp
private def pressureValues (phi : Omega → ℝ) : Set ℝ :=
  {v | ∃ rho : Measure Omega, IsProbabilityMeasure rho ∧
    v = (∫ x, phi x ∂rho) + niEntropy rho}
def niPressure (phi : Omega → ℝ) : ℝ := sSup (pressureValues phi)
private lemma pressure_constant : niPressure (fun _ => -Real.log 2) = 0 := by
  have hbound : ∀ v ∈ pressureValues (fun _ => -Real.log 2), v ≤ 0 := by
    intro v hv
    rcases hv with ⟨rho, hprob, rfl⟩
    letI : IsProbabilityMeasure rho := hprob
    have hh := entropy_le_log_two rho
    simp only [integral_const, probReal_univ, one_smul]
    linarith
  have hzero : 0 ∈ pressureValues (fun _ => -Real.log 2) := by
    refine ⟨law, inferInstance, ?_⟩
    simp [law_entropy]
  exact le_antisymm (csSup_le ⟨0, hzero⟩ hbound) (le_csSup ⟨0, hbound⟩ hzero)
private lemma actual_law_deficit :
    niPressure (fun _ => -Real.log 2) - niEntropy law -
      (∫ _ : Omega, -Real.log 2 ∂law) = 0 := by
  simp [pressure_constant, law_entropy]

/- The product topology is unchanged by this PiNat metric. Source coordinate
   number n + 1 corresponds to internal coordinate n, hence the factor 1/2. -/
local instance : MetricSpace (ℕ → Bool) := PiNat.metricSpace (E := fun _ => Bool)

private def coordinateHomeomorph : (ℕ → Bool) ≃ₜ Omega where
  toEquiv := coordinateEquiv.toEquiv
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (continuous_of_discreteTopology (f := symbolEquiv)).comp
      (continuous_apply (Equiv.pnatEquivNat i))
  continuous_invFun := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology (f := symbolEquiv.symm)).comp
      (continuous_apply (Nat.succPNat n))

def sourceDistance (x y : Omega) : ℝ := dist (code x) (code y) / 2

private lemma sourceDistance_nonneg (x y : Omega) : 0 ≤ sourceDistance x y :=
  div_nonneg dist_nonneg (by norm_num)

private lemma sourceDistance_le (x y : Omega) : sourceDistance x y ≤ 1/2 := by
  exact div_le_div_of_nonneg_right (PiNat.dist_le_one (code x) (code y)) (by norm_num)

/-- The source metric, with exactly the original product topology. -/
def sourceMetric : MetricSpace Omega :=
  MetricSpace.ofDistTopology sourceDistance
    (fun x => by simp [sourceDistance])
    (fun x y => by simp only [sourceDistance, dist_comm])
    (fun x y z => by
      have h := dist_triangle (code x) (code y) (code z)
      dsimp [sourceDistance]
      linarith)
    (fun s => by
      rw [← coordinateHomeomorph.isOpen_preimage, Metric.isOpen_iff]
      constructor
      · intro h x hx
        have hx2 : code x ∈ coordinateHomeomorph ⁻¹' s := by
          simpa [coordinateHomeomorph, code] using hx
        obtain ⟨ε, hε, hball⟩ := h (code x) hx2
        refine ⟨ε / 2, by positivity, ?_⟩
        intro y hy
        have hnear : code y ∈ Metric.ball (code x) ε := by
          simp only [Metric.mem_ball, dist_comm]
          dsimp [sourceDistance] at hy
          linarith
        have hh := hball hnear
        simpa [coordinateHomeomorph, code] using hh
      · intro h z hz
        obtain ⟨ε, hε, hball⟩ := h (coordinateEquiv z) hz
        refine ⟨2 * ε, by positivity, ?_⟩
        intro w hw
        apply hball (coordinateEquiv w)
        dsimp [sourceDistance]
        simp only [code, coordinateEquiv.symm_apply_apply]
        have hw2 : dist z w < 2 * ε := by simpa [Metric.mem_ball, dist_comm] using hw
        linarith)
    (fun x y h => coordinateEquiv.symm.injective (by
      apply eq_of_dist_eq_zero
      dsimp [sourceDistance] at h
      linarith))

private lemma source_borel : @borel Omega sourceMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : MeasurableSpace Omega) := by
  exact (BorelSpace.measurable_eq : (inferInstance : MeasurableSpace Omega) =
    borel Omega).symm

private lemma source_first_difference (x y : Omega) (hne : x ≠ y) :
    sourceDistance x y = (1/2 : ℝ) ^ (PiNat.firstDiff (code x) (code y) + 1) := by
  unfold sourceDistance
  rw [PiNat.dist_eq_of_ne (coordinateEquiv.symm.injective.ne hne), pow_succ]
  ring

private lemma sourceDistance_measurable : Measurable (fun p : Omega × Omega =>
    sourceDistance p.1 p.2) :=
  (measurable_dist.comp (coordinateEquiv.symm.measurable.prodMap
    coordinateEquiv.symm.measurable)).div_const 2

private lemma gapTest_measurable : Measurable gapTest :=
  ((firstIndicator_measurable false).comp shift_measurable |>.sub
    (firstIndicator_measurable false)).div_const 4

private lemma gapTest_integrable (rho : Measure Omega) [IsProbabilityMeasure rho] :
    Integrable gapTest rho := by
  apply Integrable.of_bound gapTest_measurable.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    simp only [gapTest, firstIndicator]
    split_ifs <;> norm_num

private lemma invariant_gapTest (rho : Measure Omega) [IsProbabilityMeasure rho]
    (hinv : Measure.map shift rho = rho) : ∫ x, gapTest x ∂rho = 0 := by
  have heq : (∫ x, firstIndicator false (shift x) ∂rho) =
      ∫ x, firstIndicator false x ∂rho := by
    rw [← integral_map shift_measurable.aemeasurable
      (firstIndicator_measurable false).aestronglyMeasurable, hinv]
  change (∫ x, (firstIndicator false (shift x) - firstIndicator false x) / 4 ∂rho) = 0
  have hi : Integrable (firstIndicator false) (Measure.map shift rho) := by
    rw [hinv]
    exact firstIndicator_integrable rho false
  have hi2 : Integrable (fun x => firstIndicator false (shift x)) rho :=
    hi.comp_measurable shift_measurable
  rw [integral_div, integral_sub hi2 (firstIndicator_integrable rho false),
    heq, sub_self, zero_div]

private lemma gapTest_lipschitz (x y : Omega) :
    |gapTest x - gapTest y| ≤ sourceDistance x y := by
  by_cases h0 : code x 0 = code y 0
  · by_cases h1 : code x 1 = code y 1
    · have heq : gapTest x = gapTest y := by
        change ((if code x 1 = false then 1 else 0) -
          (if code x 0 = false then 1 else 0)) / 4 =
          ((if code y 1 = false then 1 else 0) -
          (if code y 0 = false then 1 else 0)) / 4
        simp [h0, h1]
      rw [heq, sub_self, abs_zero]
      exact sourceDistance_nonneg x y
    · have hlower : (1/2 : ℝ) ^ 1 ≤ dist (code x) (code y) := by
        by_contra h
        have he := PiNat.apply_eq_of_dist_lt (lt_of_not_ge h) (le_refl 1)
        exact h1 he
      have htest : |gapTest x - gapTest y| ≤ (1/4 : ℝ) := by
        change |((if code x 1 = false then 1 else 0) -
          (if code x 0 = false then 1 else 0)) / 4 - ((if code y 1 = false then 1 else 0) -
          (if code y 0 = false then 1 else 0)) / 4| ≤ (1/4 : ℝ)
        cases hx0 : code x 0 <;> cases hx1 : code x 1 <;>
          cases hy0 : code y 0 <;> cases hy1 : code y 1 <;>
          simp_all <;> norm_num
      exact htest.trans (by unfold sourceDistance; norm_num at hlower ⊢; linarith)
  · have hlower : (1/2 : ℝ) ^ 0 ≤ dist (code x) (code y) := by
      by_contra h
      have he := PiNat.apply_eq_of_dist_lt (lt_of_not_ge h) (le_refl 0)
      exact h0 he
    have htest : |gapTest x - gapTest y| ≤ (1/2 : ℝ) := by
      change |((if code x 1 = false then 1 else 0) -
          (if code x 0 = false then 1 else 0)) / 4 - ((if code y 1 = false then 1 else 0) -
          (if code y 0 = false then 1 else 0)) / 4| ≤ (1/2 : ℝ)
      cases hx0 : code x 0 <;> cases hx1 : code x 1 <;>
        cases hy0 : code y 0 <;> cases hy1 : code y 1 <;>
        norm_num [hx0, hx1, hy0, hy1]
    exact htest.trans (by unfold sourceDistance; norm_num at hlower ⊢; linarith)

/-- All probability couplings, with both actual marginals. -/
def couplings (eta xi : Measure Omega) : Set (Measure (Omega × Omega)) :=
  {pi | IsProbabilityMeasure pi ∧ Measure.map Prod.fst pi = eta ∧
    Measure.map Prod.snd pi = xi}

/-- The infimum of integrals of the source metric over all Borel probability couplings. -/
def wassersteinOne (eta xi : Measure Omega) : ℝ :=
  sInf {v | ∃ pi ∈ couplings eta xi, v = ∫ p, sourceDistance p.1 p.2 ∂pi}

private lemma coupling_exists (eta xi : Measure Omega)
    [IsProbabilityMeasure eta] [IsProbabilityMeasure xi] :
    eta.prod xi ∈ couplings eta xi := by
  exact ⟨inferInstance, by simp, by simp⟩

private lemma coupling_cost_lower (rho : Measure Omega) [IsProbabilityMeasure rho]
    (hinv : Measure.map shift rho = rho) (pi : Measure (Omega × Omega))
    (hpi : pi ∈ couplings law rho) :
    1/8 ≤ ∫ p, sourceDistance p.1 p.2 ∂pi := by
  letI : IsProbabilityMeasure pi := hpi.1
  have hleft : Integrable (fun p : Omega × Omega => gapTest p.1) pi := by
    have h : Integrable gapTest (Measure.map Prod.fst pi) := by
      rw [hpi.2.1]
      exact gapTest_integrable law
    exact h.comp_measurable measurable_fst
  have hright : Integrable (fun p : Omega × Omega => gapTest p.2) pi := by
    have h : Integrable gapTest (Measure.map Prod.snd pi) := by
      rw [hpi.2.2]
      exact gapTest_integrable rho
    exact h.comp_measurable measurable_snd
  have hcost : Integrable (fun p : Omega × Omega => sourceDistance p.1 p.2) pi := by
    apply Integrable.of_bound sourceDistance_measurable.aestronglyMeasurable (1/2)
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sourceDistance_nonneg _ _)]
      exact sourceDistance_le _ _
  have hle := integral_mono (hleft.sub hright) hcost (fun p =>
    (le_abs_self _).trans (gapTest_lipschitz p.1 p.2))
  simp only [Pi.sub_apply] at hle
  rw [integral_sub hleft hright] at hle
  rw [← integral_map measurable_fst.aemeasurable gapTest_measurable.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable gapTest_measurable.aestronglyMeasurable,
    hpi.2.1, hpi.2.2, law_gapTest, invariant_gapTest rho hinv, sub_zero] at hle
  exact hle

/-- The binary encoding preserves the literal source distance. -/
lemma source_distance_eq (x y : Omega) :
    LopesOliveiraSource.distance x y = sourceDistance x y := by
  classical
  change @dist (ℕ → Symbol) PiNat.dist (fun n => x (Nat.succPNat n))
      (fun n => y (Nat.succPNat n)) / 2 =
    @dist (ℕ → Bool) PiNat.dist (coordinateEquiv.symm x) (coordinateEquiv.symm y) / 2
  congr 1
  have hcoord (n : ℕ) : x (Nat.succPNat n) = y (Nat.succPNat n) ↔
      coordinateEquiv.symm x n = coordinateEquiv.symm y n := by
    change _ ↔ symbolEquiv.symm (x (Nat.succPNat n)) =
      symbolEquiv.symm (y (Nat.succPNat n))
    exact symbolEquiv.symm.injective.eq_iff.symm
  have hfun : (fun n => x (Nat.succPNat n)) = (fun n => y (Nat.succPNat n)) ↔
      coordinateEquiv.symm x = coordinateEquiv.symm y := by
    simp only [funext_iff, hcoord]
  change (if (fun n => x (Nat.succPNat n)) ≠ (fun n => y (Nat.succPNat n)) then
    (1/2 : ℝ) ^ PiNat.firstDiff (fun n => x (Nat.succPNat n))
      (fun n => y (Nat.succPNat n)) else 0) =
    (if coordinateEquiv.symm x ≠ coordinateEquiv.symm y then
      (1/2 : ℝ) ^ PiNat.firstDiff (coordinateEquiv.symm x) (coordinateEquiv.symm y) else 0)
  simp only [ne_eq, hfun]
  split_ifs with h
  · rfl
  · congr 1
    have hn : (fun n => x (Nat.succPNat n)) ≠ (fun n => y (Nat.succPNat n)) :=
      mt hfun.mp h
    apply le_antisymm
    · by_contra hnle
      have he := PiNat.apply_eq_of_lt_firstDiff (lt_of_not_ge hnle)
      exact PiNat.apply_firstDiff_ne h ((hcoord _).mp he)
    · by_contra hnle
      have he := PiNat.apply_eq_of_lt_firstDiff (lt_of_not_ge hnle)
      exact PiNat.apply_firstDiff_ne hn ((hcoord _).mpr he)

/-- The complete-future pressure maximizer stays a positive transport distance from
    every invariant target. This is an obstruction lemma, not a KS-equilibrium theorem. -/
theorem full_tail_transport_obstruction (rho : Measure Omega) [IsProbabilityMeasure rho]
    (hinv : Measure.map shift rho = rho) :
    (@borel Omega sourceMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : MeasurableSpace Omega)) ∧
    (∀ x y : Omega, x ≠ y → sourceDistance x y =
      (1/2 : ℝ) ^ (PiNat.firstDiff (coordinateEquiv.symm x) (coordinateEquiv.symm y) + 1)) ∧
    (∀ eta : Measure Omega, IsProbabilityMeasure eta →
      Integrable (fun x => ∑ j : Symbol,
        Real.negMulLog ((eta[sourceIndicator j | tailSigma]) x)) eta) ∧
    niPressure (fun _ => -Real.log 2) = 0 ∧ niEntropy law = Real.log 2 ∧
    niPressure (fun _ => -Real.log 2) - niEntropy law -
      (∫ _ : Omega, -Real.log 2 ∂law) = 0 ∧
    1/8 ≤ wassersteinOne law rho := by
  refine ⟨source_borel, source_first_difference, ?_,
    pressure_constant, law_entropy, actual_law_deficit, ?_⟩
  · intro eta heta
    letI : IsProbabilityMeasure eta := heta
    simpa only [entropy_integrand_reindex] using entropy_integrable eta
  apply le_csInf
  · exact ⟨∫ p, sourceDistance p.1 p.2 ∂(law.prod rho), law.prod rho,
      coupling_exists law rho, rfl⟩
  · rintro v ⟨pi, hpi, rfl⟩
    exact coupling_cost_lower rho hinv pi hpi

end D5.S3.Entropy.LopesOliveiraFullTail
