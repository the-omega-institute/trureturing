/- GID: D5/S3/Entropy/LopesOliveiraFullTail
   generality: G
   mirror-B: D5/B/S3/Entropy/LopesOliveiraFullTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full-future binary entropy attains all-law pressure away from every invariant law. -/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
open MeasureTheory
noncomputable section
namespace D5.S3.Entropy.LopesOliveiraFullTail
abbrev Omega := ℕ → Bool
def shift (x : Omega) : Omega := fun n => x (n + 1)
def point (b : Bool) : Omega := fun n => if n = 0 then b else false
def tailSigma : MeasurableSpace Omega := (inferInstance : MeasurableSpace Omega).comap shift
def law : Measure Omega := (2 : ENNReal)⁻¹ • Measure.dirac (point false) +
  (2 : ENNReal)⁻¹ • Measure.dirac (point true)
instance : IsProbabilityMeasure law := by
  constructor
  simp only [law, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  simpa only [one_div] using ENNReal.add_halves 1
private lemma shift_measurable : Measurable shift :=
  Measurable.of_eval fun n => measurable_pi_apply (n + 1)
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
    funext n
    simp [shift, point]
  simp only [Set.mem_preimage, h]
def firstIndicator (b : Bool) (x : Omega) : ℝ := if x 0 = b then 1 else 0
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
      cases b <;> simp [h0, h1, firstIndicator, point]
    · have h1 : point true ∉ s := mt h.mpr h0
      simp [h0, h1]
  · exact stronglyMeasurable_const.aestronglyMeasurable

def niEntropy (rho : Measure Omega) : ℝ :=
  ∫ x, ∑ b : Bool, Real.negMulLog ((rho[firstIndicator b | tailSigma]) x) ∂rho
private lemma law_entropy : niEntropy law = Real.log 2 := by
  have h0 := conditional_first false
  have h1 := conditional_first true
  unfold niEntropy
  calc
    _ = ∫ _ : Omega, (2 * Real.negMulLog (1/2 : ℝ)) ∂law := by
      apply integral_congr_ae
      filter_upwards [h0, h1] with x hx0 hx1
      simp [hx0, hx1]
      ring
    _ = Real.log 2 := by
      simp [Real.negMulLog]
private lemma firstIndicator_measurable (b : Bool) : Measurable (firstIndicator b) := by
  have hm : Measurable (fun x : Omega => x 0) := measurable_pi_apply 0
  have hs : MeasurableSet {x : Omega | x 0 = b} := hm (measurableSet_singleton b)
  unfold firstIndicator
  exact Measurable.ite hs measurable_const measurable_const

private lemma law_noninvariant : Measure.map shift law ≠ law := by
  intro h
  have hh := congrArg (fun rho : Measure Omega => ∫ x, firstIndicator false x ∂rho) h
  rw [integral_map shift_measurable.aemeasurable
    (firstIndicator_measurable false).aestronglyMeasurable] at hh
  simp only [integral_law] at hh
  norm_num [firstIndicator, shift, point] at hh

def gapTest (x : Omega) : ℝ :=
  (firstIndicator false (shift x) - firstIndicator false x) / 4
private lemma law_gapTest : ∫ x, gapTest x ∂law = 1/8 := by
  rw [integral_law]
  norm_num [gapTest, firstIndicator, shift, point]
private lemma firstIndicator_integrable (rho : Measure Omega) [IsProbabilityMeasure rho] (b : Bool) :
    Integrable (firstIndicator b) rho := by
  apply Integrable.of_bound (firstIndicator_measurable b).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    unfold firstIndicator
    split_ifs <;> norm_num
private lemma entropy_le_log_two (rho : Measure Omega) [IsProbabilityMeasure rho] :
    niEntropy rho ≤ Real.log 2 := by
  have hi : firstIndicator false + firstIndicator true = (fun _ : Omega => (1 : ℝ)) := by
    funext x
    cases h : x 0 <;> simp [firstIndicator, h]
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
  calc
    niEntropy rho ≤ ∫ _ : Omega, Real.log 2 ∂rho :=
      integral_mono_of_nonneg (hp.mono fun x hx => hx.1) (integrable_const _)
        (hp.mono fun x hx => hx.2)
    _ = Real.log 2 := by simp
def pressureValues (phi : Omega → ℝ) : Set ℝ :=
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
local instance : MetricSpace Omega := PiNat.metricSpace (E := fun _ => Bool)

def sourceDistance (x y : Omega) : ℝ := dist x y / 2

private lemma sourceDistance_nonneg (x y : Omega) : 0 ≤ sourceDistance x y :=
  div_nonneg dist_nonneg (by norm_num)

private lemma sourceDistance_le (x y : Omega) : sourceDistance x y ≤ 1/2 := by
  exact div_le_div_of_nonneg_right (PiNat.dist_le_one x y) (by norm_num)

private lemma sourceDistance_measurable : Measurable (fun p : Omega × Omega =>
    sourceDistance p.1 p.2) :=
  (continuous_dist.div_const 2).measurable

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
  rw [integral_div, integral_sub]
  · rw [heq, sub_self, zero_div]
  · rw [← hinv]
    exact (firstIndicator_integrable rho false).comp_measurable
      shift_measurable
  · exact firstIndicator_integrable rho false

private lemma gapTest_lipschitz (x y : Omega) :
    |gapTest x - gapTest y| ≤ sourceDistance x y := by
  by_cases h0 : x 0 = y 0
  · by_cases h1 : x 1 = y 1
    · have heq : gapTest x = gapTest y := by
        simp [gapTest, firstIndicator, shift, h0, h1]
      rw [heq, sub_self, abs_zero]
      exact sourceDistance_nonneg x y
    · have hlower : (1/2 : ℝ) ^ 1 ≤ dist x y := by
        by_contra h
        have he := PiNat.apply_eq_of_dist_lt (lt_of_not_ge h) (le_refl 1)
        exact h1 he
      have htest : |gapTest x - gapTest y| ≤ (1/4 : ℝ) := by
        cases hx0 : x 0 <;> cases hx1 : x 1 <;>
          cases hy0 : y 0 <;> cases hy1 : y 1 <;>
          norm_num [gapTest, firstIndicator, shift, hx0, hx1, hy0, hy1] at *
      exact htest.trans (by unfold sourceDistance; norm_num at hlower ⊢; linarith)
  · have hlower : (1/2 : ℝ) ^ 0 ≤ dist x y := by
      by_contra h
      have he := PiNat.apply_eq_of_dist_lt (lt_of_not_ge h) (le_refl 0)
      exact h0 he
    have htest : |gapTest x - gapTest y| ≤ (1/2 : ℝ) := by
      cases hx0 : x 0 <;> cases hx1 : x 1 <;>
        cases hy0 : y 0 <;> cases hy1 : y 1 <;>
        norm_num [gapTest, firstIndicator, shift, hx0, hx1, hy0, hy1]
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

/-- The complete-future pressure maximizer stays a positive transport distance from
    every invariant target. This is an obstruction lemma, not a KS-equilibrium theorem. -/
theorem full_tail_transport_obstruction (rho : Measure Omega) [IsProbabilityMeasure rho]
    (hinv : Measure.map shift rho = rho) :
    niPressure (fun _ => -Real.log 2) = 0 ∧ niEntropy law = Real.log 2 ∧
    niPressure (fun _ => -Real.log 2) - niEntropy law -
      (∫ _ : Omega, -Real.log 2 ∂law) = 0 ∧
    1/8 ≤ wassersteinOne law rho := by
  refine ⟨pressure_constant, law_entropy, actual_law_deficit, ?_⟩
  apply le_csInf
  · exact ⟨∫ p, sourceDistance p.1 p.2 ∂(law.prod rho), law.prod rho,
      coupling_exists law rho, rfl⟩
  · rintro v ⟨pi, hpi, rfl⟩
    exact coupling_cost_lower rho hinv pi hpi

end D5.S3.Entropy.LopesOliveiraFullTail
