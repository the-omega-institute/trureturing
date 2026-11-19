module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic

/-! # The scalar optimization for the five-level flagged projective simulator -/

@[expose] public section

namespace D5.S3.Quantum.Measurement.AuricFiveLevelTilt

open Set
open scoped ComplexOrder

/-- Derivative of the first-projector Choi score in its spectator leakage mass. -/
noncomputable def tiltDerivative (r p : ℝ) : ℝ :=
  -1 - 2 * r / Real.sqrt (1 - p) +
    (r ^ 2 - 1) / Real.sqrt (1 + (r ^ 2 - 1) * p)

theorem tiltDerivative_strictAntiOn (r : ℝ) (hr : 1 < r) :
    StrictAntiOn (tiltDerivative r) (Ico 0 1) := by
  intro p hp q hq hpq
  have hr0 : 0 < r := by linarith
  have hweight : 0 < r ^ 2 - 1 := by nlinarith
  have hqp : 0 < Real.sqrt (1 - q) :=
    Real.sqrt_pos.2 (by linarith [hq.2])
  have hlt : Real.sqrt (1 - q) < Real.sqrt (1 - p) :=
    Real.sqrt_lt_sqrt (by linarith [hq.2]) (by linarith)
  have hfirst :
      2 * r / Real.sqrt (1 - p) < 2 * r / Real.sqrt (1 - q) :=
    div_lt_div_of_pos_left (by positivity) hqp hlt
  have hp0 : 0 < Real.sqrt (1 + (r ^ 2 - 1) * p) :=
    Real.sqrt_pos.2 (by nlinarith [mul_nonneg hweight.le hp.1])
  have hsecond :
      (r ^ 2 - 1) / Real.sqrt (1 + (r ^ 2 - 1) * q) ≤
        (r ^ 2 - 1) / Real.sqrt (1 + (r ^ 2 - 1) * p) :=
    div_le_div_of_nonneg_left hweight.le hp0
      (Real.sqrt_le_sqrt (by
        nlinarith [mul_nonneg hweight.le (sub_nonneg.mpr hpq.le)]))
  unfold tiltDerivative
  linarith

private theorem growthRatio_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a / Real.sqrt (1 + a / 50) ≤ b / Real.sqrt (1 + b / 50) := by
  have hb : 0 ≤ b := ha.trans hab
  have hA : 0 < Real.sqrt (1 + a / 50) := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < Real.sqrt (1 + b / 50) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_div_iff₀ hA hB]
  have hdiff : 0 ≤ (b-a) * (a+b+a*b/50) := by positivity
  have hsq : (a * Real.sqrt (1+b/50)) ^ 2 ≤ (b * Real.sqrt (1+a/50)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1+b/50),
      Real.sq_sqrt (by positivity : 0 ≤ 1+a/50)]
    nlinarith
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

theorem existsUnique_tiltDerivative_zero (r : ℝ) (hr : r ∈ Icc (11 / 4) (14 / 5)) :
    ∃! p : ℝ, p ∈ Ioo 0 (1/50) ∧ tiltDerivative r p = 0 := by
  have hr1 : 1 < r := by linarith [hr.1]
  have hweight : 0 < r ^ 2 - 1 := by nlinarith
  have hleft : 0 < tiltDerivative r 0 := by
    simp [tiltDerivative]
    nlinarith [sq_nonneg (r - 11/4), hr.1]
  have hright : tiltDerivative r (1/50) < 0 := by
    have hfirst : (11/2) / Real.sqrt (49/50) ≤ 2*r / Real.sqrt (49/50) :=
      div_le_div_of_nonneg_right (by linarith [hr.1]) (Real.sqrt_nonneg _)
    have hlower : (11/2) / Real.sqrt (49/50) > 11/2 := by
      have hs : Real.sqrt (49/50) < 1 := by
        simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 49/50) (by norm_num : (49/50:ℝ) < 1)
      exact (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))).2 (by linarith)
    have hmax : r ^ 2 - 1 ≤ 171/25 := by
      nlinarith [mul_nonneg (show 0 ≤ 14/5-r by linarith [hr.2])
        (show 0 ≤ 14/5+r by linarith [hr.1])]
    have hsecond := growthRatio_mono hweight.le hmax
    have hupper : (171/25 : ℝ) / Real.sqrt (1 + (171/25 : ℝ)/50) < 13/2 := by
      have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1 + (171/25:ℝ)/50)
      apply (div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num))).2
      nlinarith [Real.sqrt_nonneg (1 + (171/25:ℝ)/50)]
    unfold tiltDerivative
    rw [show (1 : ℝ) - 1/50 = 49/50 by norm_num,
      show (r^2-1) * (1/50) = (r^2-1)/50 by ring]
    linarith
  have hcont : ContinuousOn (tiltDerivative r) (Icc 0 (1/50)) := by
    unfold tiltDerivative
    refine ((continuousOn_const.sub (continuousOn_const.div
      (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn ?_)).add
      (continuousOn_const.div
        (Real.continuous_sqrt.comp (continuous_const.add
          (continuous_const.mul continuous_id))).continuousOn ?_))
    · intro p hp
      change Real.sqrt (1 - p) ≠ 0
      exact (Real.sqrt_pos.2 (by linarith [hp.2])).ne'
    · intro p hp
      change Real.sqrt (1 + (r ^ 2 - 1) * p) ≠ 0
      exact (Real.sqrt_pos.2 (by nlinarith [mul_nonneg hweight.le hp.1])).ne'
  obtain ⟨p, hp, hpzero⟩ := intermediate_value_Icc'
    (by norm_num : (0:ℝ) ≤ 1/50) hcont ⟨hright.le, hleft.le⟩
  have hpOpen : p ∈ Ioo 0 (1/50) := by
    refine ⟨lt_of_le_of_ne hp.1 ?_, lt_of_le_of_ne hp.2 ?_⟩
    · intro h
      rw [← h] at hpzero
      linarith
    · intro h
      rw [h] at hpzero
      linarith
  refine ⟨p, ⟨hpOpen, hpzero⟩, ?_⟩
  intro q hq
  have hqUnit : q ∈ Ico 0 1 := ⟨hq.1.1.le, by linarith [hq.1.2]⟩
  have hpUnit : p ∈ Ico 0 1 := ⟨hp.1, by linarith [hp.2]⟩
  exact (tiltDerivative_strictAntiOn r hr1).injOn hqUnit hpUnit (hq.2.trans hpzero.symm)

abbrev WitnessInterval := ↥(Icc (11 / 4 : ℝ) (14 / 5))

/-- The uniquely optimal leakage mass at the specified Choi witness. -/
noncomputable def tiltMass (r : WitnessInterval) : ℝ :=
  (existsUnique_tiltDerivative_zero r r.property).exists.choose

theorem tiltMass_spec (r : WitnessInterval) :
    tiltMass r ∈ Ioo 0 (1 / 50) ∧ tiltDerivative r (tiltMass r) = 0 :=
  (existsUnique_tiltDerivative_zero r r.property).exists.choose_spec

private theorem continuous_derivative_fixed_mass {p : ℝ} (hp : p ∈ Ico 0 1) :
    Continuous (fun r : WitnessInterval => tiltDerivative r p) := by
  have hs : ∀ r : WitnessInterval,
      Real.sqrt (1 + ((r : ℝ) ^ 2 - 1) * p) ≠ 0 := by
    intro r
    have hr : (11 / 4 : ℝ) ≤ r := r.property.1
    have hweight : 0 ≤ (r : ℝ) ^ 2 - 1 := by nlinarith
    apply (Real.sqrt_pos.2 _).ne'
    linarith [mul_nonneg hweight hp.1]
  have hnum : Continuous (fun r : WitnessInterval => (r : ℝ) ^ 2 - 1) := by fun_prop
  have hden : Continuous
      (fun r : WitnessInterval => Real.sqrt (1 + ((r : ℝ) ^ 2 - 1) * p)) := by fun_prop
  have hfirst : Continuous (fun r : WitnessInterval =>
      -1 - 2 * (r : ℝ) / Real.sqrt (1 - p)) := by fun_prop
  exact hfirst.add (hnum.div hden hs)

theorem tiltMass_continuous : Continuous tiltMass := by
  rw [continuous_iff_continuousAt]
  intro r
  have hr1 (t : WitnessInterval) : (1 : ℝ) < t := by linarith [t.property.1]
  have hUnit (t : WitnessInterval) : tiltMass t ∈ Ico 0 1 :=
    ⟨(tiltMass_spec t).1.1.le, by linarith [(tiltMass_spec t).1.2]⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases hnonneg : 0 ≤ a
    · have haUnit : a ∈ Ico 0 1 := ⟨hnonneg, ha.trans (hUnit r).2⟩
      have hpos : 0 < tiltDerivative r a := by
        rw [← (tiltMass_spec r).2]
        exact (tiltDerivative_strictAntiOn r (hr1 r)) haUnit (hUnit r) ha
      filter_upwards [continuousAt_const.eventually_lt
        (continuous_derivative_fixed_mass haUnit).continuousAt hpos] with t ht
      by_contra! hle
      have haLe := (tiltDerivative_strictAntiOn t (hr1 t)).antitoneOn (hUnit t) haUnit hle
      rw [(tiltMass_spec t).2] at haLe
      exact (not_lt_of_ge haLe) ht
    · exact Filter.Eventually.of_forall fun t =>
        (lt_of_not_ge hnonneg).trans (tiltMass_spec t).1.1
  · intro b hb
    by_cases hlt : b < 1
    · have hbUnit : b ∈ Ico 0 1 := ⟨(lt_of_le_of_lt (hUnit r).1 hb).le, hlt⟩
      have hneg : tiltDerivative r b < 0 := by
        rw [← (tiltMass_spec r).2]
        exact (tiltDerivative_strictAntiOn r (hr1 r)) (hUnit r) hbUnit hb
      filter_upwards [(continuous_derivative_fixed_mass hbUnit).continuousAt.eventually_lt
        continuousAt_const hneg] with t ht
      by_contra! hle
      have hbLe := (tiltDerivative_strictAntiOn t (hr1 t)).antitoneOn hbUnit (hUnit t) hle
      rw [(tiltMass_spec t).2] at hbLe
      exact (not_lt_of_ge hbLe) ht
    · exact Filter.Eventually.of_forall fun t => (hUnit t).2.trans_le (le_of_not_gt hlt)

private theorem derivative_lower {r p cosineFloor normCeiling : ℝ}
    (hr : 1 < r) (hcos : 0 < cosineFloor)
    (hcosFloor : cosineFloor ^ 2 ≤ 1 - p)
    (hnorm : 0 ≤ normCeiling)
    (hnormCeiling : 1 + (r ^ 2 - 1) * p ≤ normCeiling ^ 2)
    (hp : 0 ≤ p) :
    -1 - 2 * r / cosineFloor + (r ^ 2 - 1) / normCeiling ≤ tiltDerivative r p := by
  have hw : 0 ≤ r ^ 2 - 1 := by nlinarith
  have hrealcos := Real.le_sqrt_of_sq_le hcosFloor
  have hrealnorm := (Real.sqrt_le_left hnorm).2 hnormCeiling
  have hnpos : 0 < Real.sqrt (1 + (r ^ 2 - 1) * p) :=
    Real.sqrt_pos.2 (by linarith [mul_nonneg hw hp])
  have h₁ := div_le_div_of_nonneg_left (show 0 ≤ 2 * r by linarith) hcos hrealcos
  have h₂ := div_le_div_of_nonneg_left hw hnpos hrealnorm
  unfold tiltDerivative
  linarith

private theorem derivative_upper {r p cosineCeiling normFloor : ℝ}
    (hr : 1 < r) (hcos : 0 ≤ cosineCeiling)
    (hcosCeiling : 1 - p ≤ cosineCeiling ^ 2)
    (hnorm : 0 < normFloor)
    (hnormFloor : normFloor ^ 2 ≤ 1 + (r ^ 2 - 1) * p)
    (hp : p < 1) :
    tiltDerivative r p ≤ -1 - 2 * r / cosineCeiling + (r ^ 2 - 1) / normFloor := by
  have hw : 0 ≤ r ^ 2 - 1 := by nlinarith
  have hrealcos := (Real.sqrt_le_left hcos).2 hcosCeiling
  have hrealnorm := Real.le_sqrt_of_sq_le hnormFloor
  have hcpos : 0 < Real.sqrt (1 - p) := Real.sqrt_pos.2 (sub_pos.mpr hp)
  have h₁ := div_le_div_of_nonneg_left (show 0 ≤ 2 * r by linarith) hcpos hrealcos
  have h₂ := div_le_div_of_nonneg_left hw hnorm hrealnorm
  unfold tiltDerivative
  linarith

private noncomputable def witnessLeft : WitnessInterval := ⟨11 / 4, by constructor <;> norm_num⟩

private noncomputable def witnessRight : WitnessInterval := ⟨14 / 5, by constructor <;> norm_num⟩

private theorem tiltMass_left_bound : tiltMass witnessLeft < 3 / 1000 := by
  have hder := derivative_upper (r := 11 / 4) (p := 3 / 1000)
    (cosineCeiling := 998499 / 1000000) (normFloor := 1009795 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hneg : tiltDerivative witnessLeft (3 / 1000) < 0 := by
    change tiltDerivative (11 / 4) (3 / 1000) < 0
    linarith
  by_contra! hle
  have hr : (1 : ℝ) < witnessLeft := by norm_num [witnessLeft]
  have hm : tiltMass witnessLeft ∈ Ico 0 1 :=
    ⟨(tiltMass_spec _).1.1.le, by linarith [(tiltMass_spec witnessLeft).1.2]⟩
  have hanti := (tiltDerivative_strictAntiOn witnessLeft hr).antitoneOn
    (show (3 / 1000 : ℝ) ∈ Ico 0 1 by constructor <;> norm_num) hm hle
  rw [(tiltMass_spec witnessLeft).2] at hanti
  linarith

private theorem tiltMass_right_bounds :
    9 / 1000 < tiltMass witnessRight ∧ tiltMass witnessRight < 1 / 100 := by
  have hlow := derivative_lower (r := 14 / 5) (p := 9 / 1000)
    (cosineFloor := 995489 / 1000000) (normCeiling := 1030321 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hupp := derivative_upper (r := 14 / 5) (p := 1 / 100)
    (cosineCeiling := 994988 / 1000000) (normFloor := 1033634 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 < tiltDerivative witnessRight (9 / 1000) := by
    change 0 < tiltDerivative (14 / 5) (9 / 1000)
    linarith
  have hneg : tiltDerivative witnessRight (1 / 100) < 0 := by
    change tiltDerivative (14 / 5) (1 / 100) < 0
    linarith
  have hr : (1 : ℝ) < witnessRight := by norm_num [witnessRight]
  have hm : tiltMass witnessRight ∈ Ico 0 1 :=
    ⟨(tiltMass_spec _).1.1.le, by linarith [(tiltMass_spec witnessRight).1.2]⟩
  constructor
  · by_contra! hle
    have hanti := (tiltDerivative_strictAntiOn witnessRight hr).antitoneOn hm
      (show (9 / 1000 : ℝ) ∈ Ico 0 1 by constructor <;> norm_num) hle
    rw [(tiltMass_spec witnessRight).2] at hanti
    linarith
  · by_contra! hle
    have hanti := (tiltDerivative_strictAntiOn witnessRight hr).antitoneOn
      (show (1 / 100 : ℝ) ∈ Ico 0 1 by constructor <;> norm_num) hm hle
    rw [(tiltMass_spec witnessRight).2] at hanti
    linarith

noncomputable def tiltNormalizer (r p : ℝ) : ℝ := Real.sqrt (1 + (r ^ 2 - 1) * p)

noncomputable def tiltedActive (r p : ℝ) : ℝ := (1 - p) / tiltNormalizer r p

noncomputable def tiltedSpectator (r p : ℝ) : ℝ := r * p / tiltNormalizer r p

noncomputable def sectorDifference (r p : ℝ) : ℝ :=
  (1 - tiltedActive r p) * (3 + tiltedActive r p) / 4

noncomputable def spectatorDifference (r p : ℝ) : ℝ :=
  (p - (tiltedSpectator r p) ^ 2) / 2

noncomputable def coherenceDifference (r p : ℝ) : ℝ :=
  1 - Real.sqrt 2 * (Real.sqrt (1 - p) / 2 +
    (1 + tiltedActive r p) * tiltedSpectator r p / 4)

noncomputable def matchingResidual (r p : ℝ) : ℝ :=
  (2 - r / Real.sqrt 2) * coherenceDifference r p +
    Real.sqrt 2 * r * spectatorDifference r p - sectorDifference r p

private theorem tiltedComponent_bounds {r p : ℝ} (hr : 1 < r) (hp : p ∈ Icc 0 1) :
    1 ≤ tiltNormalizer r p ∧
    tiltedActive r p ∈ Icc 0 1 ∧
    tiltedSpectator r p ∈ Icc 0 (r * p) ∧
    spectatorDifference r p ∈ Icc 0 (p / 2) := by
  have hr0 : 0 ≤ r := by linarith
  have hweight : 0 ≤ r ^ 2 - 1 := by nlinarith
  have hnonneg : 0 ≤ (r ^ 2 - 1) * p := mul_nonneg hweight hp.1
  have hn : 1 ≤ tiltNormalizer r p := by
    unfold tiltNormalizer
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hn0 : 0 < tiltNormalizer r p := lt_of_lt_of_le zero_lt_one hn
  have hnsq : (tiltNormalizer r p) ^ 2 = 1 + (r ^ 2 - 1) * p :=
    Real.sq_sqrt (by linarith)
  have hc : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hs : (tiltedSpectator r p) ^ 2 ≤ p := by
    unfold tiltedSpectator
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hn0), hnsq]
    nlinarith only [mul_nonneg hp.1 hc]
  refine ⟨hn, ⟨div_nonneg hc hn0.le, ?_⟩,
    ⟨div_nonneg (mul_nonneg hr0 hp.1) hn0.le, ?_⟩, ⟨?_, ?_⟩⟩
  · unfold tiltedActive
    exact (div_le_one hn0).2 (by linarith [hp.1, hn])
  · unfold tiltedSpectator
    exact div_le_self (mul_nonneg hr0 hp.1) hn
  · unfold spectatorDifference
    linarith
  · unfold spectatorDifference
    linarith [sq_nonneg (tiltedSpectator r p)]

private theorem standardSqrtTwo_bounds :
    1414 / 1000 < Real.sqrt 2 ∧ Real.sqrt 2 < 1415 / 1000 := by
  exact ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num),
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)⟩

private theorem matchingResidual_left_pos (p : ℝ) (hp : p ∈ Icc 0 (3 / 1000)) :
    0 < matchingResidual (11 / 4) p := by
  have hpUnit : p ∈ Icc 0 1 := ⟨hp.1, by linarith [hp.2]⟩
  obtain ⟨hn, ha, hh, hv⟩ := tiltedComponent_bounds (r := 11 / 4) (by norm_num) hpUnit
  have hnUpper : tiltNormalizer (11 / 4) p ≤ 101 / 100 := by
    unfold tiltNormalizer
    exact (Real.sqrt_le_left (by norm_num)).2 (by linarith [hp.2])
  have hf : (987 / 1000 : ℝ) ≤ tiltedActive (11 / 4) p := by
    unfold tiltedActive
    apply (le_div_iff₀ (show 0 < tiltNormalizer (11 / 4) p by linarith)).2
    linarith [hp.2, hnUpper]
  have hU : sectorDifference (11 / 4) p ≤ 13 / 1000 := by
    unfold sectorDifference
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr ha.2)]
  have hc : Real.sqrt (1 - p) ≤ 1 :=
    (Real.sqrt_le_left zero_le_one).2 (by linarith [hp.1])
  have hm : (1 + tiltedActive (11 / 4) p) * tiltedSpectator (11 / 4) p ≤ 18 / 1000 := by
    have h₁ : 1 + tiltedActive (11 / 4) p ≤ 2 := by linarith [ha.2]
    have h₂ : tiltedSpectator (11 / 4) p ≤ 9 / 1000 := by linarith [hh.2, hp.2]
    nlinarith only [mul_le_mul h₁ h₂ hh.1 (by norm_num : (0 : ℝ) ≤ 2)]
  have hM : Real.sqrt (1 - p) / 2 +
      (1 + tiltedActive (11 / 4) p) * tiltedSpectator (11 / 4) p / 4 ≤ 1009 / 2000 := by
    linarith
  have hC : (286 / 1000 : ℝ) ≤ coherenceDifference (11 / 4) p := by
    unfold coherenceDifference
    have h0 : 0 ≤ Real.sqrt (1 - p) / 2 +
        (1 + tiltedActive (11 / 4) p) * tiltedSpectator (11 / 4) p / 4 := by
      exact add_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
        (div_nonneg (mul_nonneg (by linarith [ha.1]) hh.1) (by norm_num))
    nlinarith only [mul_le_mul standardSqrtTwo_bounds.2.le hM h0 (by norm_num :
      (0 : ℝ) ≤ 1415 / 1000)]
  have hs0 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hcoef : (55 / 1000 : ℝ) ≤ 2 - (11 / 4) / Real.sqrt 2 := by
    have hdiv : (11 / 4 : ℝ) / Real.sqrt 2 ≤ 1945 / 1000 := by
      apply (div_le_iff₀ hs0).2
      linarith [standardSqrtTwo_bounds.1]
    linarith
  have hmain := mul_le_mul hcoef hC (by norm_num : (0 : ℝ) ≤ 286 / 1000)
    (by linarith : 0 ≤ 2 - (11 / 4 : ℝ) / Real.sqrt 2)
  have hrest := mul_nonneg (show 0 ≤ Real.sqrt 2 * (11 / 4 : ℝ) by positivity) hv.1
  unfold matchingResidual
  linarith

private theorem matchingResidual_right_neg (p : ℝ) (hp : p ∈ Icc (9 / 1000) (1 / 100)) :
    matchingResidual (14 / 5) p < 0 := by
  have hpUnit : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  obtain ⟨hn, ha, hh, hv⟩ := tiltedComponent_bounds (r := 14 / 5) (by norm_num) hpUnit
  have hnLower : (103 / 100 : ℝ) ≤ tiltNormalizer (14 / 5) p := by
    unfold tiltNormalizer
    exact (Real.le_sqrt (by norm_num) (by linarith [hp.1])).2 (by linarith [hp.1])
  have hf : tiltedActive (14 / 5) p ≤ 963 / 1000 := by
    unfold tiltedActive
    apply (div_le_iff₀ (show 0 < tiltNormalizer (14 / 5) p by linarith)).2
    linarith [hp.1, hnLower]
  have hU : (111 / 4000 : ℝ) ≤ sectorDifference (14 / 5) p := by
    unfold sectorDifference
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) ha.1, hf]
  have hc : (994 / 1000 : ℝ) ≤ Real.sqrt (1 - p) :=
    (Real.le_sqrt (by norm_num) (by linarith [hp.2])).2 (by linarith [hp.2])
  have hM : (497 / 1000 : ℝ) ≤ Real.sqrt (1 - p) / 2 +
      (1 + tiltedActive (14 / 5) p) * tiltedSpectator (14 / 5) p / 4 := by
    have h₀ : 0 ≤ (1 + tiltedActive (14 / 5) p) * tiltedSpectator (14 / 5) p :=
      mul_nonneg (by linarith [ha.1]) hh.1
    linarith
  have hC : coherenceDifference (14 / 5) p ≤ 3 / 10 := by
    unfold coherenceDifference
    nlinarith only [mul_le_mul standardSqrtTwo_bounds.1.le hM (by norm_num :
      (0 : ℝ) ≤ 497 / 1000) (Real.sqrt_nonneg 2)]
  have hs0 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hcoef0 : 0 ≤ 2 - (14 / 5 : ℝ) / Real.sqrt 2 := by
    have ht := (div_le_iff₀ hs0).2 (by linarith [standardSqrtTwo_bounds.1] :
      (14 / 5 : ℝ) ≤ 2 * Real.sqrt 2)
    linarith
  have hcoef : 2 - (14 / 5 : ℝ) / Real.sqrt 2 ≤ 22 / 1000 := by
    have ht := (le_div_iff₀ hs0).2 (by linarith [standardSqrtTwo_bounds.2] :
      (1978 / 1000 : ℝ) * Real.sqrt 2 ≤ 14 / 5)
    linarith
  have hmain := mul_le_mul hC hcoef hcoef0 (by norm_num : (0 : ℝ) ≤ 3 / 10)
  have hvUpper : spectatorDifference (14 / 5) p ≤ 1 / 200 := by linarith [hp.2, hv.2]
  have hrest := mul_le_mul
    (show Real.sqrt 2 * (14 / 5 : ℝ) ≤ (1415 / 1000) * (14 / 5) by
      linarith [standardSqrtTwo_bounds.2])
    hvUpper hv.1 (by norm_num : (0 : ℝ) ≤ (1415 / 1000) * (14 / 5))
  unfold matchingResidual
  linarith

theorem sectorDifference_le_twice_coherence (r : WitnessInterval) :
    sectorDifference r (tiltMass r) ≤ 2 * coherenceDifference r (tiltMass r) := by
  let p := tiltMass r
  have hp := (tiltMass_spec r).1
  have hr1 : (1 : ℝ) < r := by linarith [r.property.1]
  have hrU : (r : ℝ) ≤ 14 / 5 := r.property.2
  have hweight : (r : ℝ) ^ 2 - 1 ≤ 171 / 25 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrU) (show 0 ≤ (14 / 5 : ℝ) + r by
      linarith)]
  have hpUnit : p ∈ Icc 0 1 := ⟨hp.1.le, by linarith [hp.2]⟩
  obtain ⟨hn, ha, hh, _⟩ := tiltedComponent_bounds hr1 hpUnit
  have hnUpper : tiltNormalizer r p ≤ 11 / 10 := by
    unfold tiltNormalizer
    apply (Real.sqrt_le_left (by norm_num)).2
    have hpCeiling : (r ^ 2 - 1 : ℝ) * p ≤ (171 / 25) * (1 / 50) :=
      mul_le_mul hweight hp.2.le hp.1.le (by norm_num)
    linarith
  have haLower : (49 / 55 : ℝ) ≤ tiltedActive r p := by
    unfold tiltedActive
    apply (le_div_iff₀ (show 0 < tiltNormalizer r p by linarith)).2
    linarith [hp.2, hnUpper]
  have hU : sectorDifference r p ≤ 6 / 55 := by
    unfold sectorDifference
    nlinarith [sq_nonneg (1 - tiltedActive r p)]
  have hhUpper : tiltedSpectator r p ≤ 3 / 50 := by
    have hprod : (r : ℝ) * p ≤ (14 / 5 : ℝ) * (1 / 50) :=
      mul_le_mul hrU hp.2.le hp.1.le (by norm_num)
    linarith [hh.2]
  have hproduct : (1 + tiltedActive r p) * tiltedSpectator r p ≤ 3 / 25 := by
    nlinarith only [mul_le_mul (show 1 + tiltedActive r p ≤ 2 by linarith [ha.2])
      hhUpper hh.1 (by norm_num : (0 : ℝ) ≤ 2)]
  have hc : Real.sqrt (1 - p) ≤ 1 :=
    (Real.sqrt_le_left zero_le_one).2 (by linarith [hp.1])
  have hM : Real.sqrt (1 - p) / 2 +
      (1 + tiltedActive r p) * tiltedSpectator r p / 4 ≤ 53 / 100 := by linarith
  have hM0 : 0 ≤ Real.sqrt (1 - p) / 2 +
      (1 + tiltedActive r p) * tiltedSpectator r p / 4 :=
    add_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
      (div_nonneg (mul_nonneg (by linarith [ha.1]) hh.1) (by norm_num))
  have hC : (1 / 5 : ℝ) ≤ coherenceDifference r p := by
    unfold coherenceDifference
    have hs : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by linarith [standardSqrtTwo_bounds.2]
    nlinarith only [mul_le_mul hs hM hM0 (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  change sectorDifference r p ≤ 2 * coherenceDifference r p
  linarith

private theorem matchingResidual_continuous :
    Continuous (fun r : WitnessInterval => matchingResidual r (tiltMass r)) := by
  have hr : Continuous (fun r : WitnessInterval => (r : ℝ)) := continuous_subtype_val
  have hp := tiltMass_continuous
  have hn : Continuous (fun r : WitnessInterval => tiltNormalizer r (tiltMass r)) := by
    unfold tiltNormalizer
    fun_prop
  have hn0 (r : WitnessInterval) : tiltNormalizer r (tiltMass r) ≠ 0 := by
    have hr1 : (1 : ℝ) < r := by linarith [r.property.1]
    have hp := (tiltMass_spec r).1
    exact (lt_of_lt_of_le zero_lt_one
      (tiltedComponent_bounds hr1 ⟨hp.1.le, by linarith [hp.2]⟩).1).ne'
  have ha : Continuous (fun r : WitnessInterval => tiltedActive r (tiltMass r)) :=
    (continuous_const.sub hp).div hn hn0
  have hh : Continuous (fun r : WitnessInterval => tiltedSpectator r (tiltMass r)) :=
    (hr.mul hp).div hn hn0
  unfold matchingResidual sectorDifference spectatorDifference coherenceDifference
  fun_prop

/-- An equality witness exists in the interval where the first-projection
score is attained by the tilted rank-three and rank-two PVM. -/
theorem exists_matchingResidual_zero : ∃ r : WitnessInterval,
    matchingResidual r (tiltMass r) = 0 := by
  have hab : (11 / 4 : ℝ) ≤ 14 / 5 := by norm_num
  let f := fun r : WitnessInterval => matchingResidual r (tiltMass r)
  let g := f ∘ projIcc (11 / 4 : ℝ) (14 / 5) hab
  have hg : Continuous g := matchingResidual_continuous.comp continuous_projIcc
  have hleft : 0 < g (11 / 4) := by
    have heq : projIcc (11 / 4 : ℝ) (14 / 5) hab (11 / 4) = witnessLeft :=
      Subtype.ext (by simp [witnessLeft, projIcc_of_mem, hab])
    change 0 < f (projIcc (11 / 4 : ℝ) (14 / 5) hab (11 / 4))
    rw [heq]
    exact matchingResidual_left_pos _ ⟨(tiltMass_spec _).1.1.le, tiltMass_left_bound.le⟩
  have hright : g (14 / 5) < 0 := by
    have heq : projIcc (11 / 4 : ℝ) (14 / 5) hab (14 / 5) = witnessRight :=
      Subtype.ext (by simp [witnessRight, projIcc_of_mem, hab])
    change f (projIcc (11 / 4 : ℝ) (14 / 5) hab (14 / 5)) < 0
    rw [heq]
    exact matchingResidual_right_neg _
      ⟨tiltMass_right_bounds.1.le, tiltMass_right_bounds.2.le⟩
  obtain ⟨r, _, hr⟩ := intermediate_value_Icc' hab hg.continuousOn ⟨hright.le, hleft.le⟩
  exact ⟨projIcc _ _ hab r, hr⟩

/-- The two tilted projective branches' score, in expanded form. -/
noncomputable def tiltScore (r p : ℝ) : ℝ :=
  6 + r ^ 2 - p + 4 * r * Real.sqrt (1 - p) +
    2 * Real.sqrt (1 + (r ^ 2 - 1) * p)

theorem tiltScore_eq_branch_sum (r p : ℝ) (hr : 1 < r) (hp : p ∈ Icc 0 1) :
    tiltScore r p = (2 + r * Real.sqrt (1 - p)) ^ 2 +
      (1 + Real.sqrt (1 + (r ^ 2 - 1) * p)) ^ 2 := by
  have hweight : 0 ≤ r ^ 2 - 1 := by nlinarith
  have hleft := Real.sq_sqrt (sub_nonneg.mpr hp.2)
  have hright := Real.sq_sqrt (by
    linarith [mul_nonneg hweight hp.1] : 0 ≤ 1 + (r ^ 2 - 1) * p)
  unfold tiltScore
  linear_combination -r ^ 2 * hleft - hright

private theorem tiltScore_hasDerivAt (r p : ℝ) (hr : 1 < r) (hp : p ∈ Ico 0 1) :
    HasDerivAt (tiltScore r) (tiltDerivative r p) p := by
  have hweight : 0 ≤ r ^ 2 - 1 := by nlinarith
  have hleft : 0 < 1 - p := sub_pos.mpr hp.2
  have hright : 0 < 1 + (r ^ 2 - 1) * p := by
    linarith [mul_nonneg hweight hp.1]
  have hid := hasDerivAt_id p
  have hbase := (hasDerivAt_const p (6 + r ^ 2)).sub hid
  have hfirst := ((hasDerivAt_const p (1 : ℝ)).sub hid).sqrt hleft.ne'
  have hsecond := ((hasDerivAt_const p (1 : ℝ)).add
    (hid.const_mul (r ^ 2 - 1))).sqrt hright.ne'
  convert (hbase.add (hfirst.const_mul (4 * r))).add (hsecond.const_mul 2) using 1
  · rfl
  · change tiltDerivative r p = 0 - 1 +
        4 * r * ((0 - 1) / (2 * Real.sqrt (1 - p))) +
        2 * ((0 + (r ^ 2 - 1) * 1) / (2 * Real.sqrt (1 + (r ^ 2 - 1) * p)))
    unfold tiltDerivative
    field_simp [(Real.sqrt_pos.2 hleft).ne', (Real.sqrt_pos.2 hright).ne']
    <;> ring

/-- The interior zero of the derivative is the strict global maximizer over
all leakage masses, including the two degenerate projective splits. -/
theorem tiltScore_lt_of_ne_maximizer (r p q : ℝ) (hr : 1 < r) (hp : p ∈ Ioo 0 1)
    (hzero : tiltDerivative r p = 0) (hq : q ∈ Icc 0 1) (hne : q ≠ p) :
    tiltScore r q < tiltScore r p := by
  have hcont : Continuous (tiltScore r) := by
    unfold tiltScore
    fun_prop
  have hpUnit : p ∈ Ico 0 1 := ⟨hp.1.le, hp.2⟩
  have hanti := tiltDerivative_strictAntiOn r hr
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmono : StrictMonoOn (tiltScore r) (Icc 0 p) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 p) hcont.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      have hxUnit : x ∈ Ico 0 1 := ⟨hx.1.le, hx.2.trans hp.2⟩
      rw [(tiltScore_hasDerivAt r x hr hxUnit).deriv, ← hzero]
      exact hanti hxUnit hpUnit hx.2
    exact hmono ⟨hq.1, hlt.le⟩ ⟨hp.1.le, le_rfl⟩ hlt
  · have hdown : StrictAntiOn (tiltScore r) (Icc p 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc p 1) hcont.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      have hxUnit : x ∈ Ico 0 1 := ⟨(hp.1.trans hx.1).le, hx.2⟩
      rw [(tiltScore_hasDerivAt r x hr hxUnit).deriv, ← hzero]
      exact hanti hpUnit hxUnit hx.1
    exact hdown ⟨le_rfl, hp.2.le⟩ ⟨hgt.le, hq.2⟩ hgt

private theorem sqrt_transfer_le {A B d t : ℝ}
    (hd : 0 ≤ d) (hdA : d ≤ A) (hB : 0 < B) (ht : 0 ≤ t)
    (hdominates : t * Real.sqrt A ≤ Real.sqrt B) :
    Real.sqrt (A - d) + Real.sqrt (B + t * d) ≤ Real.sqrt A + Real.sqrt B := by
  by_cases hdz : d = 0
  · simp [hdz]
  have hA : 0 < A := lt_of_lt_of_le (lt_of_le_of_ne hd (Ne.symm hdz)) hdA
  have hAA : 0 ≤ A - d := sub_nonneg.mpr hdA
  have hBB : 0 ≤ B + t * d := add_nonneg hB.le (mul_nonneg ht hd)
  let SA := Real.sqrt A + Real.sqrt (A - d)
  let SB := Real.sqrt (B + t * d) + Real.sqrt B
  have hSA : 0 < SA := add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hA) (Real.sqrt_nonneg _)
  have hSB : 0 < SB := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.2 hB)
  have hx : Real.sqrt A - Real.sqrt (A - d) = d / SA := by
    apply (eq_div_iff hSA.ne').2
    dsimp [SA]
    nlinarith only [Real.sq_sqrt hA.le, Real.sq_sqrt hAA]
  have hy : Real.sqrt (B + t * d) - Real.sqrt B = t * d / SB := by
    apply (eq_div_iff hSB.ne').2
    dsimp [SB]
    nlinarith only [Real.sq_sqrt hBB, Real.sq_sqrt hB.le]
  have hb : t * SA ≤ SB := by
    have h₁ := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith : A - d ≤ A)) ht
    have h₂ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (mul_nonneg ht hd) :
      B ≤ B + t * d)
    dsimp [SA, SB]
    nlinarith only [hdominates, h₁, h₂]
  have htrans : t * d / SB ≤ d / SA := by
    apply (div_le_div_iff₀ hSB hSA).2
    have hm := mul_le_mul_of_nonneg_right hb hd
    nlinarith only [hm]
  linarith

/-- In the opposite-preference split, moving the distinguished spectator
component outside the preferred rank-two sector increases the score bound. -/
theorem opposed_rank_three_bound (r eta z tau : ℝ)
    (hr : r ∈ Icc (11 / 4) (14 / 5)) (heta : eta ∈ Icc (1 / 8) 1)
    (hz : z ∈ Icc 0 1) (htau : tau ∈ Icc (1 / 2) 1) :
    Real.sqrt tau + Real.sqrt (tau - (2 * tau - 1) * z) +
        Real.sqrt (r ^ 2 * eta + (1 - eta) * ((1 - tau) + (2 * tau - 1) * z)) ≤
      2 + r * Real.sqrt eta := by
  have hη0 : 0 ≤ 1 - eta := sub_nonneg.mpr heta.2
  have hη : 0 < eta := by linarith [heta.1]
  have hr0 : 0 < r := by linarith [hr.1]
  have hτ0 : 0 ≤ 2 * tau - 1 := by linarith [htau.1]
  have hdz : 0 ≤ (2 * tau - 1) * z := mul_nonneg hτ0 hz.1
  have hdzA : (2 * tau - 1) * z ≤ tau := by
    have hh := mul_le_mul_of_nonneg_left hz.2 hτ0
    nlinarith only [hh, htau.2]
  have hB0 : 0 < r ^ 2 * eta := mul_pos (sq_pos_of_pos hr0) hη
  have hB : 0 < r ^ 2 * eta + (1 - eta) * (1 - tau) :=
    add_pos_of_pos_of_nonneg hB0 (mul_nonneg hη0 (sub_nonneg.mpr htau.2))
  have hspread : 1 - eta ≤ Real.sqrt (r ^ 2 * eta) := by
    apply (Real.le_sqrt hη0 hB0.le).2
    have hsmall : 1 - eta ≤ 7 / 8 := by linarith [heta.1]
    have hRsq : (11 / 4 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num) hr.1 2
    have hlarge := mul_le_mul hRsq heta.1 (by norm_num : (0 : ℝ) ≤ 1 / 8) (by positivity :
      0 ≤ r ^ 2)
    nlinarith only [pow_le_pow_left₀ hη0 hsmall 2, hlarge]
  have hτroot : Real.sqrt tau ≤ 1 :=
    (Real.sqrt_le_left zero_le_one).2 (by linarith [htau.2])
  have hstep := sqrt_transfer_le hdz hdzA hB hη0 (show
      (1 - eta) * Real.sqrt tau ≤ Real.sqrt (r ^ 2 * eta + (1 - eta) * (1 - tau)) by
    calc
      (1 - eta) * Real.sqrt tau ≤ 1 - eta := by nlinarith [mul_le_mul_of_nonneg_left hτroot hη0]
      _ ≤ Real.sqrt (r ^ 2 * eta) := hspread
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (mul_nonneg hη0
        (sub_nonneg.mpr htau.2))))
  have hstep' : Real.sqrt (tau - (2 * tau - 1) * z) +
      Real.sqrt (r ^ 2 * eta + (1 - eta) * ((1 - tau) + (2 * tau - 1) * z)) ≤
      Real.sqrt tau + Real.sqrt (r ^ 2 * eta + (1 - eta) * (1 - tau)) := by
    rw [show r ^ 2 * eta + (1 - eta) * ((1 - tau) + (2 * tau - 1) * z) =
        r ^ 2 * eta + (1 - eta) * (1 - tau) + (1 - eta) * ((2 * tau - 1) * z) by ring]
    exact hstep
  have hmove := sqrt_transfer_le (sub_nonneg.mpr htau.2)
    (by linarith [htau.1] : 1 - tau ≤ 1) hB0 hη0
    (by rwa [Real.sqrt_one, mul_one])
  have hmove' : Real.sqrt tau + Real.sqrt (r ^ 2 * eta + (1 - eta) * (1 - tau)) ≤
      1 + Real.sqrt (r ^ 2 * eta) := by
    simpa only [sub_sub_cancel, Real.sqrt_one] using hmove
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0.le] at hmove'
  linarith

/-- The opposite-preference rank-two contribution is bounded by its value
when both preferred weights are one and the mixed unit vector is in Q. -/
theorem opposed_rank_two_bound (r eta z sigma : ℝ) (heta : 0 ≤ eta)
    (hz : 0 ≤ z) (hsigma : sigma ∈ Icc (1 / 2) 1) :
    Real.sqrt sigma + Real.sqrt (r ^ 2 * (1 - eta) + eta * (sigma - (2 * sigma - 1) * z)) ≤
      1 + Real.sqrt (r ^ 2 * (1 - eta) + eta) := by
  have hσ : Real.sqrt sigma ≤ 1 :=
    (Real.sqrt_le_left zero_le_one).2 (by linarith [hsigma.2])
  have hcoef : sigma - (2 * sigma - 1) * z ≤ 1 := by
    linarith [mul_nonneg (show 0 ≤ 2 * sigma - 1 by linarith [hsigma.1]) hz, hsigma.2]
  have hr := Real.sqrt_le_sqrt (add_le_add_left
    (by simpa using mul_le_mul_of_nonneg_left hcoef heta) (r ^ 2 * (1 - eta)))
  exact add_le_add hσ (by simpa only [add_comm] using hr)

/-- The discarded first-projection cases are below the untilted rank-three
and rank-two score throughout the witness interval. -/
theorem other_rank_bounds_lt (r : WitnessInterval) :
    (Real.sqrt 5 + (r : ℝ)) ^ 2 + 1 < tiltScore r 0 ∧
    (Real.sqrt (9 / 2) + Real.sqrt ((r : ℝ) ^ 2 + 1)) ^ 2 < tiltScore r 0 ∧
    (2 + Real.sqrt (1 + ((r : ℝ) ^ 2 - 1) / 8)) ^ 2 + (1 + r) ^ 2 < tiltScore r 0 := by
  let x : ℝ := r
  have hxLo : (11 / 4 : ℝ) ≤ x := r.property.1
  have hxHi : x ≤ 14 / 5 := r.property.2
  have hx0 : 0 ≤ x := by linarith
  have hbase : (10625 / 400 : ℝ) ≤ tiltScore r 0 := by
    change 10625 / 400 ≤ tiltScore x 0
    simp [tiltScore]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11 / 4) hxLo 2]
  have hxSq : x ^ 2 ≤ (14 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hxHi 2
  have h5 : Real.sqrt (5 : ℝ) ≤ 2237 / 1000 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have h45 : Real.sqrt (9 / 2 : ℝ) ≤ 2122 / 1000 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hxRoot : Real.sqrt (x ^ 2 + 1) ≤ 2974 / 1000 :=
    (Real.sqrt_le_left (by norm_num)).2 (by linarith)
  have hfRoot : Real.sqrt (1 + (x ^ 2 - 1) / 8) ≤ 1363 / 1000 :=
    (Real.sqrt_le_left (by norm_num)).2 (by linarith)
  change (Real.sqrt 5 + x) ^ 2 + 1 < tiltScore r 0 ∧
    (Real.sqrt (9 / 2) + Real.sqrt (x ^ 2 + 1)) ^ 2 < tiltScore r 0 ∧
    (2 + Real.sqrt (1 + (x ^ 2 - 1) / 8)) ^ 2 + (1 + x) ^ 2 < tiltScore r 0
  refine ⟨?_, ?_, ?_⟩
  · have hsum : Real.sqrt 5 + x ≤ 5037 / 1000 := by linarith
    have hs := pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) hx0) hsum 2
    linarith
  · have hsum : Real.sqrt (9 / 2) + Real.sqrt (x ^ 2 + 1) ≤ 5096 / 1000 := by linarith
    have hs := pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hsum 2
    linarith
  · have hsum : 2 + Real.sqrt (1 + (x ^ 2 - 1) / 8) ≤ 3363 / 1000 := by linarith
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2 + Real.sqrt (1 + (x ^ 2 - 1) / 8)) hsum 2
    have hr := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + x)
      (by linarith : 1 + x ≤ 19 / 5) 2
    linarith

/-- The scalar matching relation provides a positive Choi slack with the
same kernel direction as the two-flag witness. -/
theorem matching_certificate (r sector spectator coherence : ℝ) (hr : 0 < r)
    (hmatch : (2 - r / Real.sqrt 2) * coherence + Real.sqrt 2 * r * spectator - sector = 0)
    (hpositive : sector ≤ 2 * coherence) :
    let w := (Real.sqrt 2 * sector + r * coherence) / (2 * Real.sqrt 2 + r)
    let slack : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(2 * w - sector : ℝ), (w - coherence : ℝ);
        (w - coherence : ℝ), (w / 2 - spectator : ℝ)]
    slack.PosSemidef ∧
      2 * sector + 2 * Real.sqrt 2 * r * coherence + r ^ 2 * spectator =
        w * (r + 2 * Real.sqrt 2) ^ 2 / 2 := by
  dsimp only
  set s := Real.sqrt 2 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hss : s ^ 2 = 2 := by rw [hs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  let w := (s * sector + r * coherence) / (2 * s + r)
  have hw : w * (2 * s + r) = s * sector + r * coherence :=
    div_mul_cancel₀ _ (by positivity)
  have hfirst : s * (2 * w - sector) + r * (w - coherence) = 0 := by
    nlinarith only [hw]
  have hmatch' : 2 * s * coherence - r * coherence + 2 * r * spectator - s * sector = 0 := by
    change (2 - r / s) * coherence + s * r * spectator - sector = 0 at hmatch
    have hmul := congrArg (fun x : ℝ => s * x) hmatch
    have hdiv : s * (r / s) = r := by field_simp
    calc
      2 * s * coherence - r * coherence + 2 * r * spectator - s * sector =
          s * ((2 - r / s) * coherence + s * r * spectator - sector) := by
            nlinarith only [hss, congrArg (fun x : ℝ => x * coherence) hdiv,
              congrArg (fun x : ℝ => x * r * spectator) hss]
      _ = 0 := by simpa using hmul
  have hsecond : s * (w - coherence) + r * (w / 2 - spectator) = 0 := by
    nlinarith only [hw, hmatch']
  have hA : 0 ≤ 2 * w - sector := by
    have hid : (2 * w - sector) * (2 * s + r) = r * (2 * coherence - sector) := by
      nlinarith only [hw]
    exact nonneg_of_mul_nonneg_left (hid.symm ▸ mul_nonneg hr.le (sub_nonneg.mpr hpositive))
      (by positivity)
  let v : Fin 2 → ℂ := ![1, (-(s / r) : ℝ)]
  have hB : w - coherence = -(s / r) * (2 * w - sector) := by
    field_simp [hr.ne']
    nlinarith only [hfirst]
  have hD : w / 2 - spectator = (s / r)^2 * (2 * w - sector) := by
    have haux : r * (w / 2 - spectator) = -s * (w - coherence) := by linarith
    calc
      w / 2 - spectator = -s * (w - coherence) / r := by
        exact (eq_div_iff hr.ne').2 (by simpa [mul_comm] using haux)
      _ = (s / r)^2 * (2 * w - sector) := by rw [hB]; ring
  refine ⟨?_, ?_⟩
  · let slack : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(2 * w - sector : ℝ), (w - coherence : ℝ);
        (w - coherence : ℝ), (w / 2 - spectator : ℝ)]
    change slack.PosSemidef
    have hslack : slack = (2 * w - sector) • Matrix.vecMulVec v (star v) := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [slack, v, Matrix.vecMulVec]
      · simpa [slack, v, Matrix.vecMulVec, mul_comm] using congrArg Complex.ofReal hB
      · simpa [slack, v, Matrix.vecMulVec, mul_comm] using congrArg Complex.ofReal hB
      · simpa [slack, v, Matrix.vecMulVec, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using congrArg Complex.ofReal hD
    rw [hslack]
    exact (Matrix.posSemidef_vecMulVec_self_star v).smul hA
  · change 2 * sector + 2 * s * r * coherence + r ^ 2 * spectator =
        w * (r + 2 * s) ^ 2 / 2
    linear_combination -s * hfirst - r * hsecond - sector * hss

end D5.S3.Quantum.Measurement.AuricFiveLevelTilt
