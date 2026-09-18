/- GID: D5/S3/Geometry/Hyperideal/CriticalTransitionStar
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CriticalTransitionStar
   mirror-E: none(waiver:universal-continuous-star-inequality)
   anchors: []
   utility: none
   digest: Two-sided angle-sum margins for a six-occurrence critical transition star. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
The target coordinate is shared across all occurrences. The other coordinates
range independently over continuous faces, so actual shared-global-label
vectors are included. All counts are counts of occurrences, not distinct
neighbour labels. Four favourable occurrences have four short neighbours
and an opposite coordinate at least 4/3. The other occurrences have at least
three short neighbours. No cosine/angle bound or desired sum is a premise.

The derivative comparison is consumed from its existing single owner. This
module proves the new endpoints, exact double-angle gap, and finite-star
aggregation. Topological face gluing and the geometric co-volume existence
argument are not encoded here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Geometry.Hyperideal.CriticalTransitionStar
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open scoped BigOperators

def ThreeSmall (y z v w : ℝ) : Prop :=
  (y ≤ 5/4 ∧ z ≤ 5/4 ∧ v ≤ 5/4) ∨
  (y ≤ 5/4 ∧ z ≤ 5/4 ∧ w ≤ 5/4) ∨
  (y ≤ 5/4 ∧ v ≤ 5/4 ∧ w ≤ 5/4) ∨
  (z ≤ 5/4 ∧ v ≤ 5/4 ∧ w ≤ 5/4)

def beta : ℝ := Real.arccos (49 / Real.sqrt 6534)
def gamma : ℝ := Real.arccos (43/99)
def margin : ℝ := min (2*Real.pi - 6*Real.arccos (4/7))
  (4*gamma + 2*beta - 2*Real.pi)

private theorem quotient_le (A B P q : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hq : 0 ≤ q) (hs : P ^ 2 ≤ q ^ 2 * (A * B)) :
    P / Real.sqrt A / Real.sqrt B ≤ q := by
  let r := Real.sqrt A * Real.sqrt B
  have hr : 0 < r := mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hrsq : r^2 = A*B := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
  rw [div_div]
  change P/r ≤ q
  apply (div_le_iff₀ hr).2
  by_cases hP : P ≤ 0
  · exact hP.trans (mul_nonneg hq hr.le)
  · by_contra h
    have hlt : q*r < P := lt_of_not_ge h
    have hsum : 0 < P+q*r := by nlinarith [mul_nonneg hq hr.le]
    have hprod := mul_pos (sub_pos.mpr hlt) hsum
    have heq : (q*r)^2 = q^2*(A*B) := by rw [mul_pow, hrsq]
    nlinarith

/-- Uniform signed angle-sum margins on both faces of the shared critical
coordinate. The same real neighbour vector is used on each face. -/
theorem critical_transition_star
    {I : Type*} [Fintype I]
    (y z o v w : I → ℝ) (good : Finset I)
    (hcard : Fintype.card I = 6) (hgood : 4 ≤ good.card)
    (hbox : ∀ i, y i ∈ Set.Icc 1 2 ∧ z i ∈ Set.Icc 1 2 ∧
      o i ∈ Set.Icc 1 2 ∧ v i ∈ Set.Icc 1 2 ∧ w i ∈ Set.Icc 1 2)
    (hsmall : ∀ i, ThreeSmall (y i) (z i) (v i) (w i))
    (hpaired : ∀ i ∈ good, y i ≤ 5 / 4 ∧ z i ≤ 5 / 4 ∧
      v i ≤ 5 / 4 ∧ w i ≤ 5 / 4 ∧ 4 / 3 ≤ o i) :
    0 < margin ∧
    (∑ i : I, Real.arccos (cosine (4/3) (y i) (z i) (o i) (v i) (w i)))
      ≤ 2*Real.pi - margin ∧
    2*Real.pi + margin ≤
      ∑ i : I, Real.arccos (cosine 2 (y i) (z i) (o i) (v i) (w i)) := by
  classical
  have hc1 : (1:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hc2 : (2:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hch : (5/4:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hca : (4/3:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have cmp := cosine_mixed_comparison
  let q : ℝ := 49 / Real.sqrt 6534
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqsq : q^2 = (2401:ℝ)/6534 := by
    dsimp [q]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6534)]
    norm_num
  have hqle : q ≤ 1 := by nlinarith
  have hqgap : q < (6103:ℝ)/9801 := by nlinarith
  have hqgamma : (43:ℝ)/99 ≤ q := by nlinarith
  have hbg : beta ≤ gamma := Real.arccos_le_arccos hqgamma
  have hg0 : 0 ≤ gamma := Real.arccos_nonneg _
  have hghalf : gamma ≤ Real.pi/2 := Real.arccos_le_pi_div_two.2 (by norm_num)
  have hcos2 : Real.cos (2*gamma) = -(6103:ℝ)/9801 := by
    rw [Real.cos_two_mul]
    unfold gamma
    rw [Real.cos_arccos (by norm_num) (by norm_num)]
    norm_num
  have hupperGap : 2*Real.pi < 4*gamma+2*beta := by
    have hh := Real.arccos_lt_arccos (Real.neg_one_le_cos (2*gamma))
      (show Real.cos (2*gamma) < -q by rw [hcos2]; linarith)
      (show -q ≤ 1 by linarith)
    rw [Real.arccos_cos (by linarith) (by linarith), Real.arccos_neg] at hh
    change Real.pi-beta < 2*gamma at hh
    linarith
  have hlowerGap : 6*Real.arccos (4/7) < 2*Real.pi := by
    have hh := Real.arccos_lt_arccos (by norm_num : (-1:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 4/7) (by norm_num : (4/7:ℝ) ≤ 1)
    have he : Real.arccos (1/2:ℝ) = Real.pi/3 := by
      rw [← Real.cos_pi_div_three, Real.arccos_cos (by positivity)
        (by linarith [Real.pi_pos])]
    rw [he] at hh
    linarith
  have hmpos : 0 < margin := by
    exact lt_min (by linarith) (by linarith)
  have hlo : ∀ i, (4:ℝ)/7 ≤ cosine (4/3) (y i) (z i) (o i) (v i) (w i) := by
    intro i
    obtain ⟨hy,hz,ho,hv,hw⟩ := hbox i
    have hh := (fourcycle_envelopes.1 (4/3) (y i) (z i) (o i) (v i) (w i)
      hca hy hz ho hv hw).1
    norm_num at hh ⊢
    exact hh
  have hregular : ∀ i, cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ q := by
    intro i
    obtain ⟨hy,hz,ho,hv,hw⟩ := hbox i
    rcases hsmall i with ⟨hyb,hzb,hvb⟩ | ⟨hyb,hzb,hwb⟩ |
      ⟨hyb,hvb,hwb⟩ | ⟨hzb,hvb,hwb⟩
    · calc
        cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ cosine 2 (5/4) (5/4) 1 (5/4) 2 :=
          cmp 2 (y i) (z i) (o i) (v i) (w i) (5/4) (5/4) 1 (5/4) 2
            hc2 hy hz ho hv hw hch hch hc1 hch hc2 hyb hzb ho.1 hvb hw.2
        _ ≤ q := by
          unfold cosine
          apply quotient_le
          · norm_num [rad]
          · norm_num [rad]
          · exact hqpos.le
          · rw [hqsq]; norm_num [rad, numerator]
    · calc
        cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ cosine 2 (5/4) (5/4) 1 2 (5/4) :=
          cmp 2 (y i) (z i) (o i) (v i) (w i) (5/4) (5/4) 1 2 (5/4)
            hc2 hy hz ho hv hw hch hch hc1 hc2 hch hyb hzb ho.1 hv.2 hwb
        _ ≤ q := by
          unfold cosine
          apply quotient_le
          · norm_num [rad]
          · norm_num [rad]
          · exact hqpos.le
          · rw [hqsq]; norm_num [rad, numerator]
    · calc
        cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ cosine 2 (5/4) 2 1 (5/4) (5/4) :=
          cmp 2 (y i) (z i) (o i) (v i) (w i) (5/4) 2 1 (5/4) (5/4)
            hc2 hy hz ho hv hw hch hc2 hc1 hch hch hyb hz.2 ho.1 hvb hwb
        _ ≤ q := by
          unfold cosine
          apply quotient_le
          · norm_num [rad]
          · norm_num [rad]
          · exact hqpos.le
          · rw [hqsq]; norm_num [rad, numerator]
    · calc
        cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ cosine 2 2 (5/4) 1 (5/4) (5/4) :=
          cmp 2 (y i) (z i) (o i) (v i) (w i) 2 (5/4) 1 (5/4) (5/4)
            hc2 hy hz ho hv hw hc2 hch hc1 hch hch hy.2 hzb ho.1 hvb hwb
        _ ≤ q := by
          unfold cosine
          apply quotient_le
          · norm_num [rad]
          · norm_num [rad]
          · exact hqpos.le
          · rw [hqsq]; norm_num [rad, numerator]
  have hfavourable : ∀ i ∈ good,
      cosine 2 (y i) (z i) (o i) (v i) (w i) ≤ (43:ℝ)/99 := by
    intro i hi
    obtain ⟨hy,hz,ho,hv,hw⟩ := hbox i
    obtain ⟨hyb,hzb,hvb,hwb,hoa⟩ := hpaired i hi
    have hh := cmp 2 (y i) (z i) (o i) (v i) (w i) (5/4) (5/4) (4/3) (5/4) (5/4)
      hc2 hy hz ho hv hw hch hch hca hch hch hyb hzb hoa hvb hwb
    have he : cosine 2 (5/4) (5/4) (4/3) (5/4) (5/4) = (43:ℝ)/99 := by
      have hA : rad 2 (5/4) (5/4) = (99:ℝ)/8 := by norm_num [rad]
      have hP : numerator 2 (5/4) (5/4) (4/3) (5/4) (5/4) = (43:ℝ)/8 := by
        norm_num [numerator]
      rw [cosine, hA, hP, div_div, ← pow_two,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 99/8)]
      norm_num
    simpa only [he] using hh
  have hlowerSum : (∑ i : I, Real.arccos
      (cosine (4/3) (y i) (z i) (o i) (v i) (w i))) ≤ 6*Real.arccos (4/7) := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => Real.arccos_le_arccos (hlo i))
    simpa [hcard, nsmul_eq_mul] using hh
  have hupperSum : 4*gamma+2*beta ≤
      ∑ i : I, Real.arccos (cosine 2 (y i) (z i) (o i) (v i) (w i)) := by
    have hh : (∑ i : I, (beta + if i ∈ good then gamma-beta else 0)) ≤
        ∑ i : I, Real.arccos (cosine 2 (y i) (z i) (o i) (v i) (w i)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ good
      · simp only [hi, if_true]
        have ha : gamma ≤ Real.arccos (cosine 2 (y i) (z i) (o i) (v i) (w i)) :=
          Real.arccos_le_arccos (hfavourable i hi)
        linarith
      · simp only [hi, if_false, add_zero]
        exact Real.arccos_le_arccos (hregular i)
    have he : (∑ i : I, (beta + if i ∈ good then gamma-beta else 0)) =
        6*beta + (good.card:ℝ)*(gamma-beta) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite_mem, hcard, nsmul_eq_mul]
      ring
    rw [he] at hh
    have hfour : (4:ℝ) ≤ good.card := by exact_mod_cast hgood
    have hprod := mul_nonneg (sub_nonneg.mpr hfour) (sub_nonneg.mpr hbg)
    nlinarith
  refine ⟨hmpos, ?_, ?_⟩
  · have hm : margin ≤ 2*Real.pi-6*Real.arccos (4/7) := min_le_left _ _
    linarith
  · have hm : margin ≤ 4*gamma+2*beta-2*Real.pi := min_le_right _ _
    linarith

#print axioms critical_transition_star
end D5.S3.Geometry.Hyperideal.CriticalTransitionStar
