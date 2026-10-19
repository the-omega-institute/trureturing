/- GID: D5/S3/StatisticalMechanics/SingleEntryMixtureBridge
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/SingleEntryMixtureBridge
   mirror-E: none(waiver:single-entry-forward-mixture)
   anchors: []
   utility: none
   digest: The actual inhibited-chain trajectory has a positive product-mixture representation. -/

import D5.S3.StatisticalMechanics.SingleEntryProductMixture
import D5.S3.StatisticalMechanics.SingleEntrySpectralGap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open Set MeasureTheory Matrix

namespace D5.S3.StatisticalMechanics.SingleEntryMixtureBridge
open SingleEntryFiniteNetwork SingleEntrySecularRoot SingleEntryProductMixture
open SingleEntrySpectralGap

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem forced_decay_integral (f v : ℝ → ℝ) (c t : ℝ)
    (ht : 0 ≤ t) (hf0 : f 0 = 0)
    (hf : ∀ u, 0 ≤ u → HasDerivAt f (-c * f u + v u) u)
    (hv : ContinuousOn v (Icc 0 t)) :
    f t = ∫ u in 0..t, v (t - u) * Real.exp (-c * u) := by
  have hd (u : ℝ) (hu : u ∈ uIcc 0 t) :
      HasDerivAt (fun x => Real.exp (c * x) * f x) (Real.exp (c * u) * v u) u := by
    have hu0 : 0 ≤ u := (show u ∈ Icc 0 t by simpa [uIcc_of_le ht] using hu).1
    convert (((hasDerivAt_id u).const_mul c).exp.mul (hf u hu0)) using 1 <;>
      first | rfl | (dsimp; ring)
  have hi : IntervalIntegrable (fun u => Real.exp (c * u) * v u) volume 0 t := by
    apply ContinuousOn.intervalIntegrable_of_Icc ht
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hv
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simp only [mul_zero, Real.exp_zero, one_mul, hf0, sub_zero] at he
  have hfac (u : ℝ) : Real.exp (-c * t) * (Real.exp (c * u) * v u) =
      v u * Real.exp (-c * (t - u)) := by
    calc
      _ = v u * (Real.exp (-c * t) * Real.exp (c * u)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
  have hswap : (∫ u in 0..t, v u * Real.exp (-c * (t - u))) =
      ∫ u in 0..t, v (t - u) * Real.exp (-c * u) := by
    have hh := intervalIntegral.integral_comp_sub_left
      (fun u => v (t - u) * Real.exp (-c * u)) t (a := 0) (b := t)
    simpa using hh
  rw [← hswap]
  simp_rw [← hfac]
  rw [intervalIntegral.integral_const_mul, he]
  rw [← mul_assoc, ← Real.exp_add]
  simp

private theorem mode_integral (k : Rates I) (p : ℝ → Option (Finset I) → ℝ)
    (hp : ForwardSolution k p) (S : Finset I) (t : ℝ) (ht : 0 ≤ t) :
    (coordinateTransform k.a k.b *ᵥ p t) (some S) =
      ∫ u in 0..t, modeWeight k.a k.b S *
        (k.theta * p (t-u) none - k.eta * p (t-u) (some ∅)) *
        Real.exp (-subsetRate k.a k.b S * u) := by
  let f := fun u => (coordinateTransform k.a k.b *ᵥ p u) (some S)
  let v := fun u => modeWeight k.a k.b S *
    (k.theta * p u none - k.eta * p u (some ∅))
  have pc (x : Option (Finset I)) : ContinuousOn (fun u => p u x) (Icc 0 t) := by
    intro u hu
    exact (hp.2 u hu.1 x).continuousAt.continuousWithinAt
  apply forced_decay_integral f v (subsetRate k.a k.b S) t ht
  · simp [f, hp.1, mulVec, dotProduct, coordinateTransform, Fintype.sum_option,
      Pi.single_apply]
  · intro u hu
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun x _ => (hp.2 u hu x).const_mul (coordinateTransform k.a k.b (some S) x))
    have hg := congrFun (transform_generator k (p u)) (some S)
    rw [Pi.neg_apply, action_some,
      ← transform_empty k.a k.b k.a_pos k.b_pos] at hg
    have hR : (coordinateTransform k.a k.b *ᵥ p u) none = p u none := by
      simp [mulVec, dotProduct, Fintype.sum_option, coordinateTransform]
    rw [hR] at hg
    convert hd using 1
    · rfl
    · change -(subsetRate k.a k.b S) * f u + v u =
        (coordinateTransform k.a k.b *ᵥ (generator k *ᵥ p u)) (some S)
      rw [hg]
      dsimp [f, v]
      ring
  · exact continuousOn_const.mul
      ((continuousOn_const.mul (pc none)).sub (continuousOn_const.mul (pc (some ∅))))

private theorem free_product_expansion (k : Rates I) (σ : Finset I) (u : ℝ) :
    (∑ S : Finset I, productBasis k.a k.b σ S * modeWeight k.a k.b S *
      Real.exp (-subsetRate k.a k.b S * u)) =
      productKernel (fun i v => SingleEntrySecularRoot.occupancy k.a k.b i *
        (1 - Real.exp (-siteRate k.a k.b i * v))) σ u := by
  have hexp (S : Finset I) :
      Real.exp (-subsetRate k.a k.b S * u) =
        ∏ i, if i ∈ S then Real.exp (-siteRate k.a k.b i * u) else 1 := by
    rw [Fintype.prod_ite_mem, ← Real.exp_sum]
    congr 1
    simp [subsetRate, Finset.sum_mul, Finset.sum_neg_distrib]
  calc
    _ = ∑ S : Finset I, ∏ i,
        if i ∈ S then
          localBasis (k.a i) (k.b i) (decide (i ∈ σ)) true *
            SingleEntrySecularRoot.occupancy k.a k.b i * Real.exp (-siteRate k.a k.b i * u)
        else localBasis (k.a i) (k.b i) (decide (i ∈ σ)) false *
            (1 - SingleEntrySecularRoot.occupancy k.a k.b i) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [hexp, productBasis, modeWeight, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [hi]
    _ = _ := by
      rw [sum_subset_product]
      apply Finset.prod_congr rfl
      intro i _
      have hs : k.a i + k.b i ≠ 0 := ne_of_gt (add_pos (k.a_pos i) (k.b_pos i))
      by_cases hi : i ∈ σ <;>
        simp [productKernel, hi, localBasis, SingleEntrySecularRoot.occupancy, siteRate] <;>
        field_simp [ne_of_gt (k.b_pos i), hs] <;> ring

private theorem trajectory_mixture (k : Rates I) (p : ℝ → Option (Finset I) → ℝ)
    (hp : ForwardSolution k p) (σ : Finset I) (t : ℝ) (ht : 0 ≤ t) :
    p t (some σ) = mixtureMass
      (fun u => k.theta * p (t-u) none - k.eta * p (t-u) (some ∅))
      (fun i u => SingleEntrySecularRoot.occupancy k.a k.b i *
        (1 - Real.exp (-siteRate k.a k.b i * u))) t σ := by
  have pc (x : Option (Finset I)) : ContinuousOn (fun u => p (t-u) x) (Icc 0 t) := by
    have hh : ContinuousOn (fun u => p u x) (Icc 0 t) := by
      intro u hu
      exact (hp.2 u hu.1 x).continuousAt.continuousWithinAt
    exact hh.comp (f := fun u : ℝ => t-u) (s := Icc 0 t)
      (continuous_const.sub continuous_id).continuousOn (by
      intro u hu
      constructor <;> linarith [hu.1, hu.2]
      )
  have hrec := congrFun (mulVec_mulVec (p t) (inverseTransform k.a k.b)
    (coordinateTransform k.a k.b)) (some σ)
  rw [transform_inverse k.a k.b k.a_pos k.b_pos, one_mulVec] at hrec
  have hrow (x : Option (Finset I) → ℝ) :
      (inverseTransform k.a k.b *ᵥ x) (some σ) =
        ∑ S, productBasis k.a k.b σ S * x (some S) := by
    simp [mulVec, dotProduct, Fintype.sum_option, inverseTransform]
  rw [hrow] at hrec
  rw [← hrec]
  simp_rw [mode_integral k p hp _ t ht, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro u _
    have he := free_product_expansion k σ u
    simp only [mixtureMass]
    rw [show (∑ S : Finset I, productBasis k.a k.b σ S *
        (modeWeight k.a k.b S * (k.theta * p (t-u) none - k.eta * p (t-u) (some ∅)) *
          Real.exp (-subsetRate k.a k.b S * u))) =
        (k.theta * p (t-u) none - k.eta * p (t-u) (some ∅)) *
          ∑ S : Finset I, productBasis k.a k.b σ S * modeWeight k.a k.b S *
            Real.exp (-subsetRate k.a k.b S * u) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; ring]
    rw [he]
  · intro S _
    apply ContinuousOn.intervalIntegrable_of_Icc ht
    exact continuousOn_const.mul ((continuousOn_const.mul
      ((continuousOn_const.mul (pc none)).sub (continuousOn_const.mul (pc (some ∅))))).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)

/-- The actual forward law has a strict minor for every incomparable pair.
The integral representation is derived from its independent generator. -/
theorem finite_network_strict_mtp2 (k : Rates I)
    (p : ℝ → Option (Finset I) → ℝ) (hp : ForwardSolution k p)
    (t : ℝ) (ht : 0 < t)
    (S T : Finset I) (hST : ¬ S ⊆ T) (hTS : ¬ T ⊆ S) :
    p t (some S) * p t (some T) < p t (some (S ∩ T)) * p t (some (S ∪ T)) := by
  obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
  obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hTS
  have hij : i ≠ j := by intro he; subst j; exact hiT hjT
  let g := fun i u => SingleEntrySecularRoot.occupancy k.a k.b i *
    (1 - Real.exp (-siteRate k.a k.b i * u))
  let h := fun u => k.theta * p (t-u) none - k.eta * p (t-u) (some ∅)
  have pc (x : Option (Finset I)) : ContinuousOn (fun u => p (t-u) x) (Icc 0 t) := by
    have hh : ContinuousOn (fun u => p u x) (Icc 0 t) := by
      intro u hu
      exact (hp.2 u hu.1 x).continuousAt.continuousWithinAt
    exact hh.comp (f := fun u : ℝ => t-u) (s := Icc 0 t)
      (continuous_const.sub continuous_id).continuousOn (by
      intro u hu
      constructor <;> linarith [hu.1, hu.2]
      )
  have hpos (u : ℝ) (hu : u ∈ Icc 0 t) : 0 < h u := by
    by_cases he : t-u = 0
    · simp [h, he, hp.1, Pi.single_apply, k.theta_pos]
    · exact ((finite_network_strict_pair k).2 p hp i j hij (t-u)
        (lt_of_le_of_ne (sub_nonneg.mpr hu.2) (Ne.symm he))).2.2.2.2.1
  have hgc (i : I) : ContinuousOn (g i) (Icc 0 t) := by dsimp [g]; fun_prop
  have hgb (i : I) (u : ℝ) (hu : u ∈ Icc 0 t) : 0 ≤ g i u ∧ g i u < 1 := by
    have hs := add_pos (k.a_pos i) (k.b_pos i)
    have hq : 0 < SingleEntrySecularRoot.occupancy k.a k.b i := div_pos (k.a_pos i) hs
    have hq1 : SingleEntrySecularRoot.occupancy k.a k.b i < 1 := by
      dsimp [SingleEntrySecularRoot.occupancy, siteRate]
      exact (div_lt_one hs).mpr (by linarith [k.b_pos i])
    have he : Real.exp (-siteRate k.a k.b i * u) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hu.1)
    dsimp [g]
    constructor
    · exact mul_nonneg hq.le (sub_nonneg.mpr he)
    · nlinarith [Real.exp_pos (-siteRate k.a k.b i * u)]
  have hgm (i : I) : StrictMonoOn (g i) (Icc 0 t) := by
    intro x hx y hy hxy
    have hs := add_pos (k.a_pos i) (k.b_pos i)
    have hq := div_pos (k.a_pos i) hs
    have he : Real.exp (-siteRate k.a k.b i * y) < Real.exp (-siteRate k.a k.b i * x) := by
      apply Real.exp_lt_exp.mpr
      dsimp [siteRate]
      nlinarith
    exact mul_lt_mul_of_pos_left (sub_lt_sub_left he 1) hq
  have hm := strict_mtp2_product_mixture h g t ht
    ((continuousOn_const.mul (pc none)).sub (continuousOn_const.mul (pc (some ∅))))
    (fun u hu => (hpos u hu).le) (fun u hu => hpos u ⟨hu.1.le, hu.2.le⟩)
    hgc hgb hgm S T hST hTS
  dsimp [h, g] at hm
  rw [← trajectory_mixture k p hp S t ht.le,
    ← trajectory_mixture k p hp T t ht.le,
    ← trajectory_mixture k p hp (S ∩ T) t ht.le,
    ← trajectory_mixture k p hp (S ∪ T) t ht.le] at hm
  exact hm

#print axioms finite_network_strict_mtp2

end D5.S3.StatisticalMechanics.SingleEntryMixtureBridge
