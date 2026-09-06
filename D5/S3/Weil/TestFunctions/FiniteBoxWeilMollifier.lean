/- GID: D5/S3/Weil/TestFunctions/FiniteBoxWeilMollifier
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/FiniteBoxWeilMollifier
   mirror-E: none(waiver:explicit-finite-order-mollifier-budget)
   anchors: []
   digest: Construct smooth even seeds by finite box averaging and derive finite-order L1 derivative budgets without assuming any derivative bound for the initial smooth bump. -/

import D5.S3.Weil.TestFunctions.QuantitativeEvenSeed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite box smoothing with explicit derivative budgets

A box density has distributional derivative equal to two endpoint atoms.
The proof below uses ordinary convolution differentiation and the fundamental
theorem of calculus, so no distribution-theory hypothesis enters the result.
After q box averages, derivatives up to order q cost at most a^(-k) in L1.
The initial normalized smooth bump supplies smoothness but contributes no
unknown derivative seminorm. This is the elementary finite-difference identity
underlying cardinal B-spline differentiation. See M. Vergne, A remark on the
convolution with the box spline, Annals of Mathematics 174 (2011), 607--618,
Section 1: the paragraph preceding Section 2 records partial_Y B(X) =
nabla_Y B(X \ Y). This module uses its one-dimensional translated/scaled
version, not that paper's semi-discrete convolution theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.TestFunctions.FiniteBoxWeilMollifier

open Set MeasureTheory Function
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.QuantitativeEvenSeed
open scoped ContDiff Convolution Pointwise

/-- Normalized box density. It is integrable, although it is not a Weil test. -/
def boxDensity (a : ℝ) : ℝ → ℂ :=
  (Icc (-a) a).indicator (fun _ => ((2 * a : ℝ) : ℂ)⁻¹)

private theorem boxDensity_support (a : ℝ) :
    tsupport (boxDensity a) ⊆ Icc (-a) a := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  exact hx (by simp [boxDensity, h])

private theorem boxDensity_compact (a : ℝ) : HasCompactSupport (boxDensity a) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (boxDensity_support a)

private theorem boxDensity_integrable (a : ℝ) : Integrable (boxDensity a) := by
  unfold boxDensity
  exact (integrableOn_const (by simp)).indicator measurableSet_Icc

private theorem boxDensity_integral (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, boxDensity a x) = 1 := by
  rw [boxDensity, integral_indicator measurableSet_Icc, setIntegral_const]
  simp only [Measure.real, Real.volume_Icc, sub_neg_eq_add]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ a + a)]
  change ((a + a : ℝ) : ℂ) * ((2 * a : ℝ) : ℂ)⁻¹ = 1
  push_cast
  field_simp [ha.ne']
  <;> ring

private theorem boxDensity_norm_integral (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, ‖boxDensity a x‖) = 1 := by
  have hnorm (x : ℝ) : ‖boxDensity a x‖ =
      (Icc (-a) a).indicator (fun _ : ℝ => (2 * a)⁻¹) x := by
    by_cases hx : x ∈ Icc (-a) a
    · simp [boxDensity, hx, norm_inv, abs_of_pos (by positivity : 0 < 2 * a)]
    · simp [boxDensity, hx]
  simp_rw [hnorm]
  rw [integral_indicator measurableSet_Icc, setIntegral_const]
  simp only [Measure.real, Real.volume_Icc, sub_neg_eq_add]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ a + a)]
  change (a + a) * (2 * a)⁻¹ = 1
  field_simp [ha.ne']
  <;> ring

/-- Box averaging produces an actual compact smooth even test. -/
def boxMean (a : ℝ) (g : WeilTestFunction) : WeilTestFunction where
  toFun := MeasureTheory.convolution (boxDensity a) g complexMul volume
  contDiff' := g.hasCompactSupport.contDiff_convolution_right (n := (⊤ : ℕ∞))
    complexMul (boxDensity_integrable a).locallyIntegrable g.contDiff
  hasCompactSupport' := (boxDensity_compact a).convolution complexMul g.hasCompactSupport
  even' _ := by
    apply convolution_neg_of_neg_eq complexMul
    · apply Filter.Eventually.of_forall
      intro x
      have hx : -x ∈ Icc (-a) a ↔ x ∈ Icc (-a) a := by
        simp only [mem_Icc]
        constructor <;> intro h <;> constructor <;> linarith
      simp only [boxDensity, indicator_apply, hx]
    · exact Filter.Eventually.of_forall g.even

private theorem integral_norm_convolution_le (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, ‖MeasureTheory.convolution f g complexMul volume x‖) ≤
      (∫ x : ℝ, ‖f x‖) * (∫ x : ℝ, ‖g x‖) := by
  let realMul : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hpoint (x : ℝ) : ‖MeasureTheory.convolution f g complexMul volume x‖ ≤
      MeasureTheory.convolution (fun t => ‖f t‖) (fun t => ‖g t‖) realMul volume x := by
    change ‖∫ t : ℝ, f t * g (x - t)‖ ≤ ∫ t : ℝ, ‖f t‖ * ‖g (x - t)‖
    simpa only [norm_mul] using
      norm_integral_le_integral_norm (fun t : ℝ => f t * g (x - t))
  calc
    _ ≤ ∫ x : ℝ, MeasureTheory.convolution (fun t => ‖f t‖)
        (fun t => ‖g t‖) realMul volume x :=
      integral_mono (hf.integrable_convolution complexMul hg).norm
        (hf.norm.integrable_convolution realMul hg.norm) hpoint
    _ = _ := by
      rw [integral_convolution (L := realMul) (ν := volume) (μ := volume) hf.norm hg.norm]
      rfl

/-- Unit-mass box convolution preserves the actual integral. -/
theorem boxMean_integral (a : ℝ) (ha : 0 < a) (g : WeilTestFunction) :
    (∫ x : ℝ, boxMean a g x) = ∫ x : ℝ, g x := by
  change (∫ x : ℝ, MeasureTheory.convolution (boxDensity a) g complexMul volume x) = _
  rw [integral_convolution (L := complexMul) (ν := volume) (μ := volume)
    (boxDensity_integrable a) g.integrable, boxDensity_integral a ha]
  change (1 : ℂ) * (∫ x : ℝ, g x) = _
  exact one_mul _

/-- Box averaging is an L1 contraction with constant exactly one. -/
theorem boxMean_norm_integral_le (a : ℝ) (ha : 0 < a) (g : WeilTestFunction) :
    (∫ x : ℝ, ‖boxMean a g x‖) ≤ ∫ x : ℝ, ‖g x‖ := by
  have h := integral_norm_convolution_le (boxDensity a) g
    (boxDensity_integrable a) g.integrable
  rw [boxDensity_norm_integral a ha, one_mul] at h
  exact h

/-- The box radius is added to the existing support radius. -/
theorem boxMean_tsupport (a L : ℝ) (g : WeilTestFunction)
    (hg : tsupport (g : ℝ → ℂ) ⊆ Icc (-L) L) :
    tsupport (boxMean a g : ℝ → ℂ) ⊆ Icc (-(a + L)) (a + L) := by
  have hs : Function.support (boxMean a g : ℝ → ℂ) ⊆
      Icc (-a) a + Icc (-L) L := by
    refine (support_convolution_subset complexMul).trans ?_
    rintro x ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, boxDensity_support a (subset_tsupport _ hu),
      v, hg (subset_tsupport _ hv), rfl⟩
  apply closure_minimal _ isClosed_Icc
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := hs hx
  exact ⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩

private theorem box_convolution_deriv (a : ℝ) (ha : 0 < a)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    MeasureTheory.convolution (boxDensity a) (deriv f) complexMul volume x =
      (f (x + a) - f (x - a)) / ((2 * a : ℝ) : ℂ) := by
  have hder (t : ℝ) : HasDerivAt (fun t : ℝ => -f (x - t)) (deriv f (x - t)) t := by
    have h := ((hf.differentiable (by simp) (x - t)).hasDerivAt.comp t
      ((hasDerivAt_const t x).sub (hasDerivAt_id t))).neg
    simpa using h
  have hit : IntervalIntegrable (fun t : ℝ => deriv f (x - t)) volume (-a) a := by
    have hc : Continuous (deriv f) := (ContDiff.iterate_deriv 1 hf).continuous
    exact (hc.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hit
  have hfun : (fun t : ℝ => boxDensity a t * deriv f (x - t)) =
      (Icc (-a) a).indicator
        (fun t => (((2 * a : ℝ) : ℂ)⁻¹) * deriv f (x - t)) := by
    funext t
    by_cases ht : t ∈ Icc (-a) a <;> simp [boxDensity, ht]
  change (∫ t : ℝ, boxDensity a t * deriv f (x - t)) = _
  rw [hfun, integral_indicator measurableSet_Icc, integral_const_mul]
  rw [← integral_Ioc_eq_integral_Icc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a), hFTC]
  simp only [sub_neg_eq_add, neg_sub_neg]
  ring

private theorem iterate_deriv_compact (g : WeilTestFunction) (k : ℕ) :
    HasCompactSupport ((deriv^[k]) (g : ℝ → ℂ)) := by
  induction k with
  | zero => exact g.hasCompactSupport
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

private theorem boxMean_iterate_deriv (a : ℝ) (g : WeilTestFunction) (k : ℕ) :
    (deriv^[k]) (boxMean a g : ℝ → ℂ) =
      MeasureTheory.convolution (boxDensity a) ((deriv^[k]) (g : ℝ → ℂ)) complexMul volume := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext x
      have h := HasCompactSupport.hasDerivAt_convolution_right complexMul
        (boxDensity_integrable a).locallyIntegrable (iterate_deriv_compact g k)
        ((ContDiff.iterate_deriv k g.contDiff).of_le (by simp)) x
      simpa only [Function.iterate_succ_apply'] using h.deriv

/-- A derivative consumes one box and becomes a centered finite difference.
This identity is proved for ordinary smooth functions by the fundamental theorem. -/
theorem boxMean_iterate_deriv_succ (a : ℝ) (ha : 0 < a)
    (g : WeilTestFunction) (k : ℕ) (x : ℝ) :
    ((deriv^[k + 1]) (boxMean a g : ℝ → ℂ)) x =
      (((deriv^[k]) (g : ℝ → ℂ)) (x + a) -
        ((deriv^[k]) (g : ℝ → ℂ)) (x - a)) / ((2 * a : ℝ) : ℂ) := by
  rw [boxMean_iterate_deriv, Function.iterate_succ_apply']
  exact box_convolution_deriv a ha _ (ContDiff.iterate_deriv k g.contDiff) x

private theorem centered_difference_L1_le
    (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ) (hf : Integrable f) :
    (∫ x : ℝ, ‖(f (x + a) - f (x - a)) / ((2 * a : ℝ) : ℂ)‖) ≤
      a⁻¹ * (∫ x : ℝ, ‖f x‖) := by
  have hp : Integrable (fun x : ℝ => f (x + a)) := hf.comp_add_right a
  have hm : Integrable (fun x : ℝ => f (x - a)) := hf.comp_sub_right a
  have hpoint (x : ℝ) :
      ‖(f (x + a) - f (x - a)) / ((2 * a : ℝ) : ℂ)‖ ≤
        (‖f (x + a)‖ + ‖f (x - a)‖) / (2 * a) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * a)]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by positivity)
  calc
    _ ≤ ∫ x : ℝ, (‖f (x + a)‖ + ‖f (x - a)‖) / (2 * a) :=
      integral_mono ((hp.sub hm).div_const _).norm
        ((hp.norm.add hm.norm).div_const _) hpoint
    _ = a⁻¹ * (∫ x : ℝ, ‖f x‖) := by
      rw [integral_div, integral_add hp.norm hm.norm,
        integral_add_right_eq_self, integral_sub_right_eq_self]
      field_simp [ha.ne']
      <;> ring

/-- q successive box averages of an actual test. -/
def boxIterate (a : ℝ) : ℕ → WeilTestFunction → WeilTestFunction
  | 0, g => g
  | q + 1, g => boxMean a (boxIterate a q g)

/-- Finite smoothing preserves the unit mass. -/
theorem boxIterate_integral (a : ℝ) (ha : 0 < a) (q : ℕ) (g : WeilTestFunction) :
    (∫ x : ℝ, boxIterate a q g x) = ∫ x : ℝ, g x := by
  induction q with
  | zero => rfl
  | succ q ih => rw [boxIterate, boxMean_integral a ha, ih]

/-- Each derivative is charged to a distinct box. No initial derivative
seminorm is supplied as a hypothesis. -/
theorem boxIterate_derivative_L1_budget
    (a : ℝ) (ha : 0 < a) (g : WeilTestFunction) (q k : ℕ) (hk : k ≤ q) :
    (∫ x : ℝ, ‖((deriv^[k]) (boxIterate a q g : ℝ → ℂ)) x‖) ≤
      (a⁻¹) ^ k * (∫ x : ℝ, ‖g x‖) := by
  induction q generalizing k with
  | zero =>
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [boxIterate]
  | succ q ih =>
      cases k with
      | zero =>
          have h0 := ih 0 (Nat.zero_le q)
          simpa only [Function.iterate_zero_apply, pow_zero, one_mul, boxIterate] using
            (boxMean_norm_integral_le a ha (boxIterate a q g)).trans h0
      | succ k =>
          have hprev := ih k (Nat.le_of_succ_le_succ hk)
          have hint : Integrable ((deriv^[k]) (boxIterate a q g : ℝ → ℂ)) :=
            (ContDiff.iterate_deriv k (boxIterate a q g).contDiff).continuous
              .integrable_of_hasCompactSupport (iterate_deriv_compact _ k)
          simp_rw [boxIterate, boxMean_iterate_deriv_succ a ha]
          calc
            _ ≤ a⁻¹ * (∫ x : ℝ,
                ‖((deriv^[k]) (boxIterate a q g : ℝ → ℂ)) x‖) :=
              centered_difference_L1_le a ha _ hint
            _ ≤ a⁻¹ * ((a⁻¹) ^ k * (∫ x : ℝ, ‖g x‖)) :=
              mul_le_mul_of_nonneg_left hprev (inv_nonneg.mpr ha.le)
            _ = _ := by ring

/-- The complete support budget after q box averages. -/
theorem boxIterate_tsupport (a L : ℝ) (g : WeilTestFunction)
    (hg : tsupport (g : ℝ → ℂ) ⊆ Icc (-L) L) (q : ℕ) :
    tsupport (boxIterate a q g : ℝ → ℂ) ⊆
      Icc (-(L + (q : ℝ) * a)) (L + (q : ℝ) * a) := by
  induction q with
  | zero => simpa [boxIterate] using hg
  | succ q ih =>
      have h := boxMean_tsupport a (L + (q : ℝ) * a) (boxIterate a q g) ih
      have heq : a + (L + (q : ℝ) * a) = L + ((q + 1 : ℕ) : ℝ) * a := by
        push_cast
        ring
      simpa only [boxIterate, heq] using h

/-- The box width is explicit even when q=0. -/
def finiteBoxWidth (h : ℝ) (q : ℕ) : ℝ := h / (2 * ((q : ℝ) + 1))

/-- A compact smooth even seed whose first q derivative seminorms are controlled. -/
def finiteBoxSeed (h : ℝ) (hh : 0 < h) (q : ℕ) : WeilTestFunction :=
  boxIterate (finiteBoxWidth h q) q (normalizedEvenSeed (h / 2) (by positivity))

/-- Simultaneous explicit support, mass, L1 norm and all required finite jets.
The only free parameters are the positive radius h and the integer order q. -/
theorem finiteBoxSeed_budget (h : ℝ) (hh : 0 < h) (q : ℕ) :
    tsupport (finiteBoxSeed h hh q : ℝ → ℂ) ⊆ Icc (-h) h ∧
      (∫ x : ℝ, finiteBoxSeed h hh q x) = 1 ∧
      (∫ x : ℝ, ‖finiteBoxSeed h hh q x‖) = 1 ∧
      ∀ k : ℕ, k ≤ q →
        (∫ x : ℝ, ‖((deriv^[k]) (finiteBoxSeed h hh q : ℝ → ℂ)) x‖) ≤
          (2 * ((q : ℝ) + 1) / h) ^ k := by
  have ha : 0 < finiteBoxWidth h q := by unfold finiteBoxWidth; positivity
  have hmass : (∫ x : ℝ, finiteBoxSeed h hh q x) = 1 := by
    rw [finiteBoxSeed, boxIterate_integral _ ha, normalizedEvenSeed_integral]
  have hjet (k : ℕ) (hk : k ≤ q) :
      (∫ x : ℝ, ‖((deriv^[k]) (finiteBoxSeed h hh q : ℝ → ℂ)) x‖) ≤
        (2 * ((q : ℝ) + 1) / h) ^ k := by
    have hb := boxIterate_derivative_L1_budget (finiteBoxWidth h q) ha
      (normalizedEvenSeed (h / 2) (by positivity)) q k hk
    rw [normalizedEvenSeed_norm_integral, mul_one] at hb
    simpa only [finiteBoxSeed, finiteBoxWidth, inv_div] using hb
  have hnorm : (∫ x : ℝ, ‖finiteBoxSeed h hh q x‖) = 1 := by
    apply le_antisymm
    · simpa using hjet 0 (Nat.zero_le q)
    · have hb := norm_integral_le_integral_norm (fun x : ℝ => finiteBoxSeed h hh q x)
      simpa only [hmass, norm_one] using hb
  refine ⟨?_, hmass, hnorm, hjet⟩
  have hs := boxIterate_tsupport (finiteBoxWidth h q) (h / 2)
    (normalizedEvenSeed (h / 2) (by positivity))
    (normalizedEvenSeed_tsupport _ _) q
  have hr : h / 2 + (q : ℝ) * finiteBoxWidth h q ≤ h := by
    unfold finiteBoxWidth
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hp : 0 < 2 * ((q : ℝ) + 1) := by positivity
    have hpart : (q : ℝ) * (h / (2 * ((q : ℝ) + 1))) ≤ h / 2 := by
      rw [mul_div_assoc]
      apply (div_le_iff₀ hp).2
      nlinarith
    linarith
  intro x hx
  have h := hs hx
  exact ⟨(neg_le_neg hr).trans h.1, h.2.trans hr⟩

/-- The derivative-controlled seed also has the explicit denominator floor
needed by squared-node interpolation. The radius is unchanged. -/
theorem finiteBoxSeed_transform_lower
    (R : ℝ) (hR : 0 ≤ R) (q : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    (1 / 2 : ℝ) ≤ ‖fourierLaplace
      (finiteBoxSeed (quantitativeSeedRadius R) (quantitativeSeedRadius_pos R hR) q) z‖ := by
  let h := quantitativeSeedRadius R
  have hh : 0 < h := quantitativeSeedRadius_pos R hR
  have hsmall : h * ‖z‖ ≤ (1 / 4 : ℝ) := by
    calc
      h * ‖z‖ = ‖z‖ / (4 * (R + 1)) := by
        dsimp [h, quantitativeSeedRadius]
        ring
      _ ≤ 1 / 4 := by
        apply (div_le_iff₀ (by positivity : 0 < 4 * (R + 1))).2
        nlinarith
  obtain ⟨hs, hmass, hnorm, _⟩ := finiteBoxSeed_budget h hh q
  have hpert := fourierLaplace_sub_one_norm_le (finiteBoxSeed h hh q) h hh.le
    hs hmass hnorm z (by linarith)
  have hreverse := norm_sub_norm_le (1 : ℂ) (fourierLaplace (finiteBoxSeed h hh q) z)
  rw [norm_one, norm_sub_rev] at hreverse
  change (1 / 2 : ℝ) ≤ ‖fourierLaplace (finiteBoxSeed h hh q) z‖
  linarith

#print axioms boxMean_iterate_deriv_succ
#print axioms boxIterate_derivative_L1_budget
#print axioms finiteBoxSeed_budget
#print axioms finiteBoxSeed_transform_lower

end D5.S3.Weil.TestFunctions.FiniteBoxWeilMollifier
