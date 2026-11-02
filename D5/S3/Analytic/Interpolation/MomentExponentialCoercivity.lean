/- GID: D5/S3/Analytic/Interpolation/MomentExponentialCoercivity
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/MomentExponentialCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus]
   utility: none
   digest: Finite causal squares control exponential atomic energy by actual primitive moments. -/

import D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
import D5.S3.Analytic.MomentOrthogonalPrimitiveGap
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
The genuinely new bridge is finite and causal. Write A for the actual inclusive
atomic prefix, B(t)=sum a_i max(t-x_i,0),
g(t)=sum a_i (1-exp(-lam max(t-x_i,0)))/lam and h=(B-g)/lam.
Their right derivatives are B'=A, g'=Z=A-lam*g, h'=g. The exact causal Gram
identity is Q=2*lam*integral_[0,D] |Z|²+|Z(D)|². Two ordinary right-FTC
identities, with B(D)=0 paid by the first atomic moment, give

 Q = 2*lam*E(A)-2*lam³*E(B)+2*lam⁵*E(h)+lam⁴*|h(D)|².

Thus the required primitive-to-exponential bridge has an explicit nonnegative
remainder; neither positive definiteness nor distributional IBP is a premise.
The public atomic identity is consumed to turn this into the bound on the
actual prefix correlation. The newly merged complex L2 primitive gap is then
consumed for the exact quantitative endpoint. Atomic moments 0,...,q give
prefix moments 0,...,q-1, with no off-by-one change in q.

All helpers are private and occur on the final theorem's proof path. Finite
sum algebra never sorts or separates nodes and never divides by an energy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory Set Filter
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy

namespace D5.S3.Analytic.Interpolation.MomentExponentialCoercivity

variable {I : Type u} [Fintype I]

private def ramp (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, a i * (max (t - x i) 0 : ℝ)

private def resolvent (lam : ℝ) (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, a i * (((1 - Real.exp (-lam * max (t - x i) 0)) / lam : ℝ) : ℂ)

private def secondResolvent (lam : ℝ) (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  (ramp x a t - resolvent lam x a t) / (lam : ℂ)

private def response (lam : ℝ) (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, if x i ≤ t then a i * (Real.exp (-lam * (t - x i)) : ℂ) else 0

private lemma prefix_below (x : I → ℝ) (a : I → ℂ) (t : ℝ)
    (ht : ∀ i, t < x i) : «prefix» x a t = 0 := by
  classical
  simp [«prefix», fun i => not_le.mpr (ht i)]

private lemma prefix_above (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (t : ℝ) (ht : ∀ i, x i ≤ t) : «prefix» x a t = 0 := by
  classical
  simp [«prefix», ht, ha]

private lemma prefix_energy_window (x : I → ℝ) (a : I → ℂ)
    (D : ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0) :
    (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) =
      ∫ t in Icc 0 D, ‖«prefix» x a t‖ ^ 2 := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rcases lt_or_ge t 0 with ht0 | ht0
  · rw [prefix_below x a t (fun i => ht0.trans_le (hx i).1)]
    simp
  · have htD : D < t := lt_of_not_ge (fun h => ht ⟨ht0, h⟩)
    rw [prefix_above x a ha t (fun i => (hx i).2.trans htD.le)]
    simp

/-- A continuous multiplier of the actual prefix is integrable on a compact
window. This supplies every mixed term in the right-FTC energy calculation. -/
private lemma prefix_mul_integrable (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) :
    IntegrableOn (fun t => «prefix» x a t * f t) (Icc 0 D) := by
  classical
  have he : (fun t => «prefix» x a t * f t) =
      fun t => ∑ i, (Ici (x i)).indicator (fun t => a i * f t) t := by
    ext t
    simp only [«prefix», Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x i ≤ t <;> simp [Set.indicator, hi]
  rw [he]
  exact integrable_finsetSum _ (fun i _ =>
    ((continuous_const.mul hf).integrableOn_Icc).indicator measurableSet_Ici)

private lemma prefix_memLp (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (ha : ∑ i, a i = 0) :
    MemLp («prefix» x a) 2 (volume.restrict (Icc 0 D)) := by
  have hi : IntegrableOn («prefix» x a) (Icc 0 D) := by
    simpa only [mul_one] using prefix_mul_integrable x a D (fun _ => 1) continuous_const
  exact (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
    (shifted_hinge_prefix_energy x a ha 0).2.1.integrableOn

/-- Exact integration of a prefix against a continuous multiplier. The upper
cutoff is retained; this is valid without zero mass. -/
private lemma prefix_mul_integral (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in Icc 0 D, «prefix» x a t * f t) =
      ∑ i, a i * (∫ t in Icc (x i) D, f t) := by
  classical
  have he (t : ℝ) : «prefix» x a t * f t =
      ∑ i, (Ici (x i)).indicator (fun t => a i * f t) t := by
    simp only [«prefix», Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x i ≤ t <;> simp [Set.indicator, hi]
  simp_rw [he]
  rw [integral_finsetSum (f := fun i t =>
    (Ici (x i)).indicator (fun t => a i * f t) t) Finset.univ (fun i _ =>
    ((continuous_const.mul hf).integrableOn_Icc).indicator measurableSet_Ici)]
  apply Finset.sum_congr rfl
  intro i _
  rw [setIntegral_indicator measurableSet_Ici]
  have hs : Icc (0 : ℝ) D ∩ Ici (x i) = Icc (x i) D := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Ici]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨(hx i).1.trans h.1, h.2⟩, h.1⟩⟩
  rw [hs, integral_const_mul]

private lemma prefix_moments (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (q : ℕ)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    ∀ r : ℕ, r < q → ∫ t in Icc 0 D, (t : ℂ) ^ r * «prefix» x a t = 0 := by
  intro r hr
  have hpow (l : ℝ) (hl : l ≤ D) :
      (∫ t in Icc l D, (t : ℂ) ^ r) =
        (((D : ℂ) ^ (r + 1) - (l : ℂ) ^ (r + 1)) / ((r + 1 : ℕ) : ℂ)) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hl]
    calc
      _ = ((∫ t in l..D, t ^ r : ℝ) : ℂ) := by
        simp only [← Complex.ofReal_pow, intervalIntegral.integral_ofReal]
      _ = _ := by rw [integral_pow]; push_cast; rfl
  calc
    _ = ∫ t in Icc 0 D, «prefix» x a t * (t : ℂ) ^ r := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => mul_comm _ _)
    _ = ∑ i, a i *
        (((D : ℂ) ^ (r + 1) - (x i : ℂ) ^ (r + 1)) / ((r + 1 : ℕ) : ℂ)) := by
      rw [prefix_mul_integral x a D hx _ (by fun_prop)]
      apply Finset.sum_congr rfl
      intro i _
      rw [hpow (x i) (hx i).2]
    _ = ((∑ i, a i) * (D : ℂ) ^ (r + 1) -
        (∑ i, a i * (x i : ℂ) ^ (r + 1))) / ((r + 1 : ℕ) : ℂ) := by
      simp only [div_eq_mul_inv, sub_mul, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul, mul_assoc]
    _ = 0 := by
      have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
      rw [ha, hm (r + 1) (by omega)]
      simp

private lemma ramp_continuous (x : I → ℝ) (a : I → ℂ) : Continuous (ramp x a) := by
  unfold ramp
  fun_prop

private lemma resolvent_continuous (lam : ℝ) (x : I → ℝ) (a : I → ℂ) :
    Continuous (resolvent lam x a) := by
  unfold resolvent
  fun_prop

private lemma second_continuous (lam : ℝ) (x : I → ℝ) (a : I → ℂ) :
    Continuous (secondResolvent lam x a) :=
  ((ramp_continuous x a).sub (resolvent_continuous lam x a)).div_const _

private lemma response_eq (lam : ℝ) (hlam : lam ≠ 0)
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    response lam x a t = «prefix» x a t - (lam : ℂ) * resolvent lam x a t := by
  classical
  have hlc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  simp only [response, «prefix», resolvent, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ≤ t
  · rw [ite_eq_left hi, ite_eq_left hi, max_eq_left (sub_nonneg.mpr hi)]
    push_cast
    field_simp [hlam, hlc]
    <;> ring
  · rw [ite_eq_right hi, ite_eq_right hi, max_eq_right (by linarith : t - x i ≤ 0)]
    simp

/-- Right derivatives include atoms at the evaluation point, matching the
inclusive prefix exactly, rather than only almost everywhere. -/
private lemma ramp_right (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    HasDerivWithinAt (ramp x a) («prefix» x a t) (Ioi t) t := by
  classical
  unfold ramp «prefix»
  apply HasDerivWithinAt.fun_sum
  intro i _
  by_cases hi : x i ≤ t
  · have hd : HasDerivWithinAt (fun y : ℝ => a i * ((y - x i : ℝ) : ℂ))
        (a i) (Ioi t) t := by
      simpa using (((hasDerivAt_id t).sub_const (x i)).ofReal_comp.const_mul (a i)).hasDerivWithinAt
        (s := Ioi t)
    have ht : max (t - x i) 0 = t - x i := max_eq_left (sub_nonneg.mpr hi)
    simpa only [ite_eq_left hi, mul_one] using hd.congr
      (fun y hy => by rw [max_eq_left (by linarith [show t < y from hy] : 0 ≤ y - x i)])
      (by rw [ht])
  · have hit : t < x i := lt_of_not_ge hi
    have hd : HasDerivWithinAt (fun _ : ℝ => (0 : ℂ)) 0 (Ioi t) t :=
      (hasDerivAt_const t (0 : ℂ)).hasDerivWithinAt
    simp only [ite_eq_right hi]
    apply hd.congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hit)] with y hy
      rw [max_eq_right (by linarith [show y < x i from hy] : y - x i ≤ 0)]
      simp
    · rw [max_eq_right (by linarith : t - x i ≤ 0)]
      simp

private lemma resolvent_right (lam : ℝ) (hlam : lam ≠ 0)
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    HasDerivWithinAt (resolvent lam x a) (response lam x a t) (Ioi t) t := by
  classical
  unfold resolvent response
  apply HasDerivWithinAt.fun_sum
  intro i _
  by_cases hi : x i ≤ t
  · have hd := (((hasDerivAt_const t (1 : ℝ)).sub
        ((((hasDerivAt_id t).sub_const (x i)).const_mul (-lam)).exp)).div_const lam).ofReal_comp.const_mul (a i)
    have hd' : HasDerivWithinAt
        (fun y : ℝ => a i * (((1 - Real.exp (-lam * (y - x i))) / lam : ℝ) : ℂ))
        (a i * (Real.exp (-lam * (t - x i)) : ℂ)) (Ioi t) t := by
      have he : (0 - Real.exp (-lam * (t - x i)) * (-lam * 1)) / lam =
          Real.exp (-lam * (t - x i)) := by field_simp; ring
      simpa only [Pi.sub_apply, id_eq, he] using hd.hasDerivWithinAt (s := Ioi t)
    simp only [ite_eq_left hi]
    exact hd'.congr
      (fun y hy => by rw [max_eq_left (by linarith [show t < y from hy] : 0 ≤ y - x i)])
      (by rw [max_eq_left (sub_nonneg.mpr hi)])
  · have hit : t < x i := lt_of_not_ge hi
    simp only [ite_eq_right hi]
    apply ((hasDerivAt_const t (0 : ℂ)).hasDerivWithinAt).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hit)] with y hy
      rw [max_eq_right (by linarith [show y < x i from hy] : y - x i ≤ 0)]
      simp
    · rw [max_eq_right (by linarith : t - x i ≤ 0)]
      simp

private lemma second_right (lam : ℝ) (hlam : lam ≠ 0)
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    HasDerivWithinAt (secondResolvent lam x a) (resolvent lam x a t) (Ioi t) t := by
  have hlc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  have hd := ((ramp_right x a t).sub (resolvent_right lam hlam x a t)).div_const (lam : ℂ)
  change HasDerivWithinAt (fun y => (ramp x a y - resolvent lam x a y) / (lam : ℂ))
    (resolvent lam x a t) (Ioi t) t
  apply hd.congr_deriv
  rw [response_eq lam hlam]
  field_simp [hlc]
  <;> ring

private lemma initial_values (lam : ℝ) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, 0 ≤ x i) :
    ramp x a 0 = 0 ∧ resolvent lam x a 0 = 0 ∧ secondResolvent lam x a 0 = 0 := by
  have hz (i : I) : max (-x i) 0 = 0 := max_eq_right (by linarith [hx i])
  simp [ramp, resolvent, secondResolvent, hz]

private lemma ramp_is_primitive (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hD : 0 ≤ D) :
    ramp x a D = ∫ t in (0 : ℝ)..D, «prefix» x a t := by
  have hf := (prefix_mul_integrable x a D (fun _ => 1) continuous_const)
  simp only [mul_one] at hf
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hD).mpr hf
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hD
    (ramp_continuous x a).continuousOn (fun t _ => ramp_right x a t) hi
  rw [(initial_values 1 x a hx).1, sub_zero] at h
  exact h.symm

private lemma ramp_terminal (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (hx : ∀ i, x i ≤ D) (ha : ∑ i, a i = 0)
    (hfirst : ∑ i, a i * (x i : ℂ) = 0) : ramp x a D = 0 := by
  have he (i : I) : max (D - x i) 0 = D - x i := max_eq_left (sub_nonneg.mpr (hx i))
  simp only [ramp, he, Complex.ofReal_sub,
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ha, hfirst]
  ring

private lemma square_right {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hd : HasDerivWithinAt f v (Ioi t) t) :
    HasDerivWithinAt (fun y => ‖f y‖ ^ 2)
      (2 * (star (f t) * v).re) (Ioi t) t := by
  have hre : HasDerivWithinAt (fun y => (f y).re) v.re (Ioi t) t := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using!
      Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have him : HasDerivWithinAt (fun y => (f y).im) v.im (Ioi t) t := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using!
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have hs := (hre.pow 2).add (him.pow 2)
  convert hs using 1
  · ext y
    change ‖f y‖ ^ 2 = (f y).re ^ 2 + (f y).im ^ 2
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  · simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring

private lemma square_FTC (D : ℝ) (hD : 0 ≤ D) (f v : ℝ → ℂ)
    (hf : Continuous f) (hd : ∀ t, HasDerivWithinAt f (v t) (Ioi t) t)
    (hi : IntegrableOn (fun t => (star (f t) * v t).re) (Icc 0 D)) :
    ‖f D‖ ^ 2 - ‖f 0‖ ^ 2 =
      2 * (∫ t in Icc 0 D, (star (f t) * v t).re) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hD
    (hf.norm.pow 2).continuousOn (fun t _ => square_right (hd t))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hD).mpr (hi.const_mul 2))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hD,
    ← integral_Icc_eq_integral_Ioc] at h
  exact h.symm

private lemma square_sub (z w : ℂ) (r : ℝ) :
    ‖z - (r : ℂ) * w‖ ^ 2 = ‖z‖ ^ 2 -
      2 * r * (star w * z).re + r ^ 2 * ‖w‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- Pair overlap of the finite causal exponentials, by actual integration
including the finite upper boundary term. The identity requires only a
nonzero rate; its positivity use is restricted to positive rates. -/
private lemma causal_pair (lam D l r : ℝ) (hlam : lam ≠ 0)
    (hl : l ∈ Icc (0 : ℝ) D) (hr : r ∈ Icc (0 : ℝ) D) :
    let f : ℝ → ℝ := fun t =>
      (if l ≤ t then Real.exp (-lam * (t - l)) else 0) *
      (if r ≤ t then Real.exp (-lam * (t - r)) else 0)
    IntegrableOn f (Icc 0 D) ∧
      2 * lam * (∫ t in Icc 0 D, f t) +
        Real.exp (-lam * (D - l)) * Real.exp (-lam * (D - r)) =
          Real.exp (-lam * |l - r|) := by
  dsimp only
  let m := max l r
  let F : ℝ → ℝ := fun t => Real.exp (-lam * (t - l)) * Real.exp (-lam * (t - r))
  have hc : Continuous F := by dsimp [F]; fun_prop
  have he : (fun t : ℝ =>
      (if l ≤ t then Real.exp (-lam * (t - l)) else 0) *
      (if r ≤ t then Real.exp (-lam * (t - r)) else 0)) = (Ici m).indicator F := by
    ext t
    by_cases hl' : l ≤ t <;> by_cases hr' : r ≤ t <;>
      simp [Set.indicator, F, m, hl', hr']
  have hm : m ∈ Icc (0 : ℝ) D := ⟨le_max_of_le_left hl.1, max_le hl.2 hr.2⟩
  have hint : (∫ t in Icc 0 D, (Ici m).indicator F t) = ∫ t in m..D, F t := by
    rw [setIntegral_indicator measurableSet_Ici]
    have hs : Icc (0 : ℝ) D ∩ Ici m = Icc m D := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · exact fun h => ⟨h.2, h.1.2⟩
      · exact fun h => ⟨⟨hm.1.trans h.1, h.2⟩, h.1⟩
    rw [hs, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hm.2]
  have hFTC : (∫ t in m..D, F t) = F m / (2 * lam) - F D / (2 * lam) := by
    have hd (t : ℝ) : HasDerivAt (fun t => -(F t / (2 * lam))) (F t) t := by
      have h := (((((hasDerivAt_id t).sub_const l).const_mul (-lam)).exp.mul
        ((((hasDerivAt_id t).sub_const r).const_mul (-lam)).exp)).div_const (2 * lam)).neg
      dsimp only [F, Pi.neg_apply, Pi.mul_apply, id_eq] at h ⊢
      convert h using 1 <;> field_simp [hlam] <;> ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hc.intervalIntegrable m D)
    linarith
  have hmax : 2 * m - l - r = |l - r| := by
    rcases le_total l r with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      dsimp [m]
      rw [max_eq_right h]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      dsimp [m]
      rw [max_eq_left h]
      ring
  have hFm : F m = Real.exp (-lam * |l - r|) := by
    dsimp [F]
    rw [← Real.exp_add, ← hmax]
    congr 1
    ring
  rw [he]
  refine ⟨hc.integrableOn_Icc.indicator measurableSet_Ici, ?_⟩
  rw [hint, hFTC, ← hFm]
  dsimp [F]
  field_simp [hlam]
  <;> ring

private lemma causal_gram (lam D : ℝ) (hlam : lam ≠ 0)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) :
    IntegrableOn (fun t => ‖response lam x a t‖ ^ 2) (Icc 0 D) ∧
      (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)).re =
        2 * lam * (∫ t in Icc 0 D, ‖response lam x a t‖ ^ 2) +
          ‖response lam x a D‖ ^ 2 := by
  classical
  let p (i : I) (t : ℝ) : ℝ := if x i ≤ t then Real.exp (-lam * (t - x i)) else 0
  let f (i j : I) (t : ℝ) : ℂ := star (a i) * a j * ((p i t * p j t : ℝ) : ℂ)
  have hi (i j : I) : IntegrableOn (f i j) (Icc 0 D) :=
    ((causal_pair lam D (x i) (x j) hlam (hx i) (hx j)).1.ofReal).const_mul _
  have hs (t : ℝ) : ((‖response lam x a t‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, f i j t := by
    have he : response lam x a t = ∑ i, a i * (p i t : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases ht : x i ≤ t <;> simp [p, ht]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    change star (response lam x a t) * response lam x a t = _
    simp only [he, star_sum]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [f, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  have hsq : IntegrableOn (fun t => ‖response lam x a t‖ ^ 2) (Icc 0 D) := by
    have h : IntegrableOn (fun t => ∑ i, ∑ j, f i j t) (Icc 0 D) :=
      integrable_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hi i j))
    have h' := h.congr (ae_of_all _ (fun t => (hs t).symm))
    simpa only [RCLike.re_eq_complex_re, ← Complex.ofReal_pow, Complex.ofReal_re] using! h'.re
  have hint : ((∫ t in Icc 0 D, ‖response lam x a t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, star (a i) * a j * ((∫ t in Icc 0 D, p i t * p j t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hs]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    simp only [f, integral_const_mul, integral_complex_ofReal]
  have hp (i j : I) : (Real.exp (-lam * |x i - x j|) : ℂ) =
      (2 * lam : ℂ) * ((∫ t in Icc 0 D, p i t * p j t : ℝ) : ℂ) +
        (p i D : ℂ) * (p j D : ℂ) := by
    have h := congrArg Complex.ofReal
      (causal_pair lam D (x i) (x j) hlam (hx i) (hx j)).2
    simpa only [p, ite_eq_left (hx i).2, ite_eq_left (hx j).2, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat] using h.symm
  have hid : (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)) =
      (2 * lam : ℂ) * ((∫ t in Icc 0 D, ‖response lam x a t‖ ^ 2 : ℝ) : ℂ) +
        ((‖response lam x a D‖ ^ 2 : ℝ) : ℂ) := by
    rw [hint, hs D]
    simp_rw [hp]
    simp only [f, Complex.ofReal_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨hsq, ?_⟩
  simpa only [← Complex.ofReal_pow, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    mul_zero, zero_mul, add_zero, sub_zero] using congrArg Complex.re hid

/-- The finite-interval analytic bridge, with both nonnegative error terms
explicit. Every integral and endpoint is derived from the actual atoms. -/
private lemma primitive_exponential_identity (lam D : ℝ) (hlam : lam ≠ 0)
    (hD : 0 ≤ D) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0)
    (hfirst : ∑ i, a i * (x i : ℂ) = 0) :
    (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)).re =
      2 * lam * (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) -
      2 * lam ^ 3 * (∫ t in Icc 0 D, ‖∫ s in (0 : ℝ)..t, «prefix» x a s‖ ^ 2) +
      2 * lam ^ 5 * (∫ t in Icc 0 D, ‖secondResolvent lam x a t‖ ^ 2) +
      lam ^ 4 * ‖secondResolvent lam x a D‖ ^ 2 := by
  let A := «prefix» x a
  let B := ramp x a
  let g := resolvent lam x a
  let h := secondResolvent lam x a
  let Z := response lam x a
  let EA := ∫ t in Icc 0 D, ‖A t‖ ^ 2
  let EB := ∫ t in Icc 0 D, ‖B t‖ ^ 2
  let Eg := ∫ t in Icc 0 D, ‖g t‖ ^ 2
  let Eh := ∫ t in Icc 0 D, ‖h t‖ ^ 2
  let J := ∫ t in Icc 0 D, (star (g t) * A t).re
  let L := ∫ t in Icc 0 D, (star (h t) * g t).re
  have hg := resolvent_continuous lam x a
  have hh := second_continuous lam x a
  have hB := ramp_continuous x a
  have hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) (Icc 0 D) := (hg.norm.pow 2).integrableOn_Icc
  have hh2 : IntegrableOn (fun t => ‖h t‖ ^ 2) (Icc 0 D) := (hh.norm.pow 2).integrableOn_Icc
  have hA2 : IntegrableOn (fun t => ‖A t‖ ^ 2) (Icc 0 D) :=
    (shifted_hinge_prefix_energy x a ha 0).2.1.integrableOn
  have hJ : IntegrableOn (fun t => (star (g t) * A t).re) (Icc 0 D) := by
    have hf := prefix_mul_integrable x a D (fun t => star (g t)) (by fun_prop)
    exact (hf.congr (ae_of_all _ (fun t => mul_comm _ _))).re
  have hL : IntegrableOn (fun t => (star (h t) * g t).re) (Icc 0 D) :=
    (by fun_prop : Continuous (fun t => (star (h t) * g t).re)).integrableOn_Icc
  have hzero : B 0 = 0 ∧ g 0 = 0 ∧ h 0 = 0 :=
    initial_values lam x a (fun i => (hx i).1)
  have hBD : B D = 0 := ramp_terminal x a D (fun i => (hx i).2) ha hfirst
  have hZ (t : ℝ) : Z t = A t - (lam : ℂ) * g t := response_eq lam hlam x a t
  have hBg (t : ℝ) : B t - (lam : ℂ) * h t = g t := by
    dsimp [B, g, h, secondResolvent]
    field_simp [Complex.ofReal_ne_zero.mpr hlam]
    <;> ring
  have hgD : g D = -(lam : ℂ) * h D := by rw [← hBg D, hBD]; ring
  have hgD2 : ‖g D‖ ^ 2 = lam ^ 2 * ‖h D‖ ^ 2 := by
    rw [hgD, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs]
  have hgFTC : ‖g D‖ ^ 2 = 2 * J - 2 * lam * Eg := by
    have hi : IntegrableOn (fun t => (star (g t) * Z t).re) (Icc 0 D) := by
      have he (t : ℝ) : (star (g t) * Z t).re =
          (star (g t) * A t).re - lam * ‖g t‖ ^ 2 := by
        rw [hZ]
        simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.star_def,
          Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      exact (hJ.sub (hg2.const_mul lam)).congr (ae_of_all _ (fun t => (he t).symm))
    have hf := square_FTC D hD g Z hg (resolvent_right lam hlam x a) hi
    have he (t : ℝ) : (star (g t) * Z t).re =
        (star (g t) * A t).re - lam * ‖g t‖ ^ 2 := by
      rw [hZ]
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.star_def,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp_rw [he] at hf
    rw [integral_sub hJ (hg2.const_mul lam), integral_const_mul, hzero.2.1] at hf
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_sub, mul_assoc] using hf
  have hhFTC : ‖h D‖ ^ 2 = 2 * L := by
    have hf := square_FTC D hD h g hh (second_right lam hlam x a) hL
    rw [hzero.2.2] at hf
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using hf
  have hEZ : (∫ t in Icc 0 D, ‖Z t‖ ^ 2) = EA - 2 * lam * J + lam ^ 2 * Eg := by
    simp_rw [hZ, square_sub]
    change (∫ t in Icc 0 D, ((fun t => ‖A t‖ ^ 2) -
      (fun t => 2 * lam * (star (g t) * A t).re)) t + lam ^ 2 * ‖g t‖ ^ 2) = _
    rw [integral_add (hA2.sub (hJ.const_mul (2 * lam))) (hg2.const_mul (lam ^ 2))]
    simp only [Pi.sub_apply]
    rw [integral_sub hA2 (hJ.const_mul (2 * lam)), integral_const_mul, integral_const_mul]
  have hEB : EB = Eg + 2 * lam * L + lam ^ 2 * Eh := by
    have he (t : ℝ) : ‖B t‖ ^ 2 = ‖g t‖ ^ 2 +
        2 * lam * (star (h t) * g t).re + lam ^ 2 * ‖h t‖ ^ 2 := by
      have hb : B t = g t - ((-lam : ℝ) : ℂ) * h t := by
        have := hBg t
        push_cast
        linear_combination this
      rw [hb, square_sub]
      ring
    dsimp only [EB]
    simp_rw [he]
    change (∫ t in Icc 0 D, ((fun t => ‖g t‖ ^ 2) +
      (fun t => 2 * lam * (star (h t) * g t).re)) t + lam ^ 2 * ‖h t‖ ^ 2) = _
    rw [integral_add (hg2.add (hL.const_mul (2 * lam))) (hh2.const_mul (lam ^ 2))]
    simp only [Pi.add_apply]
    rw [integral_add hg2 (hL.const_mul (2 * lam)), integral_const_mul, integral_const_mul]
  have hZD : ‖Z D‖ ^ 2 = lam ^ 2 * ‖g D‖ ^ 2 := by
    rw [hZ, show A D = 0 from prefix_above x a ha D (fun i => (hx i).2),
      zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hgram := (causal_gram lam D hlam x a hx).2
  rw [hEZ, hZD] at hgram
  have hprim : (∫ t in Icc 0 D, ‖∫ s in (0 : ℝ)..t, «prefix» x a s‖ ^ 2) = EB := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change ‖∫ s in (0 : ℝ)..t, «prefix» x a s‖ ^ 2 = ‖ramp x a t‖ ^ 2
    rw [← ramp_is_primitive x a t (fun i => (hx i).1) ht.1]
  rw [prefix_energy_window x a D hx ha, hprim]
  change _ = 2 * lam * EA - 2 * lam ^ 3 * EB + 2 * lam ^ 5 * Eh + lam ^ 4 * ‖h D‖ ^ 2
  linear_combination hgram + 2 * lam ^ 2 * hgFTC + 2 * lam ^ 3 * hEB -
    2 * lam ^ 4 * hhFTC - lam ^ 2 * hgD2

/-- Literal real part of the existing complex atomic-prefix identity. -/
private lemma atomic_energy_real (lam D : ℝ) (hlam : 0 < lam) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (hdiam : ∀ i j, |x i - x j| ≤ D) :
    (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)).re =
      2 * lam * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) - lam ^ 2 *
        (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) *
          (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v)).re := by
  have hc : (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)) =
      ((2 * lam * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) : ℝ) : ℂ) -
        ((lam ^ 2 : ℝ) : ℂ) *
        (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) *
          (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v)) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat] using
      (exponential_prefix_energy x a ha lam D hlam hD hdiam).2.2.2.2
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using congrArg Complex.re hc

/-- The live primitive-to-exponential correlation bound. The weighted
correlation is exactly the public AtomicPrefixEnergy correlation, on its
actual finite window. No positivity supplier is assumed. -/
private lemma primitive_correlation_bound (lam D : ℝ) (hlam : 0 < lam)
    (hD : 0 ≤ D) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0)
    (hfirst : ∑ i, a i * (x i : ℂ) = 0) :
    (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) *
      (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v)).re ≤
      2 * lam * (∫ t in Icc 0 D, ‖∫ v in (0 : ℝ)..t, «prefix» x a v‖ ^ 2) := by
  have hdiam (i j : I) : |x i - x j| ≤ D :=
    abs_le.mpr ⟨by linarith [(hx i).1, (hx j).2], by linarith [(hx i).2, (hx j).1]⟩
  have hreal := atomic_energy_real lam D hlam hD x a ha hdiam
  have hnew := primitive_exponential_identity lam D hlam.ne' hD x a hx ha hfirst
  have hrem : 0 ≤ 2 * lam ^ 5 *
      (∫ t in Icc 0 D, ‖secondResolvent lam x a t‖ ^ 2) +
      lam ^ 4 * ‖secondResolvent lam x a D‖ ^ 2 := by
    exact add_nonneg (mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_nonneg (by positivity) (sq_nonneg _))
  have hscaled : lam ^ 2 *
      (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) *
        (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v)).re ≤
      lam ^ 2 * (2 * lam *
        (∫ t in Icc 0 D, ‖∫ v in (0 : ℝ)..t, «prefix» x a v‖ ^ 2)) := by
    nlinarith only [hreal, hnew, hrem]
  exact le_of_mul_le_mul_left hscaled (sq_pos_of_pos hlam)

/-- Atomic moments through q give the exact explicit moment-sensitive
exponential prefix lower bound, uniformly over arbitrary finite complex
families. There is no integrability, distinctness or nonzero-energy premise. -/
theorem moment_exponential_prefix_coercivity
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (hlam : 0 < lam)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    2 * lam * (1 - lam ^ 2 * D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) *
        (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) ≤
      (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)).re := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have hfirst : ∑ i, a i * (x i : ℂ) = 0 := by simpa using hm 1 hq
  have hprim := D5.S3.Analytic.MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap
    D hD q hq («prefix» x a) (prefix_memLp x a D ha) (prefix_moments x a D hx q hm)
  rw [← prefix_energy_window x a D hx ha] at hprim
  have hc := primitive_correlation_bound lam D hlam hD.le x a hx ha hfirst
  have hdiam (i j : I) : |x i - x j| ≤ D :=
    abs_le.mpr ⟨by linarith [(hx i).1, (hx j).2], by linarith [(hx i).2, (hx j).1]⟩
  have hid := atomic_energy_real lam D hlam hD.le x a ha hdiam
  have hupper := mul_le_mul_of_nonneg_left hprim (by positivity : 0 ≤ 2 * lam)
  have h := sub_le_sub_left
    (mul_le_mul_of_nonneg_left (hc.trans hupper) (sq_nonneg lam))
    (2 * lam * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2))
  rw [← hid] at h
  convert h using 1 <;> ring


/- Consumed owner-local exports for the full actual-kernel certificate.
The historic endpoint above remains a reuse supplier. These are source
attempts only; no new standalone admission is requested. -/

/-- Literal causal-square realization of the exponential deficit. Only
zero mass is used: no first moment, spectral measure or PSD premise. -/
theorem causal_prefix_deficit (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) :
    (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) -
      (∑ i, ∑ j, star (a i) * a j *
        (Real.exp (-|x i - x j| / 2) : ℂ)).re =
    (1 / 4) * ((∫ t in Icc (0 : ℝ) D, ‖resolvent (1 / 2) x a t‖ ^ 2) +
      ‖resolvent (1 / 2) x a D‖ ^ 2) := by
  let g := resolvent (1 / 2) x a
  let A := «prefix» x a
  let J := ∫ t in Icc (0 : ℝ) D, (star (g t) * A t).re
  let Eg := ∫ t in Icc (0 : ℝ) D, ‖g t‖ ^ 2
  have hg : Continuous g := resolvent_continuous _ x a
  have hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) (Icc 0 D) :=
    (hg.norm.pow 2).integrableOn_Icc
  have hA2 := (shifted_hinge_prefix_energy x a ha 0).2.1.integrableOn (s := Icc 0 D)
  have hJ : IntegrableOn (fun t => (star (g t) * A t).re) (Icc 0 D) := by
    have hi := prefix_mul_integrable x a D (fun t => star (g t)) (by fun_prop)
    exact (hi.congr (ae_of_all _ (fun _ => mul_comm _ _))).re
  have he (t : ℝ) : (star (g t) * response (1 / 2) x a t).re =
      (star (g t) * A t).re - ‖g t‖ ^ 2 / 2 := by
    rw [response_eq (1 / 2) (by norm_num)]
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.star_def, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hs := square_FTC D hD g (response (1 / 2) x a) hg
    (resolvent_right (1 / 2) (by norm_num) x a)
    ((hJ.sub (hg2.div_const 2)).congr (ae_of_all _ (fun t => (he t).symm)))
  simp_rw [he] at hs
  have hg0 : g 0 = 0 := (initial_values (1 / 2) x a (fun i => (hx i).1)).2.1
  rw [integral_sub hJ (hg2.div_const 2), integral_div, hg0] at hs
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hs
  have hresponse (t : ℝ) : ‖response (1 / 2) x a t‖ ^ 2 =
      ‖A t‖ ^ 2 - (star (g t) * A t).re + ‖g t‖ ^ 2 / 4 := by
    rw [response_eq (1 / 2) (by norm_num), square_sub]
    ring
  have hDresponse : ‖response (1 / 2) x a D‖ ^ 2 = ‖g D‖ ^ 2 / 4 := by
    rw [response_eq (1 / 2) (by norm_num),
      prefix_above x a ha D (fun i => (hx i).2), zero_sub, norm_neg,
      norm_mul, Complex.norm_real]
    norm_num
    ring
  have hc := (causal_gram (1 / 2) D (by norm_num) x a hx).2
  simp_rw [hresponse] at hc
  rw [integral_add (hA2.sub hJ) (hg2.div_const 4), integral_sub hA2 hJ,
    integral_div, hDresponse] at hc
  rw [prefix_energy_window x a D hx ha]
  have heq (t : ℝ) : -(1 / 2 : ℝ) * |t| = -|t| / 2 := by ring
  simp_rw [heq] at hc
  dsimp only [J, Eg] at *
  linarith only [hc, hs]

/-- Exact nonnegative deficit, consumed by the translated causal-square
argument for the original resolvent. -/
theorem exponential_prefix_deficit_nonneg (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) :
    0 ≤ (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) -
      (∑ i, ∑ j, star (a i) * a j *
        (Real.exp (-|x i - x j| / 2) : ℂ)).re := by
  rw [causal_prefix_deficit D hD x a hx ha]
  exact mul_nonneg (by norm_num)
    (add_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg _))

/-- The actual primitive payment from the retained complex moment gap.
Atomic degrees 0,...,q pay prefix degrees 0,...,q-1. -/
theorem actual_prefix_primitive_gap (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (∫ t in Icc (0 : ℝ) D, ‖ramp x a t‖ ^ 2) ≤
      D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) *
        (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have h := D5.S3.Analytic.MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap
    D hD q hq («prefix» x a) (prefix_memLp x a D ha) (prefix_moments x a D hx q hm)
  rw [← prefix_energy_window x a D hx ha] at h
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  change ‖ramp x a t‖ ^ 2 = ‖∫ u in (0 : ℝ)..t, «prefix» x a u‖ ^ 2
  rw [ramp_is_primitive x a t (fun i => (hx i).1) ht.1]


/-- The literal growing-kernel primitive identity, in causal triangular
form. Both endpoint cancellations are paid by the mass and first atomic
moment. The generalized finite Gram identity is used at lambda=-1/2;
no positivity of the growing exponential is asserted. -/
theorem growing_primitive_identity (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (hfirst : ∑ i, a i * (x i : ℂ) = 0) :
    let G : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, «prefix» x a u
    let h : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t,
      (Real.exp ((t - u) / 2) : ℂ) * G u
    G 0 = 0 ∧ G D = 0 ∧
      (∑ i, ∑ j, star (a i) * a j * (Real.exp (|x i - x j| / 2) : ℂ)).re =
        -(∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) +
        (1 / 4) * (∫ t in Icc (0 : ℝ) D, ‖G t‖ ^ 2) +
        (1 / 16) * (2 * ∫ t in Icc (0 : ℝ) D, (star (G t) * h t).re) := by
  dsimp only
  let G : ℝ → ℂ := ramp x a
  let h : ℝ → ℂ := secondResolvent (-1 / 2) x a
  let g : ℝ → ℂ := resolvent (-1 / 2) x a
  have hG : Continuous G := ramp_continuous x a
  have hh : Continuous h := second_continuous _ x a
  have hzero := initial_values (-1 / 2) x a (fun i => (hx i).1)
  have hGD : G D = 0 := ramp_terminal x a D (fun i => (hx i).2) ha hfirst
  have hprimitive (t : ℝ) (ht : 0 ≤ t) :
      G t = ∫ u in (0 : ℝ)..t, «prefix» x a u :=
    ramp_is_primitive x a t (fun i => (hx i).1) ht
  have hderiv (t : ℝ) : HasDerivWithinAt h (g t) (Ioi t) t :=
    second_right (-1 / 2) (by norm_num) x a t
  have hg (t : ℝ) : g t = G t + (1 / 2 : ℂ) * h t := by
    dsimp [g, G, h, secondResolvent]
    norm_num
    ring
  have hintegrating (t : ℝ) : HasDerivWithinAt
      (fun v => (Real.exp (-v / 2) : ℂ) * h v)
      ((Real.exp (-t / 2) : ℂ) * G t) (Ioi t) t := by
    have hd := (((((hasDerivAt_id t).neg.div_const 2).exp).ofReal_comp).hasDerivWithinAt
      (s := Ioi t)).mul (hderiv t)
    apply hd.congr_deriv
    rw [hg]
    simp only [Pi.neg_apply, id_eq, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hconvolution (t : ℝ) (ht : 0 ≤ t) :
      h t = ∫ u in (0 : ℝ)..t, (Real.exp ((t - u) / 2) : ℂ) * G u := by
    have hc : Continuous (fun u : ℝ => (Real.exp (-u / 2) : ℂ)) := by fun_prop
    have hi : IntervalIntegrable (fun u => (Real.exp (-u / 2) : ℂ) * G u) volume 0 t :=
      (hc.mul hG).intervalIntegrable 0 t
    have hf := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
      ((hc.mul hh).continuousOn) (fun u _ => hintegrating u) hi
    have hh0 : h 0 = 0 := hzero.2.2
    simp only [Pi.mul_apply] at hf
    rw [hh0, mul_zero, sub_zero] at hf
    have hexp : (Real.exp (t / 2) : ℂ) * (Real.exp (-t / 2) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp
    calc
      h t = (Real.exp (t / 2) : ℂ) *
          ((Real.exp (-t / 2) : ℂ) * h t) := by rw [← mul_assoc, hexp, one_mul]
      _ = (Real.exp (t / 2) : ℂ) *
          ∫ u in (0 : ℝ)..t, (Real.exp (-u / 2) : ℂ) * G u := by rw [hf]
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro u _
        rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
        congr 2
        ring
  have hJ : IntegrableOn (fun t => (star (h t) * G t).re) (Icc 0 D) :=
    (Complex.continuous_re.comp (hh.star.mul hG)).integrableOn_Icc
  have hh2 : IntegrableOn (fun t => ‖h t‖ ^ 2) (Icc 0 D) :=
    (hh.norm.pow 2).integrableOn_Icc
  have he (t : ℝ) : (star (h t) * g t).re =
      (star (h t) * G t).re + ‖h t‖ ^ 2 / 2 := by
    rw [hg]
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.star_def, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
    ring
  have hFTC := square_FTC D hD h g hh hderiv
    ((hJ.add (hh2.div_const 2)).congr (ae_of_all _ (fun t => (he t).symm)))
  simp_rw [he] at hFTC
  have hh0 : h 0 = 0 := hzero.2.2
  rw [integral_add hJ (hh2.div_const 2), integral_div, hh0] at hFTC
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hFTC
  have hid := primitive_exponential_identity (-1 / 2) D (by norm_num) hD x a hx ha hfirst
  have hGint : (∫ t in Icc (0 : ℝ) D,
      ‖∫ u in (0 : ℝ)..t, «prefix» x a u‖ ^ 2) =
        ∫ t in Icc (0 : ℝ) D, ‖G t‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [← hprimitive t ht.1]
  have hJint : (∫ t in Icc (0 : ℝ) D,
      (star (∫ u in (0 : ℝ)..t, «prefix» x a u) *
        (∫ u in (0 : ℝ)..t, (Real.exp ((t - u) / 2) : ℂ) *
          (∫ v in (0 : ℝ)..u, «prefix» x a v))).re) =
      ∫ t in Icc (0 : ℝ) D, (star (h t) * G t).re := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [← hprimitive t ht.1]
    have hinner : (∫ u in (0 : ℝ)..t, (Real.exp ((t - u) / 2) : ℂ) *
        (∫ v in (0 : ℝ)..u, «prefix» x a v)) = h t := by
      rw [hconvolution t ht.1]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      rw [← hprimitive u hu.1]
    rw [hinner]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  refine ⟨by simp, ?_, ?_⟩
  · rw [← hprimitive D hD, hGD]
  · rw [hGint, hJint]
    have he (t : ℝ) : -(-1 / 2 : ℝ) * |t| = |t| / 2 := by ring
    simp_rw [he] at hid
    change _ = -(∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) +
      (1 / 4) * (∫ t in Icc (0 : ℝ) D, ‖G t‖ ^ 2) +
      (1 / 16) * (2 * ∫ t in Icc (0 : ℝ) D, (star (h t) * G t).re)
    dsimp only [h] at hFTC ⊢
    norm_num at hid
    linarith only [hid, hFTC]


/-- Reuse of the owner's actual right-FTC primitive, with the original
inclusive prefix. This export is consumed only by the continuum payment. -/
theorem actual_prefix_primitive_realization (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, 0 ≤ x i) (t : ℝ) (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, «prefix» x a u) =
      ∑ i, a i * (max (t - x i) 0 : ℝ) :=
  (ramp_is_primitive x a t hx ht).symm

end D5.S3.Analytic.Interpolation.MomentExponentialCoercivity
