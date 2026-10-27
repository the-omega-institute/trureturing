import D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck
import Mathlib.Analysis.Calculus.Deriv.Abs
/- Uncompiled E source: ordinary convolution regularity across one even cusp.
   No derivative of the convolution is an input.  The jump is paid by an
   ordinary cumulative integral, not by silently differentiating through 0.
   This source has not been submitted to Lean/kernel verification. -/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

noncomputable section

namespace RhTransient.EvenCuspConvolutionC2

open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff

/-- The orientation used by `convolution_mul_swap`. -/
def mulConv (f b : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, f (x - y) * b y

def lowerPrimitive (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Iic x, b y

def rightStep (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

private theorem mulConv_integrable {f b : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ M)
    (hb : Integrable b) (x : ℝ) :
    Integrable (fun y : ℝ => f (x - y) * b y) := by
  exact hb.bdd_mul
    (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (Eventually.of_forall fun y => hbound (x - y))

/-- A moving single cusp is harmless for the *first* derivative: at each
fixed x the exceptional integration point is just y=x. -/
theorem hasDerivAt_mulConv_of_lipschitz
    {f p b : ℝ → ℝ} {K : ℝ≥0} {M : ℝ}
    (hf : LipschitzWith K f) (hfbound : ∀ x, ‖f x‖ ≤ M)
    (hp : Measurable p)
    (hfd : ∀ z : ℝ, z ≠ 0 → HasDerivAt f (p z) z)
    (hb : Integrable b) (x : ℝ) :
    Integrable (fun y : ℝ => p (x - y) * b y) ∧
      HasDerivAt (mulConv f b) (mulConv p b x) x := by
  have hlip (y : ℝ) :
      LipschitzOnWith (Real.nnabs ((K : ℝ) * ‖b y‖))
        (fun u : ℝ => f (u - y) * b y) univ := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v _
    change dist (f (u - y) * b y) (f (v - y) * b y) ≤
      |(K : ℝ) * ‖b y‖| * dist u v
    have hshift : dist (u - y) (v - y) = dist u v := by
      simp only [dist_eq_norm]
      congr 1
      ring
    calc
      dist (f (u - y) * b y) (f (v - y) * b y) =
          dist (f (u - y)) (f (v - y)) * ‖b y‖ := by
        simp only [dist_eq_norm, ← sub_mul, norm_mul]
      _ ≤ ((K : ℝ) * dist (u - y) (v - y)) * ‖b y‖ :=
        mul_le_mul_of_nonneg_right (hf.dist_le_mul _ _) (norm_nonneg _)
      _ = ((K : ℝ) * ‖b y‖) * dist u v := by rw [hshift]; ring
      _ ≤ |(K : ℝ) * ‖b y‖| * dist u v :=
        mul_le_mul_of_nonneg_right (le_abs_self _) dist_nonneg
  have hdiff : ∀ᵐ y : ℝ, HasDerivAt
      (fun u : ℝ => f (u - y) * b y) (p (x - y) * b y) x := by
    filter_upwards [volume.ae_ne x] with y hy
    have hxy : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    simpa only [Function.comp_def, id_eq, mul_one] using!
      ((hfd (x - y) hxy).comp x
        ((hasDerivAt_id x).sub_const y)).mul_const (b y)
  simpa only [mulConv] using!
    (hasDerivAt_integral_of_dominated_loc_of_lip
      (μ := volume) (F := fun u y : ℝ => f (u - y) * b y)
      (F' := fun y : ℝ => p (x - y) * b y)
      (bound := fun y : ℝ => (K : ℝ) * ‖b y‖)
      (s := univ) (x₀ := x) (by simp)
      (Eventually.of_forall fun u =>
        ((hf.continuous.measurable.comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
            hb.aestronglyMeasurable))
      (mulConv_integrable hf.continuous.measurable hfbound hb x)
      ((hp.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
        hb.aestronglyMeasurable)
      (Eventually.of_forall hlip) (hb.norm.const_mul (K : ℝ)) hdiff)

theorem continuous_mulConv_of_bounded
    {r b : ℝ → ℝ} {M : ℝ}
    (hr : Continuous r) (hrbound : ∀ x, ‖r x‖ ≤ M)
    (hb : Integrable b) : Continuous (mulConv r b) := by
  unfold mulConv
  refine continuous_of_dominated (bound := fun y : ℝ => M * ‖b y‖)
    (fun x => ((hr.measurable.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
        hb.aestronglyMeasurable))
    (fun x => Eventually.of_forall fun y => ?_) (hb.norm.const_mul M)
    (Eventually.of_forall fun y =>
      (hr.comp (continuous_id.sub continuous_const)).mul continuous_const)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hrbound (x - y)) (norm_nonneg _)

/-- The source of the jump term: the lower cumulative integral has its
ordinary derivative at every point of continuity of the L1 density. -/
theorem lowerPrimitive_hasDerivAt {b : ℝ → ℝ}
    (hb : Integrable b) (hbc : Continuous b) (x : ℝ) :
    HasDerivAt (lowerPrimitive b) (b x) x := by
  have heq : lowerPrimitive b =
      fun u : ℝ => lowerPrimitive b 0 + ∫ y in (0 : ℝ)..u, b y := by
    funext u
    have h := intervalIntegral.integral_Iic_sub_Iic
      (f := b) (a := (0 : ℝ)) (b := u) hb.integrableOn hb.integrableOn
    dsimp only [lowerPrimitive]
    linarith
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (hb.intervalIntegrable : IntervalIntegrable b volume 0 x)
    hbc.aestronglyMeasurable.stronglyMeasurableAtFilter
    hbc.continuousAt).const_add (lowerPrimitive b 0)

/-- An exact integral identity.  Both summands are genuinely integrable. -/
theorem mulConv_split_step {p p0 b : ℝ → ℝ} {c M : ℝ}
    (hp0 : Measurable p0) (hp0bound : ∀ x, ‖p0 x‖ ≤ M)
    (hsplit : ∀ x, p x = p0 x + (2 * c) * rightStep x)
    (hb : Integrable b) (x : ℝ) :
    mulConv p b x = mulConv p0 b x + (2 * c) * lowerPrimitive b x := by
  have h0int := mulConv_integrable hp0 hp0bound hb x
  have h1int := (hb.indicator (s := Iic x) measurableSet_Iic).const_mul (2 * c)
  calc
    mulConv p b x =
        ∫ y : ℝ, p0 (x - y) * b y +
          (2 * c) * (Iic x).indicator b y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hsplit (x - y)]
      change (p0 (x - y) + (2 * c) * (if 0 ≤ x - y then (1 : ℝ) else 0)) * b y =
        p0 (x - y) * b y + (2 * c) * (if y ≤ x then b y else 0)
      by_cases hy : y ≤ x
      · simp only [if_pos (sub_nonneg.mpr hy), if_pos hy, mul_one]
        ring
      · have hxy : ¬0 ≤ x - y := by simpa only [sub_nonneg] using hy
        simp only [if_neg hxy, if_neg hy, mul_zero, add_zero]
    _ = mulConv p0 b x + (2 * c) * lowerPrimitive b x := by
      rw [integral_add h0int h1int, integral_const_mul,
        integral_indicator measurableSet_Iic]
      rfl

/-- Ordinary C2 from bounded source jets with one explicit jump.

For an even cusp f(x)=h(|x|), put c=h'(0), r(x)=h''(|x|),
p(x)=h'(x) on x>=0 and -h'(-x) on x<0, and
p0(x)=-c+integral_0^x r.  Half-line FTC supplies exactly `hsplit` and
`hp0d`.  Neither f nor p is assumed differentiable at the cusp.

For b=involution(g), this proves the requested jump formula with b(x).
The inputs concern only f and its scalar source jets, never a derivative
or regularity property of the target convolution. -/
theorem evenCusp_mulConv_C2
    {f p p0 r b : ℝ → ℝ} {K1 K2 : ℝ≥0} {M0 M1 c : ℝ}
    (hf : LipschitzWith K1 f) (hfbound : ∀ x, ‖f x‖ ≤ M0)
    (hp : Measurable p)
    (hfd : ∀ z : ℝ, z ≠ 0 → HasDerivAt f (p z) z)
    (hp0bound : ∀ x, ‖p0 x‖ ≤ M1)
    (hp0d : ∀ x, HasDerivAt p0 (r x) x)
    (hr : Continuous r) (hrbound : ∀ x, ‖r x‖₊ ≤ K2)
    (hsplit : ∀ x, p x = p0 x + (2 * c) * rightStep x)
    (hb : Integrable b) (hbc : Continuous b) :
    ContDiff ℝ 2 (mulConv f b) ∧
      deriv (mulConv f b) = mulConv p b ∧
      ∀ x, deriv (deriv (mulConv f b)) x =
        mulConv r b x + 2 * c * b x := by
  have hp0diff : Differentiable ℝ p0 := fun x => (hp0d x).differentiableAt
  have hp0lip : LipschitzWith K2 p0 :=
    lipschitzWith_of_nnnorm_deriv_le hp0diff (fun x => by
      rw [(hp0d x).deriv]
      exact hrbound x)
  have hk (x : ℝ) :=
    (hasDerivAt_mulConv_of_lipschitz hf hfbound hp hfd hb x).2
  have hkeq : deriv (mulConv f b) = mulConv p b :=
    funext fun x => (hk x).deriv
  have hpd (x : ℝ) : HasDerivAt (mulConv p b)
      (mulConv r b x + (2 * c) * b x) x := by
    have h0 := (hasDerivAt_mulConv_of_lipschitz hp0lip hp0bound
      hr.measurable (fun z _ => hp0d z) hb x).2
    have heq : mulConv p b = fun u : ℝ =>
        mulConv p0 b u + (2 * c) * lowerPrimitive b u :=
      funext fun u => mulConv_split_step hp0diff.continuous.measurable
        hp0bound hsplit hb u
    rw [heq]
    exact h0.add ((lowerPrimitive_hasDerivAt hb hbc x).const_mul (2 * c))
  have hrr : ∀ x, ‖r x‖ ≤ (K2 : ℝ) := fun x => by
    exact_mod_cast hrbound x
  have hsecond : Continuous (fun x : ℝ => mulConv r b x + (2 * c) * b x) :=
    (continuous_mulConv_of_bounded hr hrr hb).add (continuous_const.mul hbc)
  have hdeq : deriv (mulConv p b) =
      fun x : ℝ => mulConv r b x + (2 * c) * b x :=
    funext fun x => (hpd x).deriv
  have hpC1 : ContDiff ℝ 1 (mulConv p b) :=
    contDiff_one_iff_deriv.mpr
      ⟨fun x => (hpd x).differentiableAt, hdeq.symm ▸ hsecond⟩
  have hkC2 : ContDiff ℝ 2 (mulConv f b) := by
    rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hk x).differentiableAt, ?_, ?_⟩
    · simp
    · rw [hkeq]
      exact hpC1
  refine ⟨hkC2, hkeq, fun x => ?_⟩
  rw [hkeq]
  exact (hpd x).deriv

/- Exact half-line supplier skeleton, not an additional assumed result:

Assume h,h1,h2 continuous on [0,infinity), HasDerivWithinAt h (h1 t)
and HasDerivWithinAt h1 (h2 t) there, with uniform bounds M0,M1,M2.
Define f=h o abs, c=h1 0, r=h2 o abs,
  p x  = if 0<=x then h1 x else -h1 (-x),
  p0 x = -c + integral_(0..x) r.

1. Convex.Ici MVT bounds h by M1-Lipschitz on [0,infinity).
   Compose its distance inequality with abs_sub_abs_le_abs_sub to obtain
   global LipschitzWith M1 f.  HasDerivAt f (p z) z for z!=0 follows
   from hasDerivAt_abs_pos/neg and the half-line derivative at abs z>0.

2. Ordinary FTC gives HasDerivAt p0 (r x) x for every x, since r is
   continuous.  For x>=0, half-line FTC gives p0 x=h1 x-2*c.
   For x<0, integral_comp_neg plus integral_symm gives
   p0 x=-h1 (-x).  Thus hsplit holds INCLUDING x=0 and
   norm(p0 x)<=M1+2*abs(c).  This is the only boundary payment.

3. The theorem above applies to b x=g(-x).  Reflection preserves L1
   and continuity.  Its last equality is exactly
     k''(x)=(h2(abs(.))*involution(g))(x)+2*h1(0)*involution(g)(x).
   Bounded h,h1,h2 suffice for the C2 argument; any available weighted
   L1 bounds can subsequently be consumed by the displayed equality.
-/

end RhTransient.EvenCuspConvolutionC2


/- Source draft, not compiled. A consumed helper for the actual convolution
   cutoff construction, not a separate claimed content theorem. Existing
   translated_bound already leaves half an exponential of spare decay. -/

namespace D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft

open Real Set MeasureTheory Filter
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel

open private fullJet fullJet_continuous fullJet_eq_phi_derivative
  fullConstant translated_bound from
  D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck

theorem translated_phi_exp_one_integrable (r : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => Real.exp t * |iteratedDeriv r romikPhi (a + t)|)
      (Ioi 0) := by
  have hbound {t : ℝ} (ht : 0 ≤ t) :
      Real.exp t * |fullJet r (a + t)| ≤
        fullConstant r * Real.exp ((-1 / 2 : ℝ) * t) := by
    calc
      _ = Real.exp (t / 2) *
          (Real.exp (t / 2) * |fullJet r (a + t)|) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (t / 2) * (fullConstant r * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left (translated_bound r ha ht) (Real.exp_pos _).le
      _ = fullConstant r * (Real.exp (t / 2) * Real.exp (-t)) := by ring
      _ = fullConstant r * Real.exp ((-1 / 2 : ℝ) * t) := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hmajorant : IntegrableOn
      (fun t : ℝ => fullConstant r * Real.exp ((-1 / 2 : ℝ) * t)) (Ioi 0) := by
    exact (integrableOn_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0).const_mul _
  have hfull : IntegrableOn
      (fun t : ℝ => Real.exp t * |fullJet r (a + t)|) (Ioi 0) := by
    have hc : Continuous (fun t : ℝ => Real.exp t * |fullJet r (a + t)|) :=
      Real.continuous_exp.mul
        (((fullJet_continuous r).comp (continuous_const.add continuous_id)).abs)
    apply hmajorant.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound ht.le
  apply hfull.congr_fun ?_ measurableSet_Ioi
  intro t ht
  dsimp only
  have htpos : 0 < t := ht
  rw [fullJet_eq_phi_derivative r (by linarith : 0 < a + t)]

end D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft
/- UNCOMPILED E source. Append after EvenCuspConvolutionC2.fragment.lean.
   Add these imports to the combined module's initial import block:
     import Batteries.Tactic.OpenPrivate
     import D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck
     import Mathlib.Analysis.Calculus.Deriv.Abs
   This pays the actual source jets and applies the generic C2 result. -/

namespace RhTransient.ActualGaussianCuspSupplier

open MeasureTheory Set Filter Real
open scoped Topology NNReal ContDiff
open D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open RhTransient.EvenCuspConvolutionC2

open private fullJet fullJet_continuous fullJet_deriv fullJet_zero_eq_phi
  fullConstant fullConstant_nonneg translated_bound literalGaussian from
  D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck

private def jet (a : ℝ) (k : ℕ) (x : ℝ) : ℝ := fullJet k (a + x)
private def jetK (k : ℕ) : ℝ≥0 := ⟨fullConstant k, fullConstant_nonneg k⟩

def evenPhiJet (a : ℝ) (k : ℕ) (x : ℝ) : ℝ := jet a k |x|
def evenPhi (a : ℝ) : ℝ → ℝ := evenPhiJet a 0
private def cuspCharge (a : ℝ) : ℝ := jet a 1 0

private def firstJet (a x : ℝ) : ℝ :=
  if 0 ≤ x then jet a 1 x else -jet a 1 (-x)

private def correctedFirstJet (a x : ℝ) : ℝ :=
  if 0 ≤ x then jet a 1 x - 2 * cuspCharge a else -jet a 1 (-x)

private theorem jet_continuous (a : ℝ) (k : ℕ) : Continuous (jet a k) :=
  (fullJet_continuous k).comp (continuous_const.add continuous_id)

private theorem jet_deriv (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (jet a k) (jet a (k + 1) x) x := by
  simpa only [jet, Function.comp_def, id_eq, mul_one] using!
    (fullJet_deriv k (a + x)).comp x ((hasDerivAt_id x).const_add a)

private theorem jet_decay {a x : ℝ} (ha : 0 ≤ a) (k : ℕ) (hx : 0 ≤ x) :
    ‖jet a k x‖ ≤ fullConstant k * exp (-x) := by
  have he : 1 ≤ exp (x / 2) := one_le_exp (by positivity)
  calc
    _ = |fullJet k (a + x)| := Real.norm_eq_abs _
    _ ≤ exp (x / 2) * |fullJet k (a + x)| :=
      le_mul_of_one_le_left (abs_nonneg _) he
    _ ≤ _ := translated_bound k ha hx

private theorem jet_bound {a x : ℝ} (ha : 0 ≤ a) (k : ℕ) (hx : 0 ≤ x) :
    ‖jet a k x‖ ≤ fullConstant k :=
  (jet_decay ha k hx).trans (mul_le_of_le_one_right
    (fullConstant_nonneg k) (exp_le_one_iff.mpr (by linarith)))

theorem evenPhiJet_continuous (a : ℝ) (k : ℕ) : Continuous (evenPhiJet a k) :=
  (jet_continuous a k).comp continuous_abs

theorem evenPhi_neg (a x : ℝ) : evenPhi a (-x) = evenPhi a x := by
  simp only [evenPhi, evenPhiJet, abs_neg]

theorem evenPhi_eq_actualPhi {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    evenPhi a x =
      D5.S3.Analytic.Fourier.ThetaDifferentialKernel.romikPhi (a + |x|) :=
  fullJet_zero_eq_phi (add_nonneg ha (abs_nonneg x))

private theorem evenPhi_lipschitz {a : ℝ} (ha : 0 ≤ a) :
    LipschitzWith (jetK 1) (evenPhi a) := by
  have hlip : LipschitzOnWith (jetK 1) (jet a 0) (Ici 0) :=
    (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (jet_deriv a 0 x).hasDerivWithinAt)
      (fun x hx => by exact_mod_cast jet_bound ha 1 hx)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (evenPhi a x) (evenPhi a y) ≤
        (jetK 1 : ℝ) * dist |x| |y| :=
      hlip.dist_le_mul |x| (abs_nonneg x) |y| (abs_nonneg y)
    _ ≤ (jetK 1 : ℝ) * dist x y :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y)
        (jetK 1).2

private theorem firstJet_measurable (a : ℝ) : Measurable (firstJet a) := by
  exact Measurable.ite measurableSet_Ici (jet_continuous a 1).measurable
    (((jet_continuous a 1).comp continuous_neg).neg.measurable)

private theorem evenPhi_deriv_off_zero (a x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (evenPhi a) (firstJet a x) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · simpa only [evenPhi, evenPhiJet, firstJet, if_neg (not_le.mpr hneg),
      abs_of_neg hneg, mul_neg_one] using!
      (jet_deriv a 0 |x|).comp x (hasDerivAt_abs_neg hneg)
  · simpa only [evenPhi, evenPhiJet, firstJet, if_pos hpos.le,
      abs_of_pos hpos, mul_one] using!
      (jet_deriv a 0 |x|).comp x (hasDerivAt_abs_pos hpos)

private theorem correctedFirstJet_bound {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    ‖correctedFirstJet a x‖ ≤ fullConstant 1 + 2 * |cuspCharge a| := by
  by_cases hx : 0 ≤ x
  · rw [correctedFirstJet, if_pos hx]
    calc
      _ ≤ ‖jet a 1 x‖ + ‖2 * cuspCharge a‖ := norm_sub_le _ _
      _ ≤ fullConstant 1 + ‖2 * cuspCharge a‖ :=
        add_le_add (jet_bound ha 1 hx) le_rfl
      _ = _ := by
        congr 1
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  · rw [correctedFirstJet, if_neg hx, norm_neg]
    exact (jet_bound ha 1 (by linarith : 0 ≤ -x)).trans
      (le_add_of_nonneg_right (by positivity))

/-- The corrected first jet has no cusp: its values and ordinary derivatives
    match at 0. This directly pays the boundary, without a convolution premise. -/
private theorem correctedFirstJet_deriv (a x : ℝ) :
    HasDerivAt (correctedFirstJet a) (evenPhiJet a 2 x) x := by
  have hplus (u : ℝ) :
      HasDerivAt (fun t : ℝ => jet a 1 t - 2 * cuspCharge a) (jet a 2 u) u :=
    (jet_deriv a 1 u).sub_const _
  have hminus (u : ℝ) :
      HasDerivAt (fun t : ℝ => -jet a 1 (-t)) (jet a 2 (-u)) u := by
    simpa only [Function.comp_def, mul_neg_one, neg_neg] using!
      ((jet_deriv a 1 (-u)).comp u (hasDerivAt_neg u)).neg
  by_cases hx : x = 0
  · subst x
    have hvalue : correctedFirstJet a 0 = -jet a 1 (-(0 : ℝ)) := by
      simp only [correctedFirstJet, le_refl, if_pos, neg_zero, cuspCharge]
      ring
    have hl : HasDerivWithinAt (correctedFirstJet a) (jet a 2 0) (Iio 0) 0 := by
      have h := (hminus 0).hasDerivWithinAt (s := Iio 0)
      simp only [neg_zero] at h
      apply h.congr ?_ hvalue
      intro y hy
      have hy0 : y < 0 := hy
      simp only [correctedFirstJet, if_neg (not_le.mpr hy0)]
    have hr : HasDerivWithinAt (correctedFirstJet a) (jet a 2 0) (Ici 0) 0 := by
      apply (hplus 0).hasDerivWithinAt.congr_of_mem ?_ (by simp)
      intro y hy
      have hy0 : 0 ≤ y := hy
      simp only [correctedFirstJet, if_pos hy0]
    simpa only [Iio_union_Ici, hasDerivWithinAt_univ,
      evenPhiJet, abs_zero] using hl.union hr
  · rcases lt_or_gt_of_ne hx with hneg | hpos
    · rw [evenPhiJet, abs_of_neg hneg]
      apply (hminus x).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hneg] with y hy
      have hy0 : y < 0 := hy
      simp only [correctedFirstJet, if_neg (not_le.mpr hy0)]
    · rw [evenPhiJet, abs_of_pos hpos]
      apply (hplus x).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      have hy0 : 0 < y := hy
      simp only [correctedFirstJet, if_pos hy0.le]

private theorem firstJet_split (a x : ℝ) :
    firstJet a x = correctedFirstJet a x + (2 * cuspCharge a) * rightStep x := by
  by_cases hx : 0 ≤ x <;>
    simp only [firstJet, correctedFirstJet, rightStep, hx, if_true, if_false] <;> ring

/-- Actual translated Phi is an L1 function on the full line. Both half-line
    estimates follow from the accepted complete translated-jet bound. -/
theorem evenPhi_integrable {a : ℝ} (ha : 0 ≤ a) : Integrable (evenPhi a) := by
  have hc : Continuous (evenPhi a) := evenPhiJet_continuous a 0
  have hp : IntegrableOn (evenPhi a) (Ioi 0) := by
    have hm := (integrableOn_exp_mul_Ioi
      (show (-1 : ℝ) < 0 by norm_num) 0).const_mul (fullConstant 0)
    apply hm.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    simpa only [evenPhi, evenPhiJet, abs_of_pos hx0, neg_one_mul] using
      jet_decay ha 0 hx0.le
  have hn : IntegrableOn (evenPhi a) (Iic 0) := by
    have hm := (integrableOn_exp_mul_Iic
      (show (0 : ℝ) < 1 by norm_num) 0).const_mul (fullConstant 0)
    apply hm.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    have hx0 : x ≤ 0 := hx
    simpa only [evenPhi, evenPhiJet, abs_of_nonpos hx0, neg_neg, one_mul] using
      jet_decay ha 0 (neg_nonneg.mpr hx0)
  have h := integrableOn_union.mpr ⟨hn, hp⟩
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

/-- The generic C2 theorem is now consumed by actual complete theta jets.
    The coefficient 2*Phi'(a) is retained, including when a=0. -/
theorem evenPhi_mulConv_C2 {a : ℝ} (ha : 0 ≤ a)
    {b : ℝ → ℝ} (hb : Integrable b) (hbc : Continuous b) :
    ContDiff ℝ 2 (mulConv (evenPhi a) b) ∧
      ∀ x : ℝ, deriv (deriv (mulConv (evenPhi a) b)) x =
        mulConv (evenPhiJet a 2) b x + 2 * cuspCharge a * b x := by
  have h := evenCusp_mulConv_C2
    (K1 := jetK 1) (K2 := jetK 2) (c := cuspCharge a)
    (evenPhi_lipschitz ha)
    (fun x => jet_bound ha 0 (abs_nonneg x))
    (firstJet_measurable a) (evenPhi_deriv_off_zero a)
    (correctedFirstJet_bound ha) (correctedFirstJet_deriv a)
    (evenPhiJet_continuous a 2)
    (fun x => by exact_mod_cast jet_bound ha 2 (abs_nonneg x))
    (firstJet_split a) hb hbc
  exact ⟨h.1, h.2.2⟩

theorem evenPhi_autocorrelation_C2 {a : ℝ} (ha : 0 ≤ a) :
    ContDiff ℝ 2 (mulConv (evenPhi a) (evenPhi a)) ∧
      ∀ x : ℝ, deriv (deriv (mulConv (evenPhi a) (evenPhi a))) x =
        mulConv (evenPhiJet a 2) (evenPhi a) x +
          2 * cuspCharge a * evenPhi a x :=
  evenPhi_mulConv_C2 ha (evenPhi_integrable ha) (evenPhiJet_continuous a 0)

private def cPhi : ℝ := Real.pi ^ (1 / 4 : ℝ) / 4

/-- The actual real-valued Suzuki B image of the physical Gaussian. -/
def suzukiGaussianReal (a x : ℝ) : ℝ :=
  (actualSuzukiEvenBProfile (literalGaussian a) x).re

theorem suzukiGaussianReal_eq {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    suzukiGaussianReal a x = cPhi * evenPhi a x := by
  dsimp only [suzukiGaussianReal]
  rw [literalGaussian_actualSuzukiEvenB ha x]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← evenPhi_eq_actualPhi ha x]
  rfl

/-- Literal real autocorrelation with reflection. The source is the actual
    physical Gaussian's B image, not an assumed regularization. -/
def suzukiGaussianAutocorrelation (a : ℝ) : ℝ → ℝ :=
  mulConv (suzukiGaussianReal a) (fun x : ℝ => suzukiGaussianReal a (-x))

theorem suzukiGaussianAutocorrelation_C2 {a : ℝ} (ha : 0 ≤ a) :
    ContDiff ℝ 2 (suzukiGaussianAutocorrelation a) ∧
      ∀ x : ℝ, deriv (deriv (suzukiGaussianAutocorrelation a)) x =
        cPhi ^ 2 * (mulConv (evenPhiJet a 2) (evenPhi a) x +
          2 * cuspCharge a * evenPhi a x) := by
  have hp := evenPhi_autocorrelation_C2 ha
  have heq : suzukiGaussianAutocorrelation a =
      fun x : ℝ => cPhi ^ 2 * mulConv (evenPhi a) (evenPhi a) x := by
    funext x
    dsimp only [suzukiGaussianAutocorrelation, mulConv]
    simp_rw [suzukiGaussianReal_eq ha, evenPhi_neg]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have hc : ContDiff ℝ 2 (suzukiGaussianAutocorrelation a) := by
    rw [heq]
    exact contDiff_const.mul hp.1
  have hd : deriv (suzukiGaussianAutocorrelation a) =
      fun x : ℝ => cPhi ^ 2 * deriv (mulConv (evenPhi a) (evenPhi a)) x := by
    rw [heq]
    exact deriv_const_mul_field' _
  have hdd : deriv (deriv (suzukiGaussianAutocorrelation a)) =
      fun x : ℝ => cPhi ^ 2 * deriv (deriv (mulConv (evenPhi a) (evenPhi a))) x := by
    rw [hd]
    exact deriv_const_mul_field' _
  refine ⟨hc, fun x => ?_⟩
  rw [hdd]
  dsimp only
  rw [hp.2 x]

end RhTransient.ActualGaussianCuspSupplier

#print axioms RhTransient.EvenCuspConvolutionC2.evenCusp_mulConv_C2
#print axioms D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft.translated_phi_exp_one_integrable
