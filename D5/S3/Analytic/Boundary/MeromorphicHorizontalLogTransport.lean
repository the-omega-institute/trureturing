/- GID: D5/S3/Analytic/Boundary/MeromorphicHorizontalLogTransport
   generality: G
   mirror-B: D5/B/S3/Analytic/Boundary/MeromorphicHorizontalLogTransport
   mirror-E: none(waiver:compact-meromorphic-transport)
   anchors: []
   utility: none
   digest: Compact meromorphic signed horizontal lognorm transport. -/

import D5.S3.Analytic.Boundary.LogNormDirectionalDerivative
import D5.S3.Analytic.Boundary.HorizontalLogPotential
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.DiscreteSubset

/-!
# Compact meromorphic horizontal lognorm transport

A finite signed divisor factorization separates the singular logarithmic
potentials from an analytic nonvanishing regular factor. Codiscrete equalities
restrict to finite exceptional sets independently on each horizontal slice.
Only real logarithms and imaginary parts are integrated.

The signed singular-factor transport is supplied by
`HorizontalLogPotential.logPotential_signed_transport`, and the analytic
factor uses `LogNormDirectionalDerivative.vertical_log_norm_hasDerivAt`.
Mathlib supplies compact meromorphic divisor factorization and codiscrete
logarithmic derivative identities. The additional inference combines these
with finite exceptional sets on every horizontal slice and real Fubini.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Complex
open scoped BigOperators Interval Topology
open D5.S3.Analytic.Boundary.LogNormDirectionalDerivative
open D5.S3.Analytic.Boundary.HorizontalLogPotential

namespace D5.S3.Analytic.Boundary.MeromorphicHorizontalLogTransport

private def point (x t : ℝ) : ℂ := (x : ℂ) + I * (t : ℂ)

/- The integrability facts belong to this internal certificate, rather than a
   second public conjunction. Q is always a REAL function; for the final
   application it is Im(deriv f / f), including its totalized singular values. -/
private structure RectangleData (L Q : ℝ → ℝ → ℝ) (a b u v : ℝ) : Prop where
  log_integrable : ∀ t ∈ uIcc u v, IntervalIntegrable (fun x => L x t) volume a b
  im_integrable : ∀ t ∈ uIcc u v, IntervalIntegrable (fun x => Q x t) volume a b
  outer_integrable : IntervalIntegrable (fun t => -(∫ x in a..b, Q x t)) volume u v
  transport : (∫ x in a..b, L x v) - (∫ x in a..b, L x u) =
    ∫ t in u..v, -(∫ x in a..b, Q x t)

private theorem rectangle_add
    {L₁ L₂ Q₁ Q₂ : ℝ → ℝ → ℝ} {a b u v : ℝ}
    (h₁ : RectangleData L₁ Q₁ a b u v) (h₂ : RectangleData L₂ Q₂ a b u v) :
    RectangleData (fun x t => L₁ x t + L₂ x t)
      (fun x t => Q₁ x t + Q₂ x t) a b u v := by
  have hinner (t : ℝ) (ht : t ∈ uIcc u v) :
      -(∫ x in a..b, Q₁ x t + Q₂ x t) =
        -(∫ x in a..b, Q₁ x t) + -(∫ x in a..b, Q₂ x t) := by
    rw [intervalIntegral.integral_add (h₁.im_integrable t ht) (h₂.im_integrable t ht)]
    ring
  refine ⟨fun t ht => (h₁.log_integrable t ht).add (h₂.log_integrable t ht),
    fun t ht => (h₁.im_integrable t ht).add (h₂.im_integrable t ht), ?_, ?_⟩
  · exact (h₁.outer_integrable.add h₂.outer_integrable).congr
      (fun t ht => (hinner t (uIoc_subset_uIcc ht)).symm)
  · calc
      (∫ x in a..b, L₁ x v + L₂ x v) - (∫ x in a..b, L₁ x u + L₂ x u)
          = ((∫ x in a..b, L₁ x v) - (∫ x in a..b, L₁ x u)) +
            ((∫ x in a..b, L₂ x v) - (∫ x in a..b, L₂ x u)) := by
              rw [intervalIntegral.integral_add (h₁.log_integrable v right_mem_uIcc)
                    (h₂.log_integrable v right_mem_uIcc),
                  intervalIntegral.integral_add (h₁.log_integrable u left_mem_uIcc)
                    (h₂.log_integrable u left_mem_uIcc)]
              ring
      _ = (∫ t in u..v, -(∫ x in a..b, Q₁ x t)) +
            (∫ t in u..v, -(∫ x in a..b, Q₂ x t)) := by
              rw [h₁.transport, h₂.transport]
      _ = ∫ t in u..v, (-(∫ x in a..b, Q₁ x t) + -(∫ x in a..b, Q₂ x t)) :=
        (intervalIntegral.integral_add h₁.outer_integrable h₂.outer_integrable).symm
      _ = ∫ t in u..v, -(∫ x in a..b, Q₁ x t + Q₂ x t) :=
        intervalIntegral.integral_congr (fun t ht => (hinner t ht).symm)

private theorem rectangle_const_mul
    {L Q : ℝ → ℝ → ℝ} {a b u v : ℝ}
    (c : ℝ) (h : RectangleData L Q a b u v) :
    RectangleData (fun x t => c * L x t) (fun x t => c * Q x t) a b u v := by
  have hinner (t : ℝ) :
      -(∫ x in a..b, c * Q x t) = c * (-(∫ x in a..b, Q x t)) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  refine ⟨fun t ht => (h.log_integrable t ht).const_mul c,
    fun t ht => (h.im_integrable t ht).const_mul c, ?_, ?_⟩
  · exact (h.outer_integrable.const_mul c).congr (fun t _ => (hinner t).symm)
  · calc
      (∫ x in a..b, c * L x v) - (∫ x in a..b, c * L x u)
          = c * ((∫ x in a..b, L x v) - (∫ x in a..b, L x u)) := by
              rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
              ring
      _ = c * (∫ t in u..v, -(∫ x in a..b, Q x t)) := by rw [h.transport]
      _ = ∫ t in u..v, c * (-(∫ x in a..b, Q x t)) :=
        (intervalIntegral.integral_const_mul c _).symm
      _ = ∫ t in u..v, -(∫ x in a..b, c * Q x t) :=
        intervalIntegral.integral_congr (fun t _ => (hinner t).symm)

private theorem rectangle_finset_sum
    {ι : Type*} (s : Finset ι) (L Q : ι → ℝ → ℝ → ℝ) (a b u v : ℝ)
    (h : ∀ i ∈ s, RectangleData (L i) (Q i) a b u v) :
    RectangleData (fun x t => ∑ i ∈ s, L i x t)
      (fun x t => ∑ i ∈ s, Q i x t) a b u v := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro h
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t ht
        simpa using (intervalIntegrable_const (a := a) (b := b) (c := (0 : ℝ)))
      · intro t ht
        simpa using (intervalIntegrable_const (a := a) (b := b) (c := (0 : ℝ)))
      · simpa using (intervalIntegrable_const (a := u) (b := v) (c := (0 : ℝ)))
      · simp
  | @insert i s hi ih =>
      intro h
      have htail := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using
        rectangle_add (h i (Finset.mem_insert_self i s)) htail

private theorem rectangle_of_slice_ae
    {L Q M R : ℝ → ℝ → ℝ} {a b u v : ℝ}
    (h : RectangleData M R a b u v)
    (hL : ∀ t ∈ uIcc u v,
      (fun x => L x t) =ᵐ[volume.restrict (uIoc a b)] (fun x => M x t))
    (hQ : ∀ t ∈ uIcc u v,
      (fun x => Q x t) =ᵐ[volume.restrict (uIoc a b)] (fun x => R x t)) :
    RectangleData L Q a b u v := by
  have hiL (t : ℝ) (ht : t ∈ uIcc u v) :
      (∫ x in a..b, L x t) = ∫ x in a..b, M x t :=
    intervalIntegral.integral_congr_ae_restrict (hL t ht)
  have hiQ (t : ℝ) (ht : t ∈ uIcc u v) :
      (∫ x in a..b, Q x t) = ∫ x in a..b, R x t :=
    intervalIntegral.integral_congr_ae_restrict (hQ t ht)
  refine ⟨fun t ht => (h.log_integrable t ht).congr_ae (hL t ht).symm,
    fun t ht => (h.im_integrable t ht).congr_ae (hQ t ht).symm, ?_, ?_⟩
  · exact h.outer_integrable.congr (fun t ht => by rw [hiQ t (uIoc_subset_uIcc ht)])
  · rw [hiL v right_mem_uIcc, hiL u left_mem_uIcc, h.transport]
    exact intervalIntegral.integral_congr (fun t ht => by rw [hiQ t ht])

/- Pointwise vertical differentiation, finite signed FTC, then real Fubini. -/
private theorem regular_factor_rectangle_transport
    (g : ℂ → ℂ) (a b u v : ℝ)
    (hg : AnalyticOnNhd ℂ g (uIcc a b ×ℂ uIcc u v))
    (hzero : ∀ z ∈ uIcc a b ×ℂ uIcc u v, g z ≠ 0) :
    RectangleData (fun x t => Real.log ‖g (point x t)‖)
      (fun x t => (deriv g (point x t) / g (point x t)).im) a b u v := by
  let K : Set ℂ := uIcc a b ×ℂ uIcc u v
  let L : ℝ → ℝ → ℝ := fun x t => Real.log ‖g (point x t)‖
  let Q : ℝ → ℝ → ℝ := fun x t => (deriv g (point x t) / g (point x t)).im
  let F : ℝ → ℝ → ℝ := fun x t => -Q x t
  have hmem (x t : ℝ) (hx : x ∈ uIcc a b) (ht : t ∈ uIcc u v) : point x t ∈ K := by
    simpa [K, point, Complex.mem_reProdIm] using And.intro hx ht
  have hquot : ContinuousOn (fun z : ℂ => deriv g z / g z) K :=
    hg.deriv.continuousOn.div hg.continuousOn hzero
  have hlog : ContinuousOn (fun z : ℂ => Real.log ‖g z‖) K :=
    hg.continuousOn.norm.log (fun z hz => norm_ne_zero_iff.mpr (hzero z hz))
  have hLh (t : ℝ) (ht : t ∈ uIcc u v) :
      IntervalIntegrable (fun x => L x t) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    exact hlog.comp (by dsimp only [point]; fun_prop : Continuous (fun x : ℝ => point x t)).continuousOn
      (fun x hx => hmem x t hx ht)
  have hQh (t : ℝ) (ht : t ∈ uIcc u v) :
      IntervalIntegrable (fun x => Q x t) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    exact Complex.continuous_im.comp_continuousOn
      (hquot.comp (by dsimp only [point]; fun_prop : Continuous (fun x : ℝ => point x t)).continuousOn
        (fun x hx => hmem x t hx ht))
  have hFv (x : ℝ) (hx : x ∈ uIcc a b) :
      IntervalIntegrable (fun t => F x t) volume u v := by
    refine ContinuousOn.intervalIntegrable ?_
    exact (Complex.continuous_im.comp_continuousOn
      (hquot.comp (by dsimp only [point]; fun_prop : Continuous (fun t : ℝ => point x t)).continuousOn
        (fun t ht => hmem x t hx ht))).neg
  have hQcont : ContinuousOn Q.uncurry (uIcc a b ×ˢ uIcc u v) := by
    exact Complex.continuous_im.comp_continuousOn
      (hquot.comp (by dsimp only [point]; fun_prop : Continuous (fun p : ℝ × ℝ => point p.1 p.2)).continuousOn
        (fun p hp => hmem p.1 p.2 hp.1 hp.2))
  have hQint : IntegrableOn Q.uncurry (uIoc a b ×ˢ uIoc u v) :=
    (hQcont.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hFint : IntegrableOn F.uncurry (uIoc a b ×ˢ uIoc u v) :=
    (hQcont.neg.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hQprod : Integrable Q.uncurry
      ((volume.restrict (uIoc a b)).prod (volume.restrict (uIoc u v))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hQint
  have houterQ : IntervalIntegrable (fun t => ∫ x in a..b, Q x t) volume u v := by
    apply intervalIntegrable_iff.mpr
    change Integrable (fun t => ∫ x in a..b, Q x t) (volume.restrict (uIoc u v))
    simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul, Function.uncurry_apply_pair] using
      hQprod.integral_prod_right.const_mul (if a ≤ b then (1 : ℝ) else -1)
  have hFTC (x : ℝ) (hx : x ∈ uIcc a b) :
      (∫ t in u..v, F x t) = L x v - L x u := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      exact vertical_log_norm_hasDerivAt g (deriv g (point x t)) x t
        (hg _ (hmem x t hx ht)).differentiableAt.hasDerivAt (hzero _ (hmem x t hx ht))
    · exact hFv x hx
  refine ⟨hLh, hQh, houterQ.neg, ?_⟩
  calc
    (∫ x in a..b, L x v) - (∫ x in a..b, L x u)
        = ∫ x in a..b, (L x v - L x u) :=
      (intervalIntegral.integral_sub (hLh v right_mem_uIcc) (hLh u left_mem_uIcc)).symm
    _ = ∫ x in a..b, ∫ t in u..v, F x t :=
      intervalIntegral.integral_congr (fun x hx => (hFTC x hx).symm)
    _ = ∫ t in u..v, ∫ x in a..b, F x t :=
      MeasureTheory.intervalIntegral_intervalIntegral_swap hFint
    _ = ∫ t in u..v, -(∫ x in a..b, Q x t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact intervalIntegral.integral_neg

/- Both the logarithm and quotient identities hold a.e. independently at
   each height, by finite exceptional sets on compact horizontal images. -/
private theorem horizontal_ae_eq_of_codiscreteWithin
    {α : Type*} {f g : ℂ → α} {a b u v : ℝ} (hab : a ≤ b)
    (hfg : f =ᶠ[codiscreteWithin (Icc a b ×ℂ uIcc u v)] g)
    (t : ℝ) (ht : t ∈ uIcc u v) :
    (fun x : ℝ => f (point x t)) =ᵐ[volume.restrict (uIoc a b)]
      (fun x : ℝ => g (point x t)) := by
  classical
  let p : ℝ → ℂ := fun x => point x t
  let S : Set ℂ := p '' uIcc a b
  have hpcont : Continuous p := by dsimp [p, point]; fun_prop
  have hScompact : IsCompact S := isCompact_uIcc.image hpcont
  have hSK : S ⊆ Icc a b ×ℂ uIcc u v := by
    rintro z ⟨x, hx, rfl⟩
    simpa [p, point, Complex.mem_reProdIm, uIcc_of_le hab] using And.intro hx ht
  have hgood : {z : ℂ | f z = g z} ∈ codiscreteWithin S :=
    hfg.filter_mono (Filter.codiscreteWithin_mono hSK)
  have hfinite : (S \ {z : ℂ | f z = g z}).Finite :=
    hScompact.finite_sdiff_of_mem_codiscreteWithin hgood
  have hpinj : Function.Injective p := by
    intro x y hxy
    have hre := congrArg Complex.re hxy
    simpa [p, point] using hre
  have hpre : (p ⁻¹' (S \ {z : ℂ | f z = g z})).Finite :=
    Set.Finite.preimage hpinj.injOn hfinite
  have hae : ∀ᵐ x : ℝ ∂volume, x ∉ p ⁻¹' (S \ {z : ℂ | f z = g z}) :=
    hpre.countable.ae_notMem volume
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_uIoc] with x hx hxmem
  change f (p x) = g (p x)
  by_contra hneq
  apply hx
  exact ⟨⟨x, uIoc_subset_uIcc hxmem, rfl⟩, hneq⟩

private def atomLog (rho : ℂ) (x t : ℝ) : ℝ := Real.log ‖point x t - rho‖

private def atomD (rho : ℂ) (x t : ℝ) : ℝ :=
  (t - rho.im) / ((x - rho.re) ^ 2 + (t - rho.im) ^ 2)

private theorem point_norm_sq (rho : ℂ) (x t : ℝ) :
    ‖point x t - rho‖ ^ 2 = (x - rho.re) ^ 2 + (t - rho.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [point, pow_two]

private theorem atomLog_eq (rho : ℂ) (x t : ℝ) :
    atomLog rho x t = (1 / 2 : ℝ) *
      Real.log ((x - rho.re) ^ 2 + (t - rho.im) ^ 2) := by
  unfold atomLog
  rw [← point_norm_sq rho x t, Real.log_pow]
  ring

private theorem weighted_im_eq (n : ℤ) (rho : ℂ) (x t : ℝ) :
    ((n : ℂ) / (point x t - rho)).im = (n : ℝ) * (-atomD rho x t) := by
  have hden : Complex.normSq (point x t - rho) =
      (x - rho.re) ^ 2 + (t - rho.im) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, point_norm_sq]
  rw [Complex.div_im, hden]
  simp [point, atomD] <;> ring

private theorem atomLog_integrable (rho : ℂ) (a b t : ℝ) :
    IntervalIntegrable (fun x => atomLog rho x t) volume a b := by
  have ha : AnalyticOnNhd ℝ
      (fun x : ℝ => (x - rho.re) ^ 2 + (t - rho.im) ^ 2) univ := by fun_prop
  have hm : MeromorphicOn
      (fun x : ℝ => (x - rho.re) ^ 2 + (t - rho.im) ^ 2) (uIcc a b) :=
    fun x hx => (ha x (mem_univ x)).meromorphicAt
  simpa only [atomLog_eq, Function.comp_apply] using hm.intervalIntegrable_log.const_mul (1 / 2 : ℝ)

private theorem atomD_integrable (rho : ℂ) (a b t : ℝ) :
    IntervalIntegrable (fun x => atomD rho x t) volume a b := by
  by_cases ht : t - rho.im = 0
  · simpa [atomD, ht] using
      (intervalIntegrable_const (a := a) (b := b) (c := (0 : ℝ)))
  · have hden (x : ℝ) : (x - rho.re) ^ 2 + (t - rho.im) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (x - rho.re), sq_pos_of_ne_zero ht]
    have hc : Continuous (fun x : ℝ => atomD rho x t) :=
      continuous_const.div (by fun_prop) hden
    exact hc.continuousOn.intervalIntegrable

private theorem atomD_integral_eq (rho : ℂ) (a b t : ℝ) :
    (∫ x in a..b, atomD rho x t) =
      Real.arctan ((b - rho.re) / (t - rho.im)) -
        Real.arctan ((a - rho.re) / (t - rho.im)) := by
  calc
    (∫ x in a..b, atomD rho x t)
        = ∫ y in a - rho.re..b - rho.re,
            (t - rho.im) / ((t - rho.im) ^ 2 + y ^ 2) := by
          rw [← intervalIntegral.integral_comp_sub_right
            (fun y : ℝ => (t - rho.im) / ((t - rho.im) ^ 2 + y ^ 2)) rho.re]
          apply intervalIntegral.integral_congr
          intro x hx
          simp only [atomD, add_comm]
    _ = _ := integral_div_sq_add_sq

private theorem atomD_outer_integrable (rho : ℂ) (a b u v : ℝ) :
    IntervalIntegrable (fun t => ∫ x in a..b, atomD rho x t) volume u v := by
  have hm : Measurable (fun t : ℝ => ∫ x in a..b, atomD rho x t) := by
    simp_rw [atomD_integral_eq]
    fun_prop
  have hb (t : ℝ) : |∫ x in a..b, atomD rho x t| ≤ 2 * Real.pi := by
    rw [atomD_integral_eq, abs_le]
    constructor <;> nlinarith [Real.arctan_lt_pi_div_two ((b - rho.re) / (t - rho.im)),
      Real.neg_pi_div_two_lt_arctan ((b - rho.re) / (t - rho.im)),
      Real.arctan_lt_pi_div_two ((a - rho.re) / (t - rho.im)),
      Real.neg_pi_div_two_lt_arctan ((a - rho.re) / (t - rho.im)), Real.pi_pos]
  apply intervalIntegrable_iff.mpr
  refine (intervalIntegrable_const (a := u) (b := v) (c := 2 * Real.pi)).def'.mono'
    hm.aestronglyMeasurable ?_
  filter_upwards [] with t
  simpa only [Real.norm_eq_abs] using hb t

/- This is the actual use of accepted squared-log transport, shifted by the
   pole/zero ordinate. There is no restriction on either signed height. -/
private theorem singular_factor_rectangle_transport
    (rho : ℂ) (a b u v : ℝ) (hab : a ≤ b) :
    RectangleData (atomLog rho) (fun x t => -atomD rho x t) a b u v := by
  have hL (t : ℝ) : (∫ x in a..b, atomLog rho x t) =
      (1 / 2 : ℝ) * logPotential a b rho.re (t - rho.im) := by
    simp_rw [atomLog_eq]
    exact intervalIntegral.integral_const_mul _ _
  have hinner (t : ℝ) : (∫ x in a..b, atomD rho x t) =
      (1 / 2 : ℝ) * (∫ x in a..b, horizontalKernel rho.re x (t - rho.im)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    unfold atomD horizontalKernel
    ring
  have hshift : (∫ t in u..v, ∫ x in a..b, atomD rho x t) =
      (1 / 2 : ℝ) *
        (∫ s in u - rho.im..v - rho.im, ∫ x in a..b, horizontalKernel rho.re x s) := by
    simp_rw [hinner]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right
        (fun s : ℝ => ∫ x in a..b, horizontalKernel rho.re x s) rho.im]
  refine ⟨fun t ht => atomLog_integrable rho a b t,
    fun t ht => (atomD_integrable rho a b t).neg, ?_, ?_⟩
  · simpa only [intervalIntegral.integral_neg, neg_neg] using
      atomD_outer_integrable rho a b u v
  · simp only [intervalIntegral.integral_neg, neg_neg]
    rw [hL v, hL u, hshift, ← mul_sub,
      logPotential_signed_transport a b hab rho.re (u - rho.im) (v - rho.im)]

/- Full compact factorization, including negative integer divisor weights.
   No openness or nonvanishing of f on a slice is introduced. -/
private theorem meromorphic_rectangle_data
    (f : ℂ → ℂ) (a b u v : ℝ) (hab : a ≤ b)
    (hf : MeromorphicOn f (Icc a b ×ℂ uIcc u v))
    (hfinite : ∀ z ∈ Icc a b ×ℂ uIcc u v, meromorphicOrderAt f z ≠ ⊤) :
    RectangleData (fun x t => Real.log ‖f (point x t)‖)
      (fun x t => (deriv f (point x t) / f (point x t)).im) a b u v := by
  classical
  let K : Set ℂ := Icc a b ×ℂ uIcc u v
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_uIcc
  let D := MeromorphicOn.divisor f K
  have hD : (Function.support D).Finite := D.finiteSupport hK
  let s : Finset ℂ := hD.toFinset
  have hDzero (rho : ℂ) (hrho : rho ∉ s) : D rho = 0 := by
    simpa [s, Function.mem_support] using hrho
  obtain ⟨g, hg, hgnz, hfactor⟩ :=
    hf.extract_zeros_poles (fun z : K => hfinite z z.property) hD
  let P : ℂ → ℂ := ∏ᶠ rho, (· - rho) ^ D rho
  have hP : MeromorphicOn P K :=
    (Function.FactorizedRational.meromorphicNFOn D K).meromorphicOn
  have hPg : MeromorphicOn (P * g) K := hP.mul hg.meromorphicOn
  have hfactor' : f =ᶠ[codiscreteWithin K] P * g := by
    filter_upwards [hfactor] with z hz
    change f z = P z * g z
    simpa only [Pi.smul_apply', smul_eq_mul, P] using hz
  have hgorder (z : ℂ) (hz : z ∈ K) : meromorphicOrderAt g z ≠ ⊤ := by
    rw [(hg z hz).meromorphicOrderAt_eq,
      (hg z hz).analyticOrderAt_eq_zero.mpr (hgnz ⟨z, hz⟩)]
    simp
  have hPorder (z : ℂ) (hz : z ∈ K) : meromorphicOrderAt P z ≠ ⊤ :=
    Function.FactorizedRational.meromorphicOrderAt_ne_top D
  have hderiv : deriv f =ᶠ[codiscreteWithin K] deriv (P * g) :=
    hf.deriv_eventuallyEq_codiscreteWithin hPg hfactor'
  have hquotient : logDeriv f =ᶠ[codiscreteWithin K] logDeriv (P * g) := by
    filter_upwards [hderiv, hfactor'] with z hd hv
    simp only [logDeriv_apply]
    rw [hd, hv]
  have hmul := hP.logDeriv_mul_eventuallyEq hg.meromorphicOn hPorder hgorder
  have hlinear (rho : ℂ) : MeromorphicOn (fun z : ℂ => z - rho) K := by
    intro z hz
    fun_prop
  have hlinear_order (rho z : ℂ) (hz : z ∈ K) :
      meromorphicOrderAt (fun w : ℂ => w - rho) z ≠ ⊤ := by
    by_cases heq : z = rho
    · subst z
      simp
    · have ha : AnalyticAt ℂ (fun w : ℂ => w - rho) z := by fun_prop
      rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr heq)]
      simp
  have hprod := MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq
    (F := fun rho z : ℂ => z - rho) (d := fun rho => D rho) hD hlinear hlinear_order
  change logDeriv P =ᶠ[codiscreteWithin K]
    (fun z => ∑ᶠ rho, D rho • logDeriv (fun w : ℂ => w - rho) z) at hprod
  have hquotient_finite : logDeriv f =ᶠ[codiscreteWithin K]
      (fun z => (∑ rho ∈ s, (D rho : ℂ) / (z - rho)) + logDeriv g z) := by
    filter_upwards [hquotient, hmul, hprod] with z hq hm hp
    have hsupp : Function.support
        (fun rho => D rho • logDeriv (fun w : ℂ => w - rho) z) ⊆ s := by
      intro rho hrho
      by_contra hn
      apply hrho
      simp [hDzero rho hn]
    calc
      logDeriv f z = logDeriv P z + logDeriv g z := hq.trans hm
      _ = (∑ rho ∈ s, (D rho : ℂ) / (z - rho)) + logDeriv g z := by
        rw [hp, finsum_eq_sum_of_support_subset _ hsupp]
        congr 1
        apply Finset.sum_congr rfl
        intro rho hrho
        have hdiff : deriv (fun w : ℂ => w - rho) z = 1 := by
          simpa only [sub_zero, id_eq] using ((hasDerivAt_id z).sub_const rho).deriv
        rw [zsmul_eq_mul, logDeriv_apply, hdiff]
        ring
  have hlog := MeromorphicOn.extract_zeros_poles_log hgnz hfactor
  have hlog_finite : (fun z => Real.log ‖f z‖) =ᶠ[codiscreteWithin K]
      (fun z => (∑ rho ∈ s, (D rho : ℝ) * Real.log ‖z - rho‖) + Real.log ‖g z‖) := by
    have hsupp : Function.support
        (fun rho : ℂ => fun z : ℂ => (D rho : ℝ) * Real.log ‖z - rho‖) ⊆ s := by
      intro rho hrho
      by_contra hn
      apply hrho
      ext z
      simp [hDzero rho hn]
    filter_upwards [hlog] with z hz
    change Real.log ‖f z‖ =
      (∑ᶠ rho, fun w : ℂ => (D rho : ℝ) * Real.log ‖w - rho‖) z + Real.log ‖g z‖ at hz
    rw [finsum_eq_sum_of_support_subset _ hsupp] at hz
    simpa only [Finset.sum_apply] using hz
  let M : ℝ → ℝ → ℝ := fun x t =>
    (∑ rho ∈ s, (D rho : ℝ) * atomLog rho x t) + Real.log ‖g (point x t)‖
  let R : ℝ → ℝ → ℝ := fun x t =>
    (∑ rho ∈ s, (D rho : ℝ) * (-atomD rho x t)) +
      (deriv g (point x t) / g (point x t)).im
  have hg' : AnalyticOnNhd ℂ g (uIcc a b ×ℂ uIcc u v) := by
    simpa only [K, uIcc_of_le hab] using hg
  have hgnz' : ∀ z ∈ uIcc a b ×ℂ uIcc u v, g z ≠ 0 := by
    intro z hz
    apply hgnz ⟨z, ?_⟩
    simpa only [K, uIcc_of_le hab] using hz
  have hmodel : RectangleData M R a b u v := by
    exact rectangle_add
      (rectangle_finset_sum s
        (fun rho x t => (D rho : ℝ) * atomLog rho x t)
        (fun rho x t => (D rho : ℝ) * (-atomD rho x t)) a b u v
        (fun rho hrho => rectangle_const_mul (D rho : ℝ)
          (singular_factor_rectangle_transport rho a b u v hab)))
      (regular_factor_rectangle_transport g a b u v hg' hgnz')
  apply rectangle_of_slice_ae hmodel
  · intro t ht
    have ha := horizontal_ae_eq_of_codiscreteWithin hab hlog_finite t ht
    simpa only [M, atomLog] using ha
  · intro t ht
    have ha := horizontal_ae_eq_of_codiscreteWithin hab hquotient_finite t ht
    filter_upwards [ha] with x hx
    change (logDeriv f (point x t)).im = R x t
    rw [hx, Complex.add_im, Complex.im_sum]
    change (∑ rho ∈ s, ((D rho : ℂ) / (point x t - rho)).im) +
      (logDeriv g (point x t)).im = R x t
    dsimp only [R]
    congr 1
    apply Finset.sum_congr rfl
    intro rho hrho
    exact weighted_im_eq (D rho) rho x t

/-- Finite signed horizontal lognorm transport for a compact-meromorphic
function with finite order at every point. All zero/pole heights, spatial
endpoints, degenerate rectangles, and negative integer multiplicities are
included. The private, consumed `meromorphic_rectangle_data` certificate
contains each-height real log/Im and outer integrability proofs. -/
theorem meromorphic_horizontal_lognorm_transport
    (f : ℂ → ℂ) (a b u v : ℝ) (hab : a ≤ b)
    (hf : MeromorphicOn f (Icc a b ×ℂ uIcc u v))
    (hfinite : ∀ z ∈ Icc a b ×ℂ uIcc u v, meromorphicOrderAt f z ≠ ⊤) :
    (∫ x in a..b, Real.log ‖f ((x : ℂ) + I * (v : ℂ))‖) -
        (∫ x in a..b, Real.log ‖f ((x : ℂ) + I * (u : ℂ))‖) =
      ∫ t in u..v, -(∫ x in a..b,
        (deriv f ((x : ℂ) + I * (t : ℂ)) /
          f ((x : ℂ) + I * (t : ℂ))).im) := by
  exact (meromorphic_rectangle_data f a b u v hab hf hfinite).transport

end D5.S3.Analytic.Boundary.MeromorphicHorizontalLogTransport
