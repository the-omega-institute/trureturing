/- GID: D5/S3/Analytic/Isolation/GoldenGermThirdOrderStructuralZeros
   generality: I
   mirror-B: D5/B/S3/Analytic/Isolation/GoldenGermThirdOrderStructuralZeros
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two third-order denominator factors create simple structural zeros. -/

/- Library-search audit trail (2026-09-03):
   * The displayed five-zeta continuation is reused at the definition level
     from `golden_germ_third_order_factorization`: that frozen theorem exposes
     the continuation only under `ExistsUnique`, not as a named total function.
   * `golden_germ_third_normalized_factor_regularity` supplies both holomorphy
     and real-point nonvanishing for `G3`. The frozen golden auxiliary theorem
     supplies the denominator side condition at `1 / phi` for the second zero.
   * Repository and pinned-Mathlib searches found no public theorem stating
     zeta nonvanishing on `(0, 1)`. Since `zeta(1/2)` is an unavoidable regular
     factor at both points, the adjacent-pair eta argument from the frozen
     auxiliary module is instantiated internally rather than accessed through
     a generated private name. Mathlib's public `riemannZeta₁` gives the
     removable numerator used in the simple-zero normal form.

   STOPPING JUSTIFICATION: this theorem identifies only the two zeros forced
   by the displayed third-order denominator factors. It neither classifies
   any other zeros nor proves O-5, RH, or an all-order extraction theorem. -/

import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
import D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity
import D5.S3.Analytic.Isolation.GoldenAuxiliaryZetaNonzero
import D5.S3.Analytic.Isolation.GoldenGermStructuralSimplePole
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace D5.S3.Analytic.Isolation.GoldenGermThirdOrderStructuralZeros

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Filter Function Set Topology
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity
open D5.S3.Analytic.Isolation.GoldenAuxiliaryZetaNonzero
open scoped Topology

noncomputable section

private def etaPairTerm (n : ℕ) (s : ℂ) : ℂ :=
  (((2 * n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) -
    (((2 * n + 2 : ℕ) : ℝ) : ℂ) ^ (-s)

private noncomputable def pairedEta (s : ℂ) : ℂ :=
  ∑' n : ℕ, etaPairTerm n s

private def realEtaPairTerm (n : ℕ) (x : ℝ) : ℝ :=
  ((2 * n + 1 : ℕ) : ℝ) ^ (-x) - ((2 * n + 2 : ℕ) : ℝ) ^ (-x)

private noncomputable def zetaEtaFactor (s : ℂ) : ℂ :=
  (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s

private lemma etaPairTerm_norm_le {delta radius : ℝ} (hdelta : 0 < delta)
    {s : ℂ} (hsre : delta ≤ s.re) (hsnorm : ‖s‖ ≤ radius) (n : ℕ) :
    ‖etaPairTerm n s‖ ≤
      radius * ((2 * n + 1 : ℕ) : ℝ) ^ (-delta - 1) := by
  let a : ℝ := (2 * n + 1 : ℕ)
  let b : ℝ := (2 * n + 2 : ℕ)
  have ha : 1 ≤ a := by simp [a]
  have hab : a ≤ b := by simp [a, b]
  have hs0 : -s ≠ 0 := by
    exact neg_ne_zero.mpr (ne_zero_of_re_pos (hdelta.trans_le hsre))
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-s))
        ((-s) * (x : ℂ) ^ (-s - 1)) (Set.Icc a b) x := by
    exact (hasDerivAt_ofReal_cpow_const
      (lt_of_lt_of_le zero_lt_one (ha.trans hx.1)).ne' hs0).hasDerivWithinAt
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤
        radius * a ^ (-delta - 1) := by
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one (ha.trans hx.1)
    have hexp_nonpos : (-s.re - 1 : ℝ) ≤ 0 := by linarith
    have hbase : x ^ (-s.re - 1) ≤ a ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one ha)
        hx.1 hexp_nonpos
    have hexp : a ^ (-s.re - 1) ≤ a ^ (-delta - 1) :=
      Real.rpow_le_rpow_of_exponent_le ha (by linarith)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul hsnorm (hbase.trans hexp)
      (Real.rpow_nonneg (le_of_lt hxpos) _) ((norm_nonneg s).trans hsnorm)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Icc a b) (x := a) (y := b)
    (f := fun x : ℝ => (x : ℂ) ^ (-s))
    (f' := fun x : ℝ => (-s) * (x : ℂ) ^ (-s - 1))
    hderiv hbound (convex_Icc a b) (left_mem_Icc.mpr hab)
      (right_mem_Icc.mpr hab)
  have hba : b - a = 1 := by norm_num [a, b]
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), hba, mul_one] at hmv
  have hmv' :
      ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤
        radius * a ^ (-delta - 1) := by
    rw [← norm_neg]
    simpa [a, b] using hmv
  simpa [etaPairTerm, a, b] using hmv'

private lemma etaPairTerm_summable {s : ℂ} (hs : 0 < s.re) :
    Summable fun n : ℕ => etaPairTerm n s := by
  let delta : ℝ := s.re / 2
  let radius : ℝ := ‖s‖
  have hdelta : 0 < delta := by simp [delta, hs]
  have hp : 1 < delta + 1 := by linarith
  have hseries : Summable
      (fun n : ℕ => radius * ((n + 1 : ℕ) : ℝ) ^ (-delta - 1)) := by
    have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (delta + 1)) :=
      Real.summable_one_div_nat_rpow.mpr hp
    have hshift := hbase.comp_injective (add_left_injective 1)
    have heq :
        (fun n : ℕ => radius * ((n + 1 : ℕ) : ℝ) ^ (-delta - 1)) =
          fun n : ℕ => radius * (((n + 1 : ℕ) : ℝ) ^ (delta + 1))⁻¹ := by
      funext n
      rw [show -delta - 1 = -(delta + 1) by ring,
        Real.rpow_neg (by positivity) (delta + 1)]
    rw [heq]
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_comm,
      one_div] using hshift.mul_left radius
  apply Summable.of_norm_bounded hseries
  intro n
  have hraw := etaPairTerm_norm_le hdelta (s := s)
    (by simp [delta]; linarith) (show ‖s‖ ≤ radius by rfl) n
  have hcast : ((n + 1 : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : n + 1 ≤ 2 * n + 1)
  have hpow : ((2 * n + 1 : ℕ) : ℝ) ^ (-delta - 1) ≤
      ((n + 1 : ℕ) : ℝ) ^ (-delta - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hcast (by linarith)
  exact hraw.trans (mul_le_mul_of_nonneg_left hpow (by simp [radius]))

private lemma differentiableOn_pairedEta :
    DifferentiableOn ℂ pairedEta {s : ℂ | 0 < s.re} := by
  intro z hz
  change 0 < z.re at hz
  let delta : ℝ := z.re / 2
  let radius : ℝ := ‖z‖ + 1
  let U : Set ℂ := {w : ℂ | delta < w.re ∧ ‖w‖ < radius}
  have hdelta : 0 < delta := by simp [delta]; linarith
  have hradius : 0 ≤ radius := by
    dsimp [radius]
    linarith [norm_nonneg z]
  have hU_open : IsOpen U := by
    exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hzU : z ∈ U := by
    constructor
    · dsimp [delta]
      linarith
    · dsimp [radius]
      linarith
  have hmajorant : Summable
      (fun n : ℕ => radius * ((n + 1 : ℕ) : ℝ) ^ (-delta - 1)) := by
    have hp : 1 < delta + 1 := by linarith
    have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (delta + 1)) :=
      Real.summable_one_div_nat_rpow.mpr hp
    have hshift := hbase.comp_injective (add_left_injective 1)
    have heq :
        (fun n : ℕ => radius * ((n + 1 : ℕ) : ℝ) ^ (-delta - 1)) =
          fun n : ℕ => radius * (((n + 1 : ℕ) : ℝ) ^ (delta + 1))⁻¹ := by
      funext n
      rw [show -delta - 1 = -(delta + 1) by ring,
        Real.rpow_neg (by positivity) (delta + 1)]
    rw [heq]
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_comm,
      one_div] using hshift.mul_left radius
  have hterm (n : ℕ) : DifferentiableOn ℂ (etaPairTerm n) U := by
    intro w _
    have hodd : ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (by omega : 2 * n + 1 ≠ 0)
    have heven : ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (by omega : 2 * n + 2 ≠ 0)
    apply DifferentiableAt.differentiableWithinAt
    unfold etaPairTerm
    apply DifferentiableAt.sub
    · exact ((hasDerivAt_neg' w).const_cpow (Or.inl hodd)).differentiableAt
    · exact ((hasDerivAt_neg' w).const_cpow (Or.inl heven)).differentiableAt
  have hterm_bound (n : ℕ) (w : ℂ) (hw : w ∈ U) :
      ‖etaPairTerm n w‖ ≤
        radius * ((n + 1 : ℕ) : ℝ) ^ (-delta - 1) := by
    have hraw := etaPairTerm_norm_le hdelta (s := w) hw.1.le hw.2.le n
    have hcast : ((n + 1 : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ 2 * n + 1)
    have hpow : ((2 * n + 1 : ℕ) : ℝ) ^ (-delta - 1) ≤
        ((n + 1 : ℕ) : ℝ) ^ (-delta - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hcast (by linarith)
    exact hraw.trans (mul_le_mul_of_nonneg_left hpow hradius)
  have hdiff : DifferentiableOn ℂ pairedEta U := by
    change DifferentiableOn ℂ (fun w => ∑' n : ℕ, etaPairTerm n w) U
    exact Complex.differentiableOn_tsum_of_summable_norm
      hmajorant hterm hU_open hterm_bound
  exact ((hdiff z hzU).differentiableAt
    (hU_open.mem_nhds hzU)).differentiableWithinAt

private lemma pairedEta_eq_zeta_factor_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    pairedEta s = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s)
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr
    (ne_zero_of_re_pos (zero_lt_one.trans hs))
  have hf : Summable f := by
    have h := Complex.summable_one_div_nat_cpow.mpr hs
    simpa only [f, Complex.cpow_neg, one_div] using h
  have htotal : ∑' n : ℕ, f n = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    exact tsum_congr fun n => by simp only [f, Complex.cpow_neg, one_div]
  have hzero : f 0 = 0 := by simp [f, zero_cpow hs0]
  have heven_summable : Summable fun n : ℕ => f (2 * n) :=
    hf.comp_injective (mul_right_injective₀ (by omega : (2 : ℕ) ≠ 0))
  have hodd_injective : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b hab
    exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel hab)
  have hodd_summable : Summable fun n : ℕ => f (2 * n + 1) :=
    hf.comp_injective hodd_injective
  have heven : ∑' n : ℕ, f (2 * n) =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
    calc
      ∑' n : ℕ, f (2 * n) = ∑' n : ℕ, (2 : ℂ) ^ (-s) * f n := by
        exact tsum_congr fun n => by
          simpa only [f, Nat.cast_mul, Nat.cast_ofNat] using
            Complex.natCast_mul_natCast_cpow 2 n (-s)
      _ = (2 : ℂ) ^ (-s) * ∑' n : ℕ, f n := by rw [tsum_mul_left]
      _ = (2 : ℂ) ^ (-s) * riemannZeta s := by rw [htotal]
  have heven_shift_summable : Summable fun n : ℕ => f (2 * n + 2) := by
    have h := heven_summable.comp_injective (add_left_injective 1)
    apply h.congr
    intro n
    simp only [Function.comp_apply]
    congr 1
  have heven_shift : ∑' n : ℕ, f (2 * n + 2) =
      ∑' n : ℕ, f (2 * n) := by
    have h := heven_summable.tsum_eq_zero_add
    rw [hzero, zero_add] at h
    simpa only [Nat.mul_add, Nat.mul_one] using h.symm
  have hsplit := tsum_even_add_odd heven_summable hodd_summable
  rw [htotal, heven] at hsplit
  rw [pairedEta]
  change (∑' n : ℕ, (f (2 * n + 1) - f (2 * n + 2))) = _
  rw [hodd_summable.tsum_sub heven_shift_summable, heven_shift, heven]
  calc
    (∑' n : ℕ, f (2 * n + 1)) - (2 : ℂ) ^ (-s) * riemannZeta s =
        ((2 : ℂ) ^ (-s) * riemannZeta s +
          ∑' n : ℕ, f (2 * n + 1)) -
          2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by ring
    _ = riemannZeta s -
        2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by rw [hsplit]
    _ = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by ring

private lemma pairedEta_eq_zetaEtaFactor_upper_half_plane :
    Set.EqOn pairedEta zetaEtaFactor
      ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}) := by
  let U : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_const continuous_im)
  have hU_preconnected : IsPreconnected U :=
    ((convex_halfSpace_re_gt 0).inter
      (convex_halfSpace_im_gt 0)).isPreconnected
  have hpaired_diff : DifferentiableOn ℂ pairedEta U :=
    differentiableOn_pairedEta.mono inter_subset_left
  have hfactor_diff : DifferentiableOn ℂ zetaEtaFactor U := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      change 0 < (1 : ℂ).re ∧ 0 < (1 : ℂ).im at hs
      norm_num at hs
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (-w)) s :=
      ((hasDerivAt_neg' s).const_cpow
        (Or.inl (by norm_num))).differentiableAt
    have hfactor : DifferentiableAt ℂ
        (fun w : ℂ => 1 - 2 * (2 : ℂ) ^ (-w)) s :=
      (differentiableAt_const (c := (1 : ℂ))).sub
        ((differentiableAt_const (c := (2 : ℂ))).mul hpow)
    exact (hfactor.mul
      (differentiableAt_riemannZeta hs1)).differentiableWithinAt
  have hz0 : (2 + I : ℂ) ∈ U := by constructor <;> norm_num
  have hnear : pairedEta =ᶠ[𝓝 (2 + I : ℂ)] zetaEtaFactor := by
    filter_upwards
      [(isOpen_lt continuous_const continuous_re).mem_nhds
        (by norm_num : (1 : ℝ) < (2 + I : ℂ).re)] with s hs
    exact (pairedEta_eq_zeta_factor_of_one_lt_re hs).trans rfl
  change Set.EqOn pairedEta zetaEtaFactor U
  exact (hpaired_diff.analyticOnNhd hU_open).eqOn_of_preconnected_of_eventuallyEq
    (hfactor_diff.analyticOnNhd hU_open) hU_preconnected hz0 hnear

private lemma pairedEta_eq_zetaEtaFactor_of_real {x : ℝ}
    (hx : 0 < x) (hx1 : x ≠ 1) :
    pairedEta (x : ℂ) = zetaEtaFactor (x : ℂ) := by
  let seq : ℕ → ℂ := fun n => (x : ℂ) + I * (1 / ((n + 1 : ℕ) : ℂ))
  have hone_div : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
  have hseq : Tendsto seq atTop (𝓝 (x : ℂ)) := by
    simpa only [seq, mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hone_div)
  have hseq_mem (n : ℕ) :
      seq n ∈ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}) := by
    constructor
    · simp [seq, hx]
    · change 0 < (seq n).im
      have him : (seq n).im = (((n + 1 : ℕ) : ℂ)⁻¹).re := by
        simp only [seq, add_im, ofReal_im, zero_add, mul_im, I_re, I_im,
          zero_mul, one_mul, one_div]
      rw [him, inv_re, normSq_natCast]
      exact div_pos (by exact_mod_cast Nat.zero_lt_succ n) (by positivity)
  have hseq_eq (n : ℕ) : pairedEta (seq n) = zetaEtaFactor (seq n) :=
    pairedEta_eq_zetaEtaFactor_upper_half_plane (hseq_mem n)
  have hpaired_cont : ContinuousAt pairedEta (x : ℂ) := by
    have hxmem : (x : ℂ) ∈ {s : ℂ | 0 < s.re} := by simpa using hx
    exact ((differentiableOn_pairedEta (x : ℂ) hxmem).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        hxmem)).continuousAt
  have hfactor_cont : ContinuousAt zetaEtaFactor (x : ℂ) := by
    have hx1c : (x : ℂ) ≠ 1 := by exact_mod_cast hx1
    have hpow : DifferentiableAt ℂ
        (fun w : ℂ => (2 : ℂ) ^ (-w)) (x : ℂ) :=
      ((hasDerivAt_neg' (x : ℂ)).const_cpow
        (Or.inl (by norm_num))).differentiableAt
    have hfactor : DifferentiableAt ℂ
        (fun w : ℂ => 1 - 2 * (2 : ℂ) ^ (-w)) (x : ℂ) :=
      (differentiableAt_const (c := (1 : ℂ))).sub
        ((differentiableAt_const (c := (2 : ℂ))).mul hpow)
    exact (hfactor.mul (differentiableAt_riemannZeta hx1c)).continuousAt
  have hleft := hpaired_cont.tendsto.comp hseq
  have hright := hfactor_cont.tendsto.comp hseq
  have hleft' : Tendsto (zetaEtaFactor ∘ seq) atTop
      (𝓝 (pairedEta (x : ℂ))) := by
    apply hleft.congr'
    exact Eventually.of_forall hseq_eq
  exact tendsto_nhds_unique hleft' hright

private lemma etaPairTerm_of_real (n : ℕ) (x : ℝ) :
    etaPairTerm n (x : ℂ) = (realEtaPairTerm n x : ℂ) := by
  unfold etaPairTerm realEtaPairTerm
  rw [← Complex.ofReal_neg]
  rw [← Complex.ofReal_cpow (by positivity) (-x),
    ← Complex.ofReal_cpow (by positivity) (-x)]
  exact (Complex.ofReal_sub _ _).symm

private lemma realEtaPairTerm_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < realEtaPairTerm n x := by
  unfold realEtaPairTerm
  apply sub_pos.mpr
  exact Real.strictAntiOn_rpow_Ioi_of_exponent_neg (neg_lt_zero.mpr hx)
    (by change 0 < ((2 * n + 1 : ℕ) : ℝ); positivity)
    (by change 0 < ((2 * n + 2 : ℕ) : ℝ); positivity)
    (by exact_mod_cast (by omega : 2 * n + 1 < 2 * n + 2))

private lemma realEtaPairTerm_summable {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => realEtaPairTerm n x := by
  rw [← Complex.summable_ofReal]
  exact (etaPairTerm_summable (by simpa using hx)).congr fun n =>
    etaPairTerm_of_real n x

private lemma riemannZeta_ne_zero_of_real_pos {x : ℝ}
    (hx : 0 < x) (hx1 : x ≠ 1) : riemannZeta (x : ℂ) ≠ 0 := by
  have hsummable := realEtaPairTerm_summable hx
  have hsum : 0 < ∑' n : ℕ, realEtaPairTerm n x :=
    hsummable.tsum_pos (fun n => (realEtaPairTerm_pos n hx).le) 0
      (realEtaPairTerm_pos 0 hx)
  have hpair : pairedEta (x : ℂ) =
      ((∑' n : ℕ, realEtaPairTerm n x : ℝ) : ℂ) := by
    rw [pairedEta]
    calc
      (∑' n : ℕ, etaPairTerm n (x : ℂ)) =
          ∑' n : ℕ, (realEtaPairTerm n x : ℂ) :=
        tsum_congr fun n => etaPairTerm_of_real n x
      _ = ((∑' n : ℕ, realEtaPairTerm n x : ℝ) : ℂ) :=
        (Complex.ofReal_tsum _).symm
  have heta : pairedEta (x : ℂ) ≠ 0 := by
    rw [hpair]
    exact_mod_cast hsum.ne'
  intro hzeta
  apply heta
  rw [pairedEta_eq_zetaEtaFactor_of_real hx hx1, zetaEtaFactor,
    hzeta, mul_zero]

private noncomputable def phiSq : ℂ :=
  ((Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def phiCub : ℂ :=
  ((Real.goldenRatio ^ 3 : ℝ) : ℂ)

private noncomputable def doublePhiSq : ℂ :=
  ((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def doublePhiCub : ℂ :=
  ((2 * Real.goldenRatio ^ 3 : ℝ) : ℂ)

private noncomputable def mixedScale : ℂ :=
  ((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : ℝ) : ℂ)

private noncomputable def z2 : ℂ :=
  ((1 / (2 * Real.goldenRatio ^ 2) : ℝ) : ℂ)

private noncomputable def z3 : ℂ :=
  ((1 / (2 * Real.goldenRatio ^ 3) : ℝ) : ℂ)

private noncomputable def thirdG : ℂ → ℂ := fun s =>
  ∏' p : Nat.Primes,
    let x := (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
    let y := (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))
    (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p

private noncomputable def thirdGerm : ℂ → ℂ := fun s =>
  riemannZeta (phiSq * s) * riemannZeta (phiCub * s) *
    (riemannZeta (doublePhiSq * s))⁻¹ *
    ((riemannZeta (doublePhiCub * s))⁻¹ *
      riemannZeta (mixedScale * s) * thirdG s)

private lemma scale_ne_zero (c : ℝ) (hc : 0 < c) : ((c : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast hc.ne'

private lemma transport_identities :
    phiSq * z2 = ((1 / 2 : ℝ) : ℂ) ∧
    phiCub * z2 = ((Real.goldenRatio / 2 : ℝ) : ℂ) ∧
    doublePhiSq * z2 = 1 ∧
    doublePhiCub * z2 = (Real.goldenRatio : ℂ) ∧
    mixedScale * z2 = ((1 + Real.goldenRatio / 2 : ℝ) : ℂ) ∧
    phiSq * z3 = ((1 / (2 * Real.goldenRatio) : ℝ) : ℂ) ∧
    phiCub * z3 = ((1 / 2 : ℝ) : ℂ) ∧
    doublePhiSq * z3 = ((1 / Real.goldenRatio : ℝ) : ℂ) ∧
    doublePhiCub * z3 = 1 ∧
    mixedScale * z3 =
      ((1 / Real.goldenRatio + 1 / 2 : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [phiSq, phiCub, doublePhiSq, doublePhiCub, mixedScale, z2, z3,
      ← Complex.ofReal_mul, Complex.ofReal_inj] <;>
    field_simp [Real.goldenRatio_ne_zero] <;>
    norm_num

private lemma numeric_facts :
    1 / Real.goldenRatio ^ 5 < 1 / (2 * Real.goldenRatio ^ 2) ∧
    1 / Real.goldenRatio ^ 5 < 1 / (2 * Real.goldenRatio ^ 3) ∧
    (0 : ℝ) < Real.goldenRatio / 2 ∧ Real.goldenRatio / 2 < 1 ∧
    (0 : ℝ) < 1 / (2 * Real.goldenRatio) ∧
    (1 : ℝ) < 1 / Real.goldenRatio + 1 / 2 := by
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi2 : 2 < Real.goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    linarith [Real.one_lt_goldenRatio]
  have hphi3 : 2 < Real.goldenRatio ^ 3 := by
    calc
      2 < Real.goldenRatio ^ 2 := hphi2
      _ < Real.goldenRatio ^ 2 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right (by positivity)).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 3 := by ring
  have hinvHalf : (1 : ℝ) / 2 < 1 / Real.goldenRatio :=
    one_div_lt_one_div_of_lt hphi Real.goldenRatio_lt_two
  constructor
  · rw [one_div_lt_one_div (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hphi3 (show 0 < Real.goldenRatio ^ 2 by positivity)]
  constructor
  · rw [one_div_lt_one_div (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hphi2 (show 0 < Real.goldenRatio ^ 3 by positivity)]
  exact ⟨by positivity, (div_lt_one (by norm_num)).mpr Real.goldenRatio_lt_two,
    by positivity, by linarith⟩

private lemma zeta_scale_analytic {c z : ℂ} (h : c * z ≠ 1) :
    AnalyticAt ℂ (fun s : ℂ => riemannZeta (c * s)) z :=
  (analyticOn_riemannZeta _ h).comp (analyticAt_const.mul analyticAt_id)

private lemma inverse_zeta_scale_analytic {c z : ℂ}
    (hpole : c * z ≠ 1) (hnz : riemannZeta (c * z) ≠ 0) :
    AnalyticAt ℂ (fun s : ℂ => (riemannZeta (c * s))⁻¹) z :=
  (zeta_scale_analytic hpole).inv hnz

private lemma ofReal_ne_one {x : ℝ} (hx : x ≠ 1) : (x : ℂ) ≠ 1 := by
  exact_mod_cast hx

private lemma inverse_zeta_simple_zero {c z : ℂ} (hc : c ≠ 0)
    (hcz : c * z = 1) {R : ℂ → ℂ} (hR : AnalyticAt ℂ R z)
    (hR0 : R z ≠ 0) :
    MeromorphicAt (fun s => (riemannZeta (c * s))⁻¹ * R s) z ∧
      meromorphicOrderAt (fun s => (riemannZeta (c * s))⁻¹ * R s) z =
        (1 : ℤ) := by
  let regular : ℂ → ℂ := fun s =>
    (riemannZeta₁ (c * s))⁻¹ * (c * R s)
  have hinner : AnalyticAt ℂ (fun s : ℂ => c * s) z :=
    analyticAt_const.mul analyticAt_id
  have houter : AnalyticAt ℂ riemannZeta₁ (c * z) :=
    differentiable_riemannZeta₁.analyticAt (c * z)
  have hunit : AnalyticAt ℂ (fun s : ℂ => riemannZeta₁ (c * s)) z :=
    houter.comp hinner
  have hunit0 : riemannZeta₁ (c * z) ≠ 0 := by rw [hcz]; norm_num
  have hregular : AnalyticAt ℂ regular z := by
    exact (hunit.inv hunit0).mul (analyticAt_const.mul hR)
  have hregular0 : regular z ≠ 0 := by
    dsimp [regular]
    exact mul_ne_zero (inv_ne_zero hunit0) (mul_ne_zero hc hR0)
  have hnormal : ∀ᶠ s in 𝓝[≠] z,
      (riemannZeta (c * s))⁻¹ * R s =
        (s - z) ^ (1 : ℤ) • regular s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hcs : c * s ≠ 1 := by
      rw [← hcz]
      exact fun h => hs (mul_left_cancel₀ hc h)
    have hlinear : c * s - 1 = c * (s - z) := by
      rw [mul_sub, hcz]
    rw [riemannZeta_eq_inv_sub_mul hcs, hlinear, zpow_one, smul_eq_mul]
    dsimp [regular]
    field_simp
  have hmero : MeromorphicAt
      (fun s => (riemannZeta (c * s))⁻¹ * R s) z :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
      ⟨(1 : ℤ), regular, hregular, hnormal⟩
  exact ⟨hmero, (meromorphicOrderAt_eq_int_iff hmero).mpr
    ⟨regular, hregular, hregular0, hnormal⟩⟩

private lemma thirdG_analytic (z : ℂ)
    (hz : 1 / Real.goldenRatio ^ 5 < z.re) : AnalyticAt ℂ thirdG z := by
  have h := golden_germ_third_normalized_factor_regularity
  dsimp only at h
  change AnalyticAt ℂ thirdG z
  exact h.2.1 z hz

private lemma thirdG_real_ne_zero (sigma : ℝ)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) :
    thirdG (sigma : ℂ) ≠ 0 := by
  have h := golden_germ_third_normalized_factor_regularity
  dsimp only at h
  change thirdG (sigma : ℂ) ≠ 0
  exact h.2.2.2.1 sigma hsigma

private noncomputable def regular2 : ℂ → ℂ := fun s =>
  riemannZeta (phiSq * s) * riemannZeta (phiCub * s) *
    (riemannZeta (doublePhiCub * s))⁻¹ *
    riemannZeta (mixedScale * s) * thirdG s

private noncomputable def regular3 : ℂ → ℂ := fun s =>
  riemannZeta (phiSq * s) * riemannZeta (phiCub * s) *
    (riemannZeta (doublePhiSq * s))⁻¹ *
    riemannZeta (mixedScale * s) * thirdG s

private lemma regular2_analytic : AnalyticAt ℂ regular2 z2 := by
  have ht := transport_identities
  have hsquare := ht.1
  have hcubed := ht.2.1
  have hdoubleCubed := ht.2.2.2.1
  have hmixed := ht.2.2.2.2.1
  have hphi := riemannZeta_ne_zero_of_one_le_re
    (s := (Real.goldenRatio : ℂ)) (by simpa using Real.one_lt_goldenRatio.le)
  have hphi' : riemannZeta (doublePhiCub * z2) ≠ 0 := by
    rw [hdoubleCubed]
    exact hphi
  have h1 := zeta_scale_analytic (c := phiSq) (z := z2) (by
    rw [hsquare]
    exact ofReal_ne_one (by norm_num))
  have h2 := zeta_scale_analytic (c := phiCub) (z := z2) (by
    rw [hcubed]
    exact ofReal_ne_one (ne_of_lt numeric_facts.2.2.2.1))
  have h3 := inverse_zeta_scale_analytic
    (c := doublePhiCub) (z := z2) (by
      rw [hdoubleCubed]
      exact ofReal_ne_one Real.one_lt_goldenRatio.ne') hphi'
  have h4 := zeta_scale_analytic (c := mixedScale) (z := z2) (by
    rw [hmixed]
    exact ofReal_ne_one (by
      nlinarith [Real.goldenRatio_pos]))
  have h5 : AnalyticAt ℂ thirdG z2 :=
    thirdG_analytic z2 (by simpa only [z2, Complex.ofReal_re] using numeric_facts.1)
  exact (((h1.mul h2).mul h3).mul h4).mul h5

private lemma regular2_ne_zero : regular2 z2 ≠ 0 := by
  have ht := transport_identities
  rw [regular2, ht.1, ht.2.1, ht.2.2.2.1, ht.2.2.2.2.1]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (riemannZeta_ne_zero_of_real_pos (by norm_num) (by norm_num))
          (riemannZeta_ne_zero_of_real_pos numeric_facts.2.2.1
            (ne_of_lt numeric_facts.2.2.2.1)))
        (inv_ne_zero (riemannZeta_ne_zero_of_one_le_re
          (by simpa using Real.one_lt_goldenRatio.le))))
      (riemannZeta_ne_zero_of_one_le_re
        (by simp only [Complex.ofReal_re]; linarith [Real.goldenRatio_pos])))
    (by
      change thirdG (((1 / (2 * Real.goldenRatio ^ 2) : ℝ) : ℂ)) ≠ 0
      exact thirdG_real_ne_zero
        (1 / (2 * Real.goldenRatio ^ 2)) numeric_facts.1)

private lemma regular3_analytic : AnalyticAt ℂ regular3 z3 := by
  have ht := transport_identities
  have hsquare := ht.2.2.2.2.2.1
  have hcubed := ht.2.2.2.2.2.2.1
  have hdoubleSquared := ht.2.2.2.2.2.2.2.1
  have hmixed := ht.2.2.2.2.2.2.2.2.2
  have hsmall : (1 / (2 * Real.goldenRatio) : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [Real.one_lt_goldenRatio]
  have haux : riemannZeta (doublePhiSq * z3) ≠ 0 := by
    rw [hdoubleSquared]
    exact riemannZeta_golden_auxiliary_ne_zero
  have h1 := zeta_scale_analytic (c := phiSq) (z := z3) (by
    rw [hsquare]
    exact ofReal_ne_one (ne_of_lt hsmall))
  have h2 := zeta_scale_analytic (c := phiCub) (z := z3) (by
    rw [hcubed]
    exact ofReal_ne_one (by norm_num))
  have h3 := inverse_zeta_scale_analytic
    (c := doublePhiSq) (z := z3) (by
      rw [hdoubleSquared]
      exact ofReal_ne_one (ne_of_lt (by
        simpa only [one_div] using
          (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)))) haux
  have h4 := zeta_scale_analytic (c := mixedScale) (z := z3) (by
    rw [hmixed]
    exact ofReal_ne_one (ne_of_gt numeric_facts.2.2.2.2.2))
  have h5 : AnalyticAt ℂ thirdG z3 :=
    thirdG_analytic z3 (by
      simpa only [z3, Complex.ofReal_re] using numeric_facts.2.1)
  exact (((h1.mul h2).mul h3).mul h4).mul h5

private lemma regular3_ne_zero : regular3 z3 ≠ 0 := by
  have ht := transport_identities
  have hsmall : (1 / (2 * Real.goldenRatio) : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [Real.one_lt_goldenRatio]
  rw [regular3, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1,
    ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2.2]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (riemannZeta_ne_zero_of_real_pos (by positivity)
            (ne_of_lt hsmall))
          (riemannZeta_ne_zero_of_real_pos (by norm_num) (by norm_num)))
        (inv_ne_zero riemannZeta_golden_auxiliary_ne_zero))
      (riemannZeta_ne_zero_of_one_le_re
        (by simpa only [Complex.ofReal_re] using numeric_facts.2.2.2.2.2.le)))
    (by
      change thirdG (((1 / (2 * Real.goldenRatio ^ 3) : ℝ) : ℂ)) ≠ 0
      exact thirdG_real_ne_zero
        (1 / (2 * Real.goldenRatio ^ 3)) numeric_facts.2.1)

private lemma zero_at_z2 :
    MeromorphicAt thirdGerm z2 ∧
      meromorphicOrderAt thirdGerm z2 = (1 : ℤ) := by
  have hz := inverse_zeta_simple_zero
    (scale_ne_zero _ (by positivity : (0 : ℝ) < 2 * Real.goldenRatio ^ 2))
    transport_identities.2.2.1 regular2_analytic regular2_ne_zero
  have heq : thirdGerm = fun s =>
      (riemannZeta (doublePhiSq * s))⁻¹ * regular2 s := by
    funext s
    simp only [thirdGerm, regular2]
    ring
  rw [heq]
  exact hz

private lemma zero_at_z3 :
    MeromorphicAt thirdGerm z3 ∧
      meromorphicOrderAt thirdGerm z3 = (1 : ℤ) := by
  have hz := inverse_zeta_simple_zero
    (scale_ne_zero _ (by positivity : (0 : ℝ) < 2 * Real.goldenRatio ^ 3))
    transport_identities.2.2.2.2.2.2.2.2.1 regular3_analytic regular3_ne_zero
  have heq : thirdGerm = fun s =>
      (riemannZeta (doublePhiCub * s))⁻¹ * regular3 s := by
    funext s
    simp only [thirdGerm, regular3]
    ring
  rw [heq]
  exact hz

private lemma structural_numeric_check :
    (0 : ℝ) < 1 / (2 * Real.goldenRatio ^ 2) ∧
      (0 : ℝ) < 1 / (2 * Real.goldenRatio ^ 3) ∧
      ((1 / (2 * Real.goldenRatio ^ 2) : ℝ) ≠
        1 / (2 * Real.goldenRatio ^ 3)) := by
  refine ⟨by positivity, by positivity, ?_⟩
  intro h
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi2ne : Real.goldenRatio ^ 2 ≠ 0 := hphi2.ne'
  field_simp [Real.goldenRatio_ne_zero, hphi2ne] at h
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 5]

/-- In the displayed third-order continuation, the reciprocal zeta factors
at scales `2 * phi^2` and `2 * phi^3` create genuine simple zeros at their
respective structural points. -/
theorem golden_germ_third_order_structural_zeros :
    let Kp : ℂ → Nat.Primes → ℂ := fun s p =>
      let x := (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
      let y := (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : ℂ → ℂ := fun s => ∏' p : Nat.Primes, Kp s p
    let F3 : ℂ → ℂ := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : ℝ) : ℂ) * s) *
        (riemannZeta (((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ) * s))⁻¹ *
        ((riemannZeta (((2 * Real.goldenRatio ^ 3 : ℝ) : ℂ) * s))⁻¹ *
          riemannZeta
            ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : ℝ) : ℂ) * s)) *
          G3 s)
    let z2 : ℂ := ((1 / (2 * Real.goldenRatio ^ 2) : ℝ) : ℂ)
    let z3 : ℂ := ((1 / (2 * Real.goldenRatio ^ 3) : ℝ) : ℂ)
    MeromorphicAt F3 z2 ∧ meromorphicOrderAt F3 z2 = (1 : ℤ) ∧
      MeromorphicAt F3 z3 ∧ meromorphicOrderAt F3 z3 = (1 : ℤ) := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  change MeromorphicAt thirdGerm z2 ∧
    meromorphicOrderAt thirdGerm z2 = (1 : ℤ) ∧
    MeromorphicAt thirdGerm z3 ∧
    meromorphicOrderAt thirdGerm z3 = (1 : ℤ)
  exact ⟨zero_at_z2.1, zero_at_z2.2, zero_at_z3.1, zero_at_z3.2⟩

#print axioms golden_germ_third_order_structural_zeros

end

end D5.S3.Analytic.Isolation.GoldenGermThirdOrderStructuralZeros
