/- GID: D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderRealAxisSign
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermSecondOrderRealAxisSign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The second-order golden continuation is negative on its real inter-boundary interval. -/

import D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
import D5.S3.Analytic.Regularity.GoldenGermSecondNormalizedFactorRegularity
import D5.S3.Analytic.Isolation.GoldenAuxiliaryZetaNonzero
import D5.S3.Analytic.EulerGerm.GoldenGermRealAxisPositivity

/- Library-search audit trail (2026-09-03):
   * Repository searches found the frozen second-order factorization, boundary
     regularity, golden-point zeta nonvanishing, and first-order real-axis
     positivity, but no sign theorem on the target open interval.
   * The factorization publicly exposes the summable normalized deviation used
     below. The second normalized regularity theorem publicly gives
     AnalyticOnNhd on Re s > 1/phi^4 plus boundary facts, the first-order
     real-axis positivity covers the full convergence ray, and the auxiliary
     zeta theorem gives a single-point nonvanishing; none of these public APIs
     supplies the second-normalized real-factor positivity or the variable
     zeta sign on (0, 1) needed here, and their local arguments are private,
     so those two mechanisms are rebuilt from the canonical definitions
     instead of hidden behind wrappers.
   * Pinned Mathlib has no direct zeta-sign theorem on (0, 1). It supplies the
     eta continuation tools, positive-real zeta results above one, and the
     infinite-product positivity machinery used below.

   STOPPING JUSTIFICATION: this theorem determines only the real-axis sign of
   the displayed second-order continuation on one open interval. It asserts
   neither an O-5 estimate nor the Riemann hypothesis. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderRealAxisSign

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Filter Set Topology
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization

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
    exact (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le zero_lt_one (ha.trans hx.1)).ne'
      hs0).hasDerivWithinAt
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤
        radius * a ^ (-delta - 1) := by
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one (ha.trans hx.1)
    have hexp_nonpos : (-s.re - 1 : ℝ) ≤ 0 := by linarith
    have hbase : x ^ (-s.re - 1) ≤ a ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one ha) hx.1 hexp_nonpos
    have hexp : a ^ (-s.re - 1) ≤ a ^ (-delta - 1) :=
      Real.rpow_le_rpow_of_exponent_le ha (by linarith)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul hsnorm (hbase.trans hexp) (Real.rpow_nonneg (le_of_lt hxpos) _)
      ((norm_nonneg s).trans hsnorm)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Icc a b) (x := a) (y := b)
    (f := fun x : ℝ => (x : ℂ) ^ (-s))
    (f' := fun x : ℝ => (-s) * (x : ℂ) ^ (-s - 1))
    hderiv hbound (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  have hba : b - a = 1 := by norm_num [a, b]
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), hba, mul_one] at hmv
  have hmv' :
      ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ radius * a ^ (-delta - 1) := by
    rw [← norm_neg]
    simpa [a, b] using hmv
  simpa [etaPairTerm, a, b] using hmv'

private lemma etaPairTerm_summable {s : ℂ} (hs : 0 < s.re) :
    Summable fun n : ℕ => etaPairTerm n s := by
  let delta : ℝ := s.re / 2
  let radius : ℝ := ‖s‖
  have hdelta : 0 < delta := by simp [delta, hs]
  have hp : 1 < delta + 1 := by linarith
  have hseries : Summable (fun n : ℕ =>
      radius * ((n + 1 : ℕ) : ℝ) ^ (-delta - 1)) := by
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
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_comm, one_div] using
      hshift.mul_left radius
  apply Summable.of_norm_bounded hseries
  intro n
  have hraw := etaPairTerm_norm_le hdelta (s := s) (by simp [delta]; linarith)
    (show ‖s‖ ≤ radius by rfl) n
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
  have hmajorant :
      Summable (fun n : ℕ => radius * ((n + 1 : ℕ) : ℝ) ^ (-delta - 1)) := by
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
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_comm, one_div] using
      hshift.mul_left radius
  have hterm (n : ℕ) : DifferentiableOn ℂ (etaPairTerm n) U := by
    intro w hw
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
      ‖etaPairTerm n w‖ ≤ radius * ((n + 1 : ℕ) : ℝ) ^ (-delta - 1) := by
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
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (ne_zero_of_re_pos (zero_lt_one.trans hs))
  have hf : Summable f := by
    have h := Complex.summable_one_div_nat_cpow.mpr hs
    simpa only [f, Complex.cpow_neg, one_div] using h
  have htotal : ∑' n : ℕ, f n = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    apply tsum_congr
    intro n
    simp only [f, Complex.cpow_neg, one_div]
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
      ∑' n : ℕ, f (2 * n) =
          ∑' n : ℕ, (2 : ℂ) ^ (-s) * f n := by
        apply tsum_congr
        intro n
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
        ((2 : ℂ) ^ (-s) * riemannZeta s + ∑' n : ℕ, f (2 * n + 1)) -
          2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by ring
    _ = riemannZeta s - 2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by rw [hsplit]
    _ = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by ring

private lemma pairedEta_eq_zetaEtaFactor_upper_half_plane :
    Set.EqOn pairedEta zetaEtaFactor
      ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}) := by
  let U : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}
  have hU_open : IsOpen U := by
    exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_const continuous_im)
  have hU_preconnected : IsPreconnected U :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
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
      ((hasDerivAt_neg' s).const_cpow (Or.inl (by norm_num))).differentiableAt
    have hfactor : DifferentiableAt ℂ
        (fun w : ℂ => 1 - 2 * (2 : ℂ) ^ (-w)) s :=
      (differentiableAt_const (c := (1 : ℂ))).sub
        ((differentiableAt_const (c := (2 : ℂ))).mul hpow)
    exact (hfactor.mul (differentiableAt_riemannZeta hs1)).differentiableWithinAt
  have hz0 : (2 + I : ℂ) ∈ U := by
    constructor <;> norm_num
  have hnear : pairedEta =ᶠ[nhds (2 + I : ℂ)] zetaEtaFactor := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 + I : ℂ).re)] with s hs
    exact (pairedEta_eq_zeta_factor_of_one_lt_re hs).trans rfl
  change Set.EqOn pairedEta zetaEtaFactor U
  exact (hpaired_diff.analyticOnNhd hU_open).eqOn_of_preconnected_of_eventuallyEq
    (hfactor_diff.analyticOnNhd hU_open) hU_preconnected hz0 hnear

private lemma pairedEta_eq_zetaEtaFactor_of_real {x : ℝ}
    (hx : 0 < x) (hx1 : x ≠ 1) :
    pairedEta (x : ℂ) = zetaEtaFactor (x : ℂ) := by
  let seq : ℕ → ℂ := fun n => (x : ℂ) + I * (1 / ((n + 1 : ℕ) : ℂ))
  have hone_div : Tendsto
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat)
  have hseq : Tendsto seq atTop (nhds (x : ℂ)) := by
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
      apply div_pos
      · exact_mod_cast (Nat.zero_lt_succ n)
      · positivity
  have hseq_eq (n : ℕ) : pairedEta (seq n) = zetaEtaFactor (seq n) :=
    pairedEta_eq_zetaEtaFactor_upper_half_plane (hseq_mem n)
  have hpaired_cont : ContinuousAt pairedEta (x : ℂ) := by
    have hxmem : (x : ℂ) ∈ {s : ℂ | 0 < s.re} := by simpa using hx
    exact ((differentiableOn_pairedEta (x : ℂ) hxmem).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hxmem)).continuousAt
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
      (nhds (pairedEta (x : ℂ))) := by
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

private lemma pairedEta_of_real (x : ℝ) :
    pairedEta (x : ℂ) =
      ((∑' n : ℕ, realEtaPairTerm n x : ℝ) : ℂ) := by
  rw [pairedEta]
  calc
    (∑' n : ℕ, etaPairTerm n (x : ℂ)) =
        ∑' n : ℕ, (realEtaPairTerm n x : ℂ) := by
      exact tsum_congr fun n => etaPairTerm_of_real n x
    _ = ((∑' n : ℕ, realEtaPairTerm n x : ℝ) : ℂ) :=
      (Complex.ofReal_tsum _).symm

private lemma pairedEta_re_pos_of_real {x : ℝ} (hx : 0 < x) :
    0 < (pairedEta (x : ℂ)).re := by
  have hsummable := realEtaPairTerm_summable hx
  have hsum : 0 < ∑' n : ℕ, realEtaPairTerm n x :=
    hsummable.tsum_pos (fun n => (realEtaPairTerm_pos n hx).le) 0
      (realEtaPairTerm_pos 0 hx)
  rw [pairedEta_of_real]
  simpa using hsum

private theorem riemannZeta_real_negative_of_mem_Ioo {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).im = 0 ∧
      (riemannZeta (x : ℂ)).re < 0 := by
  let a : ℝ := 1 - 2 * (2 : ℝ) ^ (-x)
  have hhalf : (1 : ℝ) / 2 < (2 : ℝ) ^ (-x) := by
    have hpow := Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ) < 2) (by linarith : (-1 : ℝ) < -x)
    simpa [Real.rpow_neg_one] using hpow
  have ha : a < 0 := by
    dsimp [a]
    nlinarith
  have hpowComplex :
      (2 : ℂ) ^ (-(x : ℂ)) = (((2 : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg]
    exact (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (-x)).symm
  have hfactor :
      1 - 2 * (2 : ℂ) ^ (-(x : ℂ)) = (a : ℂ) := by
    rw [hpowComplex]
    norm_num [a]
  have heq := pairedEta_eq_zetaEtaFactor_of_real hx (ne_of_lt hx1)
  rw [zetaEtaFactor, hfactor, pairedEta_of_real] at heq
  have himEq := congrArg Complex.im heq
  simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    zero_mul] at himEq
  have him : (riemannZeta (x : ℂ)).im = 0 := by
    have hmul : a * (riemannZeta (x : ℂ)).im = 0 := by
      simpa only [add_zero] using himEq.symm
    exact (mul_eq_zero.mp hmul).resolve_left ha.ne
  have hreEq := congrArg Complex.re heq
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hreEq
  have hetaPos := pairedEta_re_pos_of_real hx
  have hetaPos' : 0 < ∑' n : ℕ, realEtaPairTerm n x := by
    rw [pairedEta_of_real] at hetaPos
    simpa using hetaPos
  constructor
  · exact him
  · nlinarith [hetaPos']

private theorem natCast_le_o5Beta (v : ℕ) : (v : ℝ) ≤ o5Beta v := by
  cases v with
  | zero => simp [o5_beta_zero]
  | succ v =>
      have hgrowth := o5_beta_growth (v + 1)
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hinv_pos : 0 < 1 / Real.goldenRatio :=
        one_div_pos.mpr Real.goldenRatio_pos
      push_cast at hgrowth ⊢
      nlinarith

private theorem real_local_factor_summable {sigma : ℝ} (hsigma : 0 < sigma)
    (p : Nat.Primes) :
    Summable (fun v : ℕ => (p : ℝ) ^ (-sigma * o5Beta v)) := by
  let q : ℝ := (p : ℝ) ^ (-sigma)
  have hp_one : (1 : ℝ) ≤ p := by exact_mod_cast p.prop.one_lt.le
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hq_nonneg : 0 ≤ q := Real.rpow_nonneg hp_pos.le _
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt) (neg_neg_of_pos hsigma)
  have hq_norm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
    exact hq_lt_one
  have hgeom : Summable (fun v : ℕ => q ^ v) :=
    summable_geometric_of_norm_lt_one hq_norm
  apply Summable.of_nonneg_of_le
    (fun _ => Real.rpow_nonneg hp_pos.le _) (fun v => ?_) hgeom
  have hexponent : -sigma * o5Beta v ≤ -sigma * (v : ℝ) := by
    nlinarith [natCast_le_o5Beta v]
  calc
    (p : ℝ) ^ (-sigma * o5Beta v) ≤
        (p : ℝ) ^ (-sigma * (v : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp_one hexponent
    _ = q ^ v := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]

private theorem real_local_factor_pos (sigma : ℝ) (hsigma : 0 < sigma)
    (p : Nat.Primes) :
    0 < ∑' v : ℕ, (p : ℝ) ^ (-sigma * o5Beta v) := by
  have hsum := real_local_factor_summable hsigma p
  refine hsum.tsum_pos (fun _ => Real.rpow_nonneg (by positivity) _) 0 ?_
  simp [o5_beta_zero]

private theorem ofReal_real_local_factor_eq (sigma : ℝ)
    (p : Nat.Primes) :
    ((∑' v : ℕ, (p : ℝ) ^ (-sigma * o5Beta v) : ℝ) : ℂ) =
      germLocalFactor (sigma : ℂ) p := by
  rw [germLocalFactor, Complex.ofReal_tsum]
  congr 1 with v
  rw [Complex.ofReal_cpow (by positivity)]
  congr 1
  norm_num

private noncomputable def realSecondNormalizedFactor
    (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  (1 - (p : ℝ) ^ (-sigma * Real.goldenRatio ^ 3)) *
    (1 + (p : ℝ) ^ (-sigma * Real.goldenRatio ^ 2))⁻¹ *
    ∑' v : ℕ, (p : ℝ) ^ (-sigma * o5Beta v)

private theorem realSecondNormalizedFactor_pos (sigma : ℝ)
    (hsigma : 0 < sigma) (p : Nat.Primes) :
    0 < realSecondNormalizedFactor sigma p := by
  have hcubed : (p : ℝ) ^ (-sigma * Real.goldenRatio ^ 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hsigma) (by positivity))
  have hsquared : 0 < (p : ℝ) ^ (-sigma * Real.goldenRatio ^ 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  unfold realSecondNormalizedFactor
  exact mul_pos
    (mul_pos (sub_pos.mpr hcubed) (inv_pos.mpr (by linarith)))
    (real_local_factor_pos sigma hsigma p)

private theorem ofReal_realSecondNormalizedFactor_eq (sigma : ℝ)
    (p : Nat.Primes) :
    (realSecondNormalizedFactor sigma p : ℂ) =
      (1 - (p : ℂ) ^
          (-(sigma : ℂ) *
            ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
        (1 + (p : ℂ) ^
          (-(sigma : ℂ) *
            ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
        germLocalFactor (sigma : ℂ) p := by
  unfold realSecondNormalizedFactor
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity),
    ofReal_real_local_factor_eq sigma p]
  congr 3 <;> norm_num

private theorem fourth_threshold_lt_third_threshold :
    1 / Real.goldenRatio ^ 4 < 1 / Real.goldenRatio ^ 3 := by
  have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
  have hphi3_lt_phi4 :
      Real.goldenRatio ^ 3 < Real.goldenRatio ^ 4 := by
    calc
      Real.goldenRatio ^ 3 <
          Real.goldenRatio ^ 3 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi3).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 4 := by ring
  exact one_div_lt_one_div_of_lt hphi3 hphi3_lt_phi4

private theorem realSecondNormalizedFactor_deviation_summable
    (sigma : ℝ) (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    Summable (fun p : Nat.Primes =>
      realSecondNormalizedFactor sigma p - 1) := by
  have hsecond := golden_germ_second_order_factorization
  dsimp only at hsecond
  have hcomplex := (hsecond.2 (sigma : ℂ)
    (by simpa using fourth_threshold_lt_third_threshold.trans hsigma)).of_norm
  apply Complex.summable_ofReal.mp
  refine hcomplex.congr fun p => ?_
  rw [Complex.ofReal_sub, Complex.ofReal_one,
    ofReal_realSecondNormalizedFactor_eq sigma p]

private theorem realSecondNormalizedFactor_multipliable
    (sigma : ℝ) (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    Multipliable (fun p : Nat.Primes => realSecondNormalizedFactor sigma p) := by
  have hdev := realSecondNormalizedFactor_deviation_summable sigma hsigma
  have hproduct := Real.multipliable_one_add_of_summable hdev
  refine hproduct.congr fun p => ?_
  ring

private theorem realSecondNormalizedProduct_pos
    (sigma : ℝ) (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    0 < ∏' p : Nat.Primes, realSecondNormalizedFactor sigma p := by
  have hsigmaPos : 0 < sigma := lt_trans (by positivity) hsigma
  let f : Nat.Primes → ℝ := realSecondNormalizedFactor sigma
  have hpos (p : Nat.Primes) : 0 < f p := by
    simpa [f] using realSecondNormalizedFactor_pos sigma hsigmaPos p
  have hdev : Summable (fun p : Nat.Primes => f p - 1) := by
    simpa [f] using realSecondNormalizedFactor_deviation_summable sigma hsigma
  have hmult : Multipliable f := by
    simpa [f] using realSecondNormalizedFactor_multipliable sigma hsigma
  have hnonzeroAux := tprod_one_add_ne_zero_of_summable
    (f := fun p : Nat.Primes => f p - 1)
    (fun p => by
      rw [show 1 + (f p - 1) = f p by ring]
      exact (hpos p).ne') hdev.norm
  have hfun : (fun p : Nat.Primes => 1 + (f p - 1)) = f := by
    funext p
    ring
  rw [hfun] at hnonzeroAux
  have hnonneg : 0 ≤ ∏' p : Nat.Primes, f p := by
    apply le_hasProd_of_le_prod hmult.hasProd
    intro t
    exact Finset.prod_nonneg fun p _ => (hpos p).le
  change 0 < ∏' p : Nat.Primes, f p
  exact lt_of_le_of_ne hnonneg (Ne.symm hnonzeroAux)

private theorem second_normalized_factor_real_axis_positive
    (sigma : ℝ) (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    let H : ℂ → ℂ := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
          (1 + (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
          germLocalFactor s p
    0 < (H (sigma : ℂ)).re ∧ (H (sigma : ℂ)).im = 0 := by
  dsimp only
  have hmap :=
    (realSecondNormalizedFactor_multipliable sigma hsigma).map_tprod
      Complex.ofRealHom Complex.continuous_ofReal
  change ((∏' p : Nat.Primes,
      realSecondNormalizedFactor sigma p : ℝ) : ℂ) =
        ∏' p : Nat.Primes,
          (realSecondNormalizedFactor sigma p : ℂ) at hmap
  have haxis :
      (∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-(sigma : ℂ) *
              ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
          (1 + (p : ℂ) ^
            (-(sigma : ℂ) *
              ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
          germLocalFactor (sigma : ℂ) p) =
        ((∏' p : Nat.Primes,
          realSecondNormalizedFactor sigma p : ℝ) : ℂ) := by
    calc
      _ = ∏' p : Nat.Primes,
          (realSecondNormalizedFactor sigma p : ℂ) :=
        tprod_congr fun p =>
          (ofReal_realSecondNormalizedFactor_eq sigma p).symm
      _ = _ := hmap.symm
  have hpos := realSecondNormalizedProduct_pos sigma hsigma
  constructor
  · rw [haxis, Complex.ofReal_re]
    exact hpos
  · rw [haxis, Complex.ofReal_im]

/-- Between the structural boundary one over phi cubed and the golden
boundary one over phi squared, the explicit second-order continuation is
real and negative. -/
theorem golden_germ_second_order_real_axis_negative
    (sigma : ℝ)
    (hlower : 1 / Real.goldenRatio ^ 3 < sigma)
    (hupper : sigma < 1 / Real.goldenRatio ^ 2) :
    let H : ℂ → ℂ := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
          (1 + (p : ℂ) ^
            (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
          germLocalFactor s p
    let F2 : ℂ → ℂ := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : ℝ) : ℂ) * s) *
        (riemannZeta
          (((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ) * s))⁻¹ *
        H s
    (F2 (sigma : ℂ)).im = 0 ∧
      (F2 (sigma : ℂ)).re < 0 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
  have hsigmaPos : 0 < sigma := lt_trans (by positivity) hlower
  have hsquaredLower :
      1 / Real.goldenRatio < Real.goldenRatio ^ 2 * sigma := by
    rw [div_lt_iff₀ hphi]
    have hcleared := (div_lt_iff₀ hphi3).mp hlower
    calc
      1 < sigma * Real.goldenRatio ^ 3 := hcleared
      _ = Real.goldenRatio ^ 2 * sigma * Real.goldenRatio := by ring
  have hsquaredUpper : Real.goldenRatio ^ 2 * sigma < 1 := by
    have hcleared := (lt_div_iff₀ hphi2).mp hupper
    nlinarith
  have hsquaredPos : 0 < Real.goldenRatio ^ 2 * sigma :=
    mul_pos hphi2 hsigmaPos
  have hzetaSquared := riemannZeta_real_negative_of_mem_Ioo
    hsquaredPos hsquaredUpper
  have hcubedDomain : 1 < Real.goldenRatio ^ 3 * sigma := by
    have hcleared := (div_lt_iff₀ hphi3).mp hlower
    nlinarith
  have hzetaCubedRe :
      0 < (riemannZeta
        (((Real.goldenRatio ^ 3 : ℝ) : ℂ) *
          (sigma : ℂ))).re := by
    simpa only [Complex.ofReal_mul] using
      riemannZeta_re_pos_of_one_lt hcubedDomain
  have hzetaCubedIm :
      (riemannZeta
        (((Real.goldenRatio ^ 3 : ℝ) : ℂ) *
          (sigma : ℂ))).im = 0 := by
    simpa only [Complex.ofReal_mul] using
      riemannZeta_im_eq_zero_of_one_lt hcubedDomain
  have htwoOverPhi : 1 < 2 * (1 / Real.goldenRatio) := by
    rw [show 2 * (1 / Real.goldenRatio) =
      2 / Real.goldenRatio by ring, lt_div_iff₀ hphi]
    simpa using Real.goldenRatio_lt_two
  have hdoubleDomain : 1 < 2 * Real.goldenRatio ^ 2 * sigma := by
    nlinarith
  let zdouble : ℂ := riemannZeta
    (((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ) * (sigma : ℂ))
  have hzetaDoubleRe : 0 < zdouble.re := by
    dsimp [zdouble]
    simpa only [Complex.ofReal_mul] using
      riemannZeta_re_pos_of_one_lt hdoubleDomain
  have hzetaDoubleIm : zdouble.im = 0 := by
    dsimp [zdouble]
    simpa only [Complex.ofReal_mul] using
      riemannZeta_im_eq_zero_of_one_lt hdoubleDomain
  have hzetaDoubleReal : zdouble = (zdouble.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hzetaDoubleIm
  have hreciprocalRe : 0 < (zdouble⁻¹).re := by
    rw [hzetaDoubleReal, ← Complex.ofReal_inv, Complex.ofReal_re]
    exact inv_pos.mpr hzetaDoubleRe
  have hreciprocalIm : (zdouble⁻¹).im = 0 := by
    rw [hzetaDoubleReal, ← Complex.ofReal_inv, Complex.ofReal_im]
  have hreciprocalRe' :
      0 < (riemannZeta
        (((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ) *
          (sigma : ℂ)))⁻¹.re := by
    simpa [zdouble] using hreciprocalRe
  have hreciprocalIm' :
      (riemannZeta
        (((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ) *
          (sigma : ℂ)))⁻¹.im = 0 := by
    simpa [zdouble] using hreciprocalIm
  have hnormalized := second_normalized_factor_real_axis_positive sigma hlower
  have hzetaSquared' :
      (riemannZeta
        (((Real.goldenRatio ^ 2 : ℝ) : ℂ) *
          (sigma : ℂ))).im = 0 ∧
      (riemannZeta
        (((Real.goldenRatio ^ 2 : ℝ) : ℂ) *
          (sigma : ℂ))).re < 0 := by
    simpa only [Complex.ofReal_mul] using hzetaSquared
  change
    (riemannZeta
          (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * (sigma : ℂ)) *
        riemannZeta
          (((Real.goldenRatio ^ 3 : ℝ) : ℂ) * (sigma : ℂ)) *
        zdouble⁻¹ *
        (∏' p : Nat.Primes,
          (1 - (p : ℂ) ^
              (-(sigma : ℂ) *
                ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) *
            (1 + (p : ℂ) ^
              (-(sigma : ℂ) *
                ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ *
            germLocalFactor (sigma : ℂ) p)).im = 0 ∧ _
  constructor
  · simp only [Complex.mul_im, hzetaSquared'.1, hzetaCubedIm,
      hreciprocalIm, hnormalized.2]
    ring
  · simp only [Complex.mul_re, Complex.mul_im, hzetaSquared'.1,
      hzetaCubedIm, hreciprocalIm', hnormalized.2, mul_zero, sub_zero,
      zero_mul, add_zero]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos hzetaSquared'.2 hzetaCubedRe)
          hreciprocalRe') hnormalized.1

private theorem golden_interval_numeric_check :
    1 / Real.goldenRatio ^ 3 < (1 / 3 : ℝ) ∧
      (1 / 3 : ℝ) < 1 / Real.goldenRatio ^ 2 := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
  constructor <;> field_simp <;> nlinarith

#print axioms golden_germ_second_order_real_axis_negative

end

end D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderRealAxisSign
