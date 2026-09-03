/- GID: D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/AlternatingZetaContinuation
   mirror-E: none(waiver:pure-mathlib-analytic-continuation-only)
   anchors: []
   digest: The alternating zeta series continues off one and excludes real critical-strip zeros. -/

import D5.S3.Weil.ZeroSum
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Filter Set Topology
open D5.S3.Weil.Convention D5.S3.Weil.ZeroSum

namespace D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation

noncomputable section

private def alternatingTerm (s : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * ((n + 1 : ℂ) ^ (-s))

private def etaPairTerm (n : ℕ) (s : ℂ) : ℂ :=
  (((2 * n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) -
    (((2 * n + 2 : ℕ) : ℝ) : ℂ) ^ (-s)

private noncomputable def pairedEta (s : ℂ) : ℂ :=
  ∑' n : ℕ, etaPairTerm n s

private noncomputable def zetaEtaFactor (s : ℂ) : ℂ :=
  (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s

private lemma alternatingTerm_pair (s : ℂ) (n : ℕ) :
    alternatingTerm s (2 * n) + alternatingTerm s (2 * n + 1) = etaPairTerm n s := by
  simp [alternatingTerm, etaPairTerm, pow_add]
  rw [show (2 * (n : ℂ) + 1 + 1) = 2 * (n : ℂ) + 2 by ring]
  rfl

private lemma alternating_sum_even (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N), alternatingTerm s n) =
      ∑ n ∈ Finset.range N, etaPairTerm n s := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      rw [add_assoc, alternatingTerm_pair]

private lemma alternating_sum_odd (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N + 1), alternatingTerm s n) =
      (∑ n ∈ Finset.range N, etaPairTerm n s) + alternatingTerm s (2 * N) := by
  rw [Finset.sum_range_succ, alternating_sum_even]

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
      ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ radius * a ^ (-delta - 1) := by
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
    have hfactor : DifferentiableAt ℂ (fun w : ℂ => 1 - 2 * (2 : ℂ) ^ (-w)) s :=
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

private lemma pairedEta_eq_zetaEtaFactor_lower_half_plane :
    Set.EqOn pairedEta zetaEtaFactor
      ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0}) := by
  let U : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0}
  have hU_open : IsOpen U := by
    exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_im continuous_const)
  have hU_preconnected : IsPreconnected U :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hpaired_diff : DifferentiableOn ℂ pairedEta U :=
    differentiableOn_pairedEta.mono inter_subset_left
  have hfactor_diff : DifferentiableOn ℂ zetaEtaFactor U := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      change 0 < (1 : ℂ).re ∧ (1 : ℂ).im < 0 at hs
      norm_num at hs
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (-w)) s :=
      ((hasDerivAt_neg' s).const_cpow (Or.inl (by norm_num))).differentiableAt
    have hfactor : DifferentiableAt ℂ (fun w : ℂ => 1 - 2 * (2 : ℂ) ^ (-w)) s :=
      (differentiableAt_const (c := (1 : ℂ))).sub
        ((differentiableAt_const (c := (2 : ℂ))).mul hpow)
    exact (hfactor.mul (differentiableAt_riemannZeta hs1)).differentiableWithinAt
  have hz0 : (2 - I : ℂ) ∈ U := by
    constructor <;> norm_num
  have hnear : pairedEta =ᶠ[nhds (2 - I : ℂ)] zetaEtaFactor := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 - I : ℂ).re)] with s hs
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
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
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
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (-w)) (x : ℂ) :=
      ((hasDerivAt_neg' (x : ℂ)).const_cpow (Or.inl (by norm_num))).differentiableAt
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

private lemma alternatingTerm_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (alternatingTerm s) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
  have h' := (Filter.tendsto_add_atTop_iff_nat 1).2 h
  convert h' using 1
  funext n
  rw [alternatingTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    show (n : ℂ) + 1 = ((((n + 1 : ℕ) : ℝ) : ℂ)) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

private lemma tendsto_alternating_partialSums_pairedEta (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, alternatingTerm s n)
      atTop (nhds (pairedEta s)) := by
  have hpair := (etaPairTerm_summable hs).hasSum.tendsto_sum_nat
  have hterm := alternatingTerm_tendsto_zero hs
  rw [Metric.tendsto_atTop] at hpair hterm ⊢
  intro ε hε
  obtain ⟨K₁, hK₁⟩ := hpair (ε / 2) (half_pos hε)
  obtain ⟨K₂, hK₂⟩ := hterm (ε / 2) (half_pos hε)
  refine ⟨2 * max K₁ K₂, ?_⟩
  intro N hN
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hk : max K₁ K₂ ≤ k := by omega
    rw [alternating_sum_even]
    exact (hK₁ k (le_trans (le_max_left _ _) hk)).trans (by linarith)
  · have hk : max K₁ K₂ ≤ k := by omega
    have hk₂ : K₂ ≤ 2 * k := by omega
    rw [alternating_sum_odd]
    calc
      dist ((∑ n ∈ Finset.range k, etaPairTerm n s) + alternatingTerm s (2 * k))
          (pairedEta s) ≤
          dist (∑ n ∈ Finset.range k, etaPairTerm n s) (pairedEta s) +
            dist (alternatingTerm s (2 * k)) 0 := by
              simpa only [add_zero] using
                (dist_add_add_le (∑ n ∈ Finset.range k, etaPairTerm n s)
                  (alternatingTerm s (2 * k)) (pairedEta s) 0)
      _ < ε / 2 + ε / 2 := add_lt_add
        (hK₁ k (le_trans (le_max_left _ _) hk))
        (hK₂ (2 * k) hk₂)
      _ = ε := by ring

private lemma pairedEta_eq_zetaEtaFactor {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    pairedEta s = zetaEtaFactor s := by
  rcases lt_trichotomy s.im 0 with him | him | him
  · exact pairedEta_eq_zetaEtaFactor_lower_half_plane ⟨hs, him⟩
  · have hs_eq : s = (s.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hs_eq]
    apply pairedEta_eq_zetaEtaFactor_of_real (by simpa using hs)
    intro hre
    apply hs1
    rw [hs_eq, hre]
    norm_num
  · exact pairedEta_eq_zetaEtaFactor_upper_half_plane ⟨hs, him⟩

private lemma two_mul_two_cpow_neg (s : ℂ) :
    2 * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
  rw [show (1 : ℂ) - s = 1 + (-s) by ring,
    Complex.cpow_add 1 (-s) (by norm_num), Complex.cpow_one]

/-- Away from Mathlib's assigned value at the pole, the alternating Dirichlet
partial sums give the eta continuation throughout the positive half-plane. -/
theorem tendsto_alternating_partialSums_eta_of_ne_one
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Filter.Tendsto
      (fun N ↦ ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * ((n + 1 : ℂ) ^ (-s)))
      Filter.atTop
      (nhds ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)) := by
  have ht := tendsto_alternating_partialSums_pairedEta s hs
  rw [pairedEta_eq_zetaEtaFactor hs hs1, zetaEtaFactor,
    two_mul_two_cpow_neg] at ht
  simpa only [alternatingTerm] using ht

private def realEtaPairTerm (n : ℕ) (x : ℝ) : ℝ :=
  ((2 * n + 1 : ℕ) : ℝ) ^ (-x) - ((2 * n + 2 : ℕ) : ℝ) ^ (-x)

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

/-- The same formula without `s ≠ 1` is false at `s = 1`: the left side is
positive, while the vanishing eta factor makes the displayed right side zero. -/
theorem alternating_partialSums_eta_atom_fails_at_one :
    ¬ Filter.Tendsto
      (fun N ↦ ∑ n ∈ Finset.range N,
        (-1 : ℂ) ^ n * ((n + 1 : ℂ) ^ (-(1 : ℂ))))
      Filter.atTop
      (nhds ((1 - (2 : ℂ) ^ (1 - (1 : ℂ))) * riemannZeta (1 : ℂ))) := by
  intro hfalse
  have hrhs :
      (1 - (2 : ℂ) ^ (1 - (1 : ℂ))) * riemannZeta (1 : ℂ) = 0 := by
    norm_num [Complex.cpow_zero]
  rw [hrhs] at hfalse
  have htrue := tendsto_alternating_partialSums_pairedEta (1 : ℂ) (by norm_num)
  have heq : pairedEta (1 : ℂ) = 0 := by
    apply tendsto_nhds_unique htrue
    simpa only [alternatingTerm] using hfalse
  have hpos := pairedEta_re_pos_of_real (x := 1) (by norm_num)
  have hpos' : 0 < (pairedEta (1 : ℂ)).re := by
    norm_num at hpos ⊢
    exact hpos
  rw [heq] at hpos'
  norm_num at hpos'

/-- Riemann zeta has no real zero strictly between zero and one. -/
theorem riemannZeta_ne_zero_of_real_mem_Ioo
    (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  have heta := pairedEta_eq_zetaEtaFactor_of_real h0 (ne_of_lt h1)
  have hpos := pairedEta_re_pos_of_real h0
  intro hz
  rw [zetaEtaFactor, hz, mul_zero] at heta
  rw [heta] at hpos
  norm_num at hpos

/-- Every nontrivial zero stored by `ZeroData` has nonzero imaginary part. -/
theorem ZeroData.im_ne_zero
    (Z : ZeroData) (n : ℕ)
    (h : IsNontrivialZero (Z.zero n)) :
    (Z.zero n).im ≠ 0 := by
  intro him
  have hzreal : Z.zero n = ((Z.zero n).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  apply riemannZeta_ne_zero_of_real_mem_Ioo (Z.zero n).re h.2.1 h.2.2
  rw [← hzreal]
  simpa [classicalZeta] using h.1

example : 0 < (2 : ℂ).re ∧ (2 : ℂ) ≠ 1 := by norm_num

example : ∃ x : ℝ, 0 < x ∧ x < 1 := ⟨1 / 2, by norm_num⟩

example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example (Z : ZeroData) (n : ℕ) : IsNontrivialZero (Z.zero n) :=
  Z.zero_isNontrivial n

#print axioms tendsto_alternating_partialSums_eta_of_ne_one
#print axioms alternating_partialSums_eta_atom_fails_at_one
#print axioms riemannZeta_ne_zero_of_real_mem_Ioo
#print axioms ZeroData.im_ne_zero

end

end D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation
