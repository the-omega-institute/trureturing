/- GID: D5/S3/Analytic/Isolation/RealUnitIntervalZetaNonvanishing
   generality: G
   mirror-B: D5/B/S3/Analytic/Isolation/RealUnitIntervalZetaNonvanishing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Riemann zeta is nonzero at every real point strictly between zero and one. -/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Library-search audit trail (2026-09-03):
* Pinned Mathlib searches for `riemannZeta_ne_zero`, `riemannZeta_neg`,
  `dirichletEta`, `LSeries`, and the zeta series identities found the public
  half-plane nonvanishing theorems and the Dirichlet series for `re s > 1`,
  but no theorem excluding real zeros for `0 < s < 1`.
* The D5 tree has a private generic proof inside
  `GoldenAuxiliaryZetaNonzero`; its only public theorem is the specialization
  at the golden auxiliary point. To avoid a second named eta API, all eta
  objects and supporting facts below are local to the one public theorem.
* The proof pairs adjacent terms of the alternating Dirichlet series, proves
  local uniform convergence for positive real part, identifies the series
  with the eta multiple of zeta by analytic continuation, and uses strict
  positivity of every real pair.
-/

open Complex Filter Set Topology

namespace D5.S3.Analytic.Isolation.RealUnitIntervalZetaNonvanishing

noncomputable section

/-- Riemann zeta has no real zero in the open unit interval. -/
theorem riemannZeta_ne_zero_on_real_unit_interval :
    ∀ sigma : ℝ, 0 < sigma → sigma < 1 → riemannZeta sigma ≠ 0 := by
  let etaPairTerm : ℕ → ℂ → ℂ := fun n s =>
    (((2 * n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) -
      (((2 * n + 2 : ℕ) : ℝ) : ℂ) ^ (-s)
  let pairedEta : ℂ → ℂ := fun s => ∑' n : ℕ, etaPairTerm n s
  let realEtaPairTerm : ℕ → ℝ → ℝ := fun n x =>
    ((2 * n + 1 : ℕ) : ℝ) ^ (-x) - ((2 * n + 2 : ℕ) : ℝ) ^ (-x)
  let zetaEtaFactor : ℂ → ℂ := fun s =>
    (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s
  have etaPairTerm_norm_le {delta radius : ℝ} (hdelta : 0 < delta)
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
  have etaPairTerm_summable {s : ℂ} (hs : 0 < s.re) :
      Summable fun n : ℕ => etaPairTerm n s := by
    let delta : ℝ := s.re / 2
    let radius : ℝ := ‖s‖
    have hdelta : 0 < delta := by simp [delta, hs]
    have hp : 1 < delta + 1 := by linarith
    have hseries : Summable (fun n : ℕ => radius * ((n + 1 : ℕ) : ℝ) ^ (-delta - 1)) := by
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
  have differentiableOn_pairedEta :
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
      dsimp [etaPairTerm]
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
    exact ((hdiff z hzU).differentiableAt (hU_open.mem_nhds hzU)).differentiableWithinAt
  have pairedEta_eq_zeta_factor_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
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
    have heven : ∑' n : ℕ, f (2 * n) = (2 : ℂ) ^ (-s) * riemannZeta s := by
      calc
        ∑' n : ℕ, f (2 * n) = ∑' n : ℕ, (2 : ℂ) ^ (-s) * f n := by
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
    have heven_shift : ∑' n : ℕ, f (2 * n + 2) = ∑' n : ℕ, f (2 * n) := by
      have h := heven_summable.tsum_eq_zero_add
      rw [hzero, zero_add] at h
      simpa only [Nat.mul_add, Nat.mul_one] using h.symm
    have hsplit := tsum_even_add_odd heven_summable hodd_summable
    rw [htotal, heven] at hsplit
    dsimp [pairedEta]
    change (∑' n : ℕ, (f (2 * n + 1) - f (2 * n + 2))) = _
    rw [hodd_summable.tsum_sub heven_shift_summable, heven_shift, heven]
    calc
      (∑' n : ℕ, f (2 * n + 1)) - (2 : ℂ) ^ (-s) * riemannZeta s =
          ((2 : ℂ) ^ (-s) * riemannZeta s + ∑' n : ℕ, f (2 * n + 1)) -
            2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by ring
      _ = riemannZeta s - 2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by rw [hsplit]
      _ = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by ring
  have pairedEta_eq_zetaEtaFactor_upper_half_plane :
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
    have hnear : pairedEta =ᶠ[𝓝 (2 + I : ℂ)] zetaEtaFactor := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num :
          (1 : ℝ) < (2 + I : ℂ).re)] with s hs
      exact (pairedEta_eq_zeta_factor_of_one_lt_re hs).trans rfl
    change Set.EqOn pairedEta zetaEtaFactor U
    exact (hpaired_diff.analyticOnNhd hU_open).eqOn_of_preconnected_of_eventuallyEq
      (hfactor_diff.analyticOnNhd hU_open) hU_preconnected hz0 hnear
  have pairedEta_eq_zetaEtaFactor_of_real {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
      pairedEta (x : ℂ) = zetaEtaFactor (x : ℂ) := by
    let seq : ℕ → ℂ := fun n => (x : ℂ) + I * (1 / ((n + 1 : ℕ) : ℂ))
    have hone_div : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
    have hseq : Tendsto seq atTop (𝓝 (x : ℂ)) := by
      simpa only [seq, mul_zero, add_zero] using
        tendsto_const_nhds.add (tendsto_const_nhds.mul hone_div)
    have hseq_mem (n : ℕ) : seq n ∈ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}) := by
      constructor
      · simp [seq, hx]
      · change 0 < (seq n).im
        have him : (seq n).im = (((n + 1 : ℕ) : ℂ)⁻¹).re := by
          simp only [seq, add_im, ofReal_im, zero_add, mul_im, I_re, I_im,
            zero_mul, one_mul, one_div]
        rw [him]
        rw [inv_re, normSq_natCast]
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
      have hfactor : DifferentiableAt ℂ (fun w : ℂ => 1 - 2 * (2 : ℂ) ^ (-w)) (x : ℂ) :=
        (differentiableAt_const (c := (1 : ℂ))).sub
          ((differentiableAt_const (c := (2 : ℂ))).mul hpow)
      exact (hfactor.mul (differentiableAt_riemannZeta hx1c)).continuousAt
    have hleft := hpaired_cont.tendsto.comp hseq
    have hright := hfactor_cont.tendsto.comp hseq
    have hleft' : Tendsto (zetaEtaFactor ∘ seq) atTop (𝓝 (pairedEta (x : ℂ))) := by
      apply hleft.congr'
      exact Eventually.of_forall hseq_eq
    exact tendsto_nhds_unique hleft' hright
  have etaPairTerm_of_real (n : ℕ) (x : ℝ) :
      etaPairTerm n (x : ℂ) = (realEtaPairTerm n x : ℂ) := by
    dsimp [etaPairTerm, realEtaPairTerm]
    change
      ((((2 * n + 1 : ℕ) : ℝ) : ℂ) ^ (-(x : ℂ)) -
          (((2 * n + 2 : ℕ) : ℝ) : ℂ) ^ (-(x : ℂ))) =
        (((((2 * n + 1 : ℕ) : ℝ) ^ (-x) -
          ((2 * n + 2 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ))
    rw [← Complex.ofReal_neg]
    rw [← Complex.ofReal_cpow (by positivity) (-x),
      ← Complex.ofReal_cpow (by positivity) (-x)]
    exact (Complex.ofReal_sub _ _).symm
  have realEtaPairTerm_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
      0 < realEtaPairTerm n x := by
    dsimp [realEtaPairTerm]
    apply sub_pos.mpr
    exact Real.strictAntiOn_rpow_Ioi_of_exponent_neg (neg_lt_zero.mpr hx)
      (by change 0 < ((2 * n + 1 : ℕ) : ℝ); positivity)
      (by change 0 < ((2 * n + 2 : ℕ) : ℝ); positivity)
      (by exact_mod_cast (by omega : 2 * n + 1 < 2 * n + 2))
  have realEtaPairTerm_summable {x : ℝ} (hx : 0 < x) :
      Summable fun n : ℕ => realEtaPairTerm n x := by
    rw [← Complex.summable_ofReal]
    exact (etaPairTerm_summable (by simpa using hx)).congr fun n =>
      etaPairTerm_of_real n x
  have pairedEta_re_pos_of_real {x : ℝ} (hx : 0 < x) :
      0 < (pairedEta (x : ℂ)).re := by
    have hsummable := realEtaPairTerm_summable hx
    have hsum : 0 < ∑' n : ℕ, realEtaPairTerm n x :=
      hsummable.tsum_pos (fun n => (realEtaPairTerm_pos n hx).le) 0
        (realEtaPairTerm_pos 0 hx)
    have hpair : pairedEta (x : ℂ) = ((∑' n : ℕ, realEtaPairTerm n x : ℝ) : ℂ) := by
      dsimp [pairedEta]
      calc
        (∑' n : ℕ, etaPairTerm n (x : ℂ)) =
            ∑' n : ℕ, (realEtaPairTerm n x : ℂ) := by
              exact tsum_congr fun n => etaPairTerm_of_real n x
        _ = ((∑' n : ℕ, realEtaPairTerm n x : ℝ) : ℂ) :=
          (Complex.ofReal_tsum _).symm
    rw [hpair]
    simpa using hsum
  intro sigma hsigma hsigma_one
  have heta_pos := pairedEta_re_pos_of_real hsigma
  have heta_ne : pairedEta (sigma : ℂ) ≠ 0 := by
    intro heta_zero
    rw [heta_zero] at heta_pos
    norm_num at heta_pos
  intro hzeta
  apply heta_ne
  rw [pairedEta_eq_zetaEtaFactor_of_real hsigma (ne_of_lt hsigma_one)]
  dsimp [zetaEtaFactor]
  rw [hzeta, mul_zero]

#print axioms riemannZeta_ne_zero_on_real_unit_interval

end

end D5.S3.Analytic.Isolation.RealUnitIntervalZetaNonvanishing
