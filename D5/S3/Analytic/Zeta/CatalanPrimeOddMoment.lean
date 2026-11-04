/- GID: D5/S3/Analytic/Zeta/CatalanPrimeOddMoment
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/CatalanPrimeOddMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime odd Dirichlet characters have nonzero weighted representative moments. -/

import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.Omega

/-!
Copyright 2026 Yao Xu. Licensed under Apache-2.0.
Source: https://github.com/cadamcat/catalan-lean4
Revision: 3dc9375da48d13751fd291f3ee0fda8fa18be56d.
This is a compatibility port of the eight-module CharacterSpecialValue closure,
not an independent proof or a claim of mathematical novelty. Source blocks below
retain their original declaration names. Changes: combine the closure, replace
its namespace/module visibility, and adapt only APIs required by the adopted pin.
Imports are restricted to the analytic modules and tactics needed by the closure.
The nonvanishing proof uses the unconditional L-value formula directly; the
redundant conditional nonvanishing forwarder is omitted. Identical license
texts are printed once, retaining the full source NOTICE and attribution chain.
The accompanying source archive retains LICENSE, NOTICE, THIRD_PARTY.md and the
referenced ClassFieldTheory LICENSE; no ClassFieldTheory mathematical file occurs
in this closure.

Retirement: when this repository's adopted Mathlib revision supplies equivalents
of hurwitzZeta_apply_zero_of_mem_Ioo, LFunction_zero_eq_neg_weighted_sum, and
odd_character_weighted_sum_ne_zero at the complete domains stated here, replace
the port and its consumers with direct applications of those declarations.
The test is against the repository's actual adopted pin, not an upstream event.
-/

set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace D5.S3.Analytic.Zeta.CatalanPrimeOddMoment

/- Source: Catalan/Stickelberger/CharacterCircle.lean (pinned revision above). -/
lemma exp_two_pi_norm (t : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
  norm_num [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

lemma exp_two_pi_ne_one (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ≠ 1 := by
  intro he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  have hi := congrArg Complex.im hn
  norm_num [Complex.mul_re, Complex.mul_im] at hi
  have htn : t = (n : ℝ) := by
    apply mul_left_cancel₀ (show (2 : ℝ) * Real.pi ≠ 0 by positivity)
    nlinarith only [hi]
  rw [htn] at ht
  have hn0 : (0 : ℤ) < n := by exact_mod_cast ht.1
  have hn1 : n < (1 : ℤ) := by exact_mod_cast ht.2
  omega

lemma exp_two_pi_pow (t : ℝ) (n : ℕ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) ^ n =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (n : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/- Source: Catalan/Stickelberger/DirichletTail.lean (pinned revision above). -/
lemma unit_circle_dirichlet_tail_bound
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (s : ℝ) (hs : 1 ≤ s)
    (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) :
    ‖∑ n ∈ Finset.Ico M N, z ^ n / (n : ℂ) ^ (s : ℂ)‖ ≤
      4 / ((M : ℝ) * ‖1 - z‖) := by
  classical
  by_cases hMNeq : M = N
  · subst N
    simp
    positivity
  have hMNlt : M < N := lt_of_le_of_ne hMN hMNeq
  have hden : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  let f : ℕ → ℝ := fun n => (n : ℝ) ^ (-s)
  let g : ℕ → ℂ := fun n => z ^ n
  have hterm (n : ℕ) (hn : 1 ≤ n) :
      z ^ n / (n : ℂ) ^ (s : ℂ) = (↑(f n) : ℂ) • g n := by
    have hnR : 0 ≤ (n : ℝ) := by positivity
    change z ^ n / (((n : ℝ) : ℂ) ^ (s : ℂ)) =
      (↑((n : ℝ) ^ (-s)) : ℂ) • z ^ n
    rw [← Complex.ofReal_cpow hnR, div_eq_mul_inv, ← Complex.ofReal_inv,
      ← Real.rpow_neg hnR]
    simp only [smul_eq_mul]
    ring
  have hsum_term :
      (∑ n ∈ Finset.Ico M N, z ^ n / (n : ℂ) ^ (s : ℂ)) =
        ∑ n ∈ Finset.Ico M N, f n • g n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hterm n (hM.trans (Finset.mem_Ico.mp hn).1)
  have hprefix (j : ℕ) :
      ‖∑ n ∈ Finset.range j, g n‖ ≤ 2 / ‖1 - z‖ := by
    have hgeom : (1 - z) * (∑ n ∈ Finset.range j, g n) = 1 - z ^ j := by
      calc
        (1 - z) * (∑ n ∈ Finset.range j, g n) =
            -((∑ n ∈ Finset.range j, g n) * (z - 1)) := by ring
        _ = -(z ^ j - 1) := by rw [geom_sum_mul]
        _ = 1 - z ^ j := by ring
    have hnum : ‖1 - z ^ j‖ ≤ 2 := by
      calc
        ‖1 - z ^ j‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ j‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_one, norm_pow, hz]; norm_num
    have hprod : ‖1 - z‖ * ‖∑ n ∈ Finset.range j, g n‖ = ‖1 - z ^ j‖ := by
      rw [← norm_mul, hgeom]
    apply (le_div_iff₀ hden).2
    nlinarith [hprod, hnum]
  have hf_le (n : ℕ) (hn : 1 ≤ n) : f (n + 1) ≤ f n := by
    dsimp [f]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · exact_mod_cast (Nat.le_succ n)
    · linarith
  have hvar :
      (∑ i ∈ Finset.Ico M (N - 1), (f i - f (i + 1))) = f M - f (N - 1) := by
    rw [Finset.sum_Ico_eq_sub _ (by omega)]
    rw [Finset.sum_range_sub' f, Finset.sum_range_sub' f]
    ring
  have hvar_abs :
      (∑ i ∈ Finset.Ico M (N - 1), |f (i + 1) - f i|) = f M - f (N - 1) := by
    rw [← hvar]
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (hf_le i
        (hM.trans (Finset.mem_Ico.mp hi).1))
  have hf_nonneg (n : ℕ) : 0 ≤ f n := by
    dsimp [f]
    exact Real.rpow_nonneg (by positivity) _
  have hvar_norm :
      (∑ i ∈ Finset.Ico M (N - 1),
        ‖(f (i + 1) - f i) • (∑ n ∈ Finset.range (i + 1), g n)‖) ≤
        (2 / ‖1 - z‖) * (f M - f (N - 1)) := by
    calc
      _ = ∑ i ∈ Finset.Ico M (N - 1),
          |f (i + 1) - f i| * ‖∑ n ∈ Finset.range (i + 1), g n‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i ∈ Finset.Ico M (N - 1),
          |f (i + 1) - f i| * (2 / ‖1 - z‖) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hprefix (i + 1)) (abs_nonneg _)
      _ = (2 / ‖1 - z‖) *
          (∑ i ∈ Finset.Ico M (N - 1), |f (i + 1) - f i|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (2 / ‖1 - z‖) * (f M - f (N - 1)) := by rw [hvar_abs]
  have hboundN : ‖f (N - 1) • (∑ n ∈ Finset.range N, g n)‖ ≤
      (2 / ‖1 - z‖) * f (N - 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf_nonneg _)]
    calc
      f (N - 1) * ‖∑ n ∈ Finset.range N, g n‖ ≤
          f (N - 1) * (2 / ‖1 - z‖) :=
        mul_le_mul_of_nonneg_left (hprefix N) (hf_nonneg _)
      _ = (2 / ‖1 - z‖) * f (N - 1) := by ring
  have hboundM : ‖f M • (∑ n ∈ Finset.range M, g n)‖ ≤
      (2 / ‖1 - z‖) * f M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf_nonneg _)]
    calc
      f M * ‖∑ n ∈ Finset.range M, g n‖ ≤
          f M * (2 / ‖1 - z‖) :=
        mul_le_mul_of_nonneg_left (hprefix M) (hf_nonneg _)
      _ = (2 / ‖1 - z‖) * f M := by ring
  have hnorm :
      ‖∑ n ∈ Finset.Ico M N, f n • g n‖ ≤
        (2 / ‖1 - z‖) * f (N - 1) +
          (2 / ‖1 - z‖) * f M +
          (2 / ‖1 - z‖) * (f M - f (N - 1)) := by
    rw [Finset.sum_Ico_by_parts f g hMNlt]
    calc
      ‖f (N - 1) • (∑ n ∈ Finset.range N, g n) -
          f M • (∑ n ∈ Finset.range M, g n) -
          ∑ i ∈ Finset.Ico M (N - 1),
            (f (i + 1) - f i) • (∑ n ∈ Finset.range (i + 1), g n)‖ ≤
        ‖f (N - 1) • (∑ n ∈ Finset.range N, g n) -
          f M • (∑ n ∈ Finset.range M, g n)‖ +
          ‖∑ i ∈ Finset.Ico M (N - 1),
            (f (i + 1) - f i) • (∑ n ∈ Finset.range (i + 1), g n)‖ :=
        norm_sub_le _ _
      _ ≤ (‖f (N - 1) • (∑ n ∈ Finset.range N, g n)‖ +
          ‖f M • (∑ n ∈ Finset.range M, g n)‖) +
          ‖∑ i ∈ Finset.Ico M (N - 1),
            (f (i + 1) - f i) • (∑ n ∈ Finset.range (i + 1), g n)‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ (2 / ‖1 - z‖) * f (N - 1) +
          (2 / ‖1 - z‖) * f M +
          (2 / ‖1 - z‖) * (f M - f (N - 1)) := by
        exact add_le_add (add_le_add hboundN hboundM)
          ((norm_sum_le _ _).trans hvar_norm)
  have hfM : f M ≤ 1 / (M : ℝ) := by
    dsimp [f]
    have hbase : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hexp : -s ≤ (-1 : ℝ) := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hbase hexp
    simpa only [Real.rpow_neg (by positivity : 0 ≤ (M : ℝ)), Real.rpow_one, one_div] using hpow
  rw [hsum_term]
  calc
    ‖∑ n ∈ Finset.Ico M N, f n • g n‖ ≤
        (2 / ‖1 - z‖) * f (N - 1) +
          (2 / ‖1 - z‖) * f M +
          (2 / ‖1 - z‖) * (f M - f (N - 1)) := hnorm
    _ = 2 * (2 / ‖1 - z‖) * f M := by ring
    _ ≤ 2 * (2 / ‖1 - z‖) * (1 / (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hfM (by positivity)
    _ = 4 / ((M : ℝ) * ‖1 - z‖) := by field_simp; ring

/- Source: Catalan/Stickelberger/CharacterBoundary.lean (pinned revision above). -/
lemma hurwitzZeta_zero_eq_sinZeta_one_div_pi
    (a : UnitAddCircle) (ha : a ≠ 0) :
    HurwitzZeta.hurwitzZeta a 0 = HurwitzZeta.sinZeta a 1 / (Real.pi : ℂ) := by
  have hone : ∀ n : ℕ, (1 : ℂ) ≠ -n := by
    intro n h
    have hr := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hfe := HurwitzZeta.hurwitzZetaOdd_one_sub a hone
  simp only [sub_self, Complex.Gamma_one, mul_one, Complex.sin_pi_div_two] at hfe
  rw [HurwitzZeta.hurwitzZeta, HurwitzZeta.hurwitzZetaEven_apply_zero, if_neg ha, zero_add,
    hfe, Complex.cpow_neg_one]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

lemma hurwitzZeta_zero_eq_sine_value_of_mem_Ioo
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.hurwitzZeta (t : UnitAddCircle) 0 =
      HurwitzZeta.sinZeta (t : UnitAddCircle) 1 / (Real.pi : ℂ) := by
  apply hurwitzZeta_zero_eq_sinZeta_one_div_pi
  intro h
  have hz := (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ)) ⟨ht.1.le, ht.2⟩).mp h
  exact ht.1.ne' hz

lemma cauchySeq_unit_circle_log_partial_sums
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n : ℂ) + 1)) := by
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hij
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound (N : ℕ) : ‖∑ n ∈ Finset.range N, z ^ (n + 1)‖ ≤ 2 / ‖z - 1‖ := by
    have he : (∑ n ∈ Finset.range N, z ^ (n + 1)) = z * ∑ n ∈ Finset.range N, z ^ n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => pow_succ' z n)
    rw [he, norm_mul, hz, one_mul, geom_sum_eq hz1, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    simpa only [norm_pow, hz, one_pow, norm_one, one_add_one_eq_two] using norm_sub_le (z ^ N) 1
  have hc := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded ht hbound
  convert hc using 1
  funext N
  apply Finset.sum_congr rfl
  intro n _
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

lemma tendsto_unit_circle_log_partial_sums
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ n / (n : ℂ))
      atTop (𝓝 (-Complex.log (1 - z))) := by
  have hc : CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ n / (n : ℂ)) := by
    rw [← cauchySeq_shift 1]
    simpa only [Finset.sum_range_succ', pow_zero, Nat.cast_zero, div_zero, add_zero,
      Nat.cast_add, Nat.cast_one] using cauchySeq_unit_circle_log_partial_sums z hz hz1
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  rw [Filter.tendsto_map'_iff] at hab
  have hre : z.re < 1 := by
    have hle : z.re ≤ 1 := hz ▸ Complex.re_le_norm z
    by_contra h
    have he : z.re = 1 := by linarith
    have hsq := Complex.sq_norm z
    rw [hz, Complex.normSq_apply, he] at hsq
    have hi : z.im = 0 := by nlinarith
    exact hz1 (Complex.ext he hi)
  have hslit : 1 - z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hre
  have hcont : Continuous (fun r : ℝ => 1 - (r : ℂ) * z) := by fun_prop
  have harg : Tendsto (fun r : ℝ => 1 - (r : ℂ) * z) (𝓝[<] (1 : ℝ)) (𝓝 (1 - z)) := by
    simpa only [Complex.ofReal_one, one_mul] using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlog := (harg.clog hslit).neg
  have hpositive : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hevent : (fun r : ℝ => ∑' n : ℕ, (z ^ n / (n : ℂ)) * (r : ℂ) ^ n) =ᶠ[𝓝[<] 1]
      (fun r : ℝ => -Complex.log (1 - (r : ℂ) * z)) := by
    filter_upwards [hpositive, self_mem_nhdsWithin] with r hr hr1
    have hn : ‖(r : ℂ) * z‖ < 1 := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one, Set.mem_Iio] using hr1
    calc
      (∑' n : ℕ, (z ^ n / (n : ℂ)) * (r : ℂ) ^ n) =
          ∑' n : ℕ, ((r : ℂ) * z) ^ n / (n : ℂ) := by
        apply tsum_congr
        intro n
        rw [mul_pow]
        ring
      _ = -Complex.log (1 - (r : ℂ) * z) := (Complex.hasSum_taylorSeries_neg_log hn).tsum_eq
  have heq : l = -Complex.log (1 - z) :=
    tendsto_nhds_unique hab (hlog.congr' hevent.symm)
  rwa [heq] at hl

/- Source: Catalan/Stickelberger/CharacterContinuity.lean (pinned revision above). -/
lemma tendsto_expZeta_one_partial_sums_of_tail_bound
    (htail : ∀ (z : ℂ), ‖z‖ = 1 → z ≠ 1 → ∀ (s : ℝ), 1 ≤ s →
      ∀ (M N : ℕ), 1 ≤ M → M ≤ N →
        ‖∑ n ∈ Finset.Ico M N, z ^ n / (n : ℂ) ^ (s : ℂ)‖ ≤
          4 / ((M : ℝ) * ‖1 - z‖))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (n : ℂ)) / (n : ℂ))
      atTop (𝓝 (HurwitzZeta.expZeta (t : UnitAddCircle) 1))
 := by
  let z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
  have hphase : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hz : ‖z‖ = 1 := by
    dsimp only [z]
    rw [hphase]
    exact Complex.norm_exp_ofReal_mul_I _
  have hz1 : z ≠ 1 := by
    intro he
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
    have hi := congrArg Complex.im hm
    norm_num [Complex.mul_im, Complex.mul_re] at hi
    have hmt : (m : ℝ) = t := by nlinarith [Real.pi_pos]
    have hm0 : (0 : ℤ) < m := by exact_mod_cast (show (0 : ℝ) < m by rw [hmt]; exact ht.1)
    have hm1 : m < (1 : ℤ) := by exact_mod_cast (show (m : ℝ) < 1 by rw [hmt]; exact ht.2)
    omega
  have htne : (t : UnitAddCircle) ≠ 0 := by
    intro he
    exact ht.1.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico
      (p := (1 : ℝ)) ⟨ht.1.le, ht.2⟩).mp he)
  have hpow (n : ℕ) : z ^ n =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (n : ℂ)) := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  let F (M : ℕ) (s : ℝ) : ℂ :=
    ∑ n ∈ Finset.range M, z ^ n / (n : ℂ) ^ (s : ℂ)
  let E (s : ℝ) : ℂ := HurwitzZeta.expZeta (t : UnitAddCircle) (s : ℂ)
  have hsum (s : ℝ) (hs : 1 < s) :
      HasSum (fun n : ℕ => z ^ n / (n : ℂ) ^ (s : ℂ)) (E s) := by
    have hh := HurwitzZeta.hasSum_expZeta_of_one_lt_re t (s := (s : ℂ))
      (by simpa only [Complex.ofReal_re] using hs)
    simpa only [← hpow] using hh
  have hbound (s : ℝ) (hs : 1 < s) (M : ℕ) (hM : 1 ≤ M) :
      ‖E s - F M s‖ ≤ 4 / ((M : ℝ) * ‖1 - z‖) := by
    have hlim : Tendsto (fun N : ℕ => ‖F N s - F M s‖) atTop (𝓝 ‖E s - F M s‖) :=
      ((hsum s hs).tendsto_sum_nat.sub_const (F M s)).norm
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop M] with N hMN
    dsimp only [F]
    rw [← Finset.sum_Ico_eq_sub _ hMN]
    exact htail z hz hz1 s hs.le M N hM hMN
  let s (j : ℕ) : ℝ := 1 + 1 / ((j : ℝ) + 1)
  have hs (j : ℕ) : 1 < s j := by
    dsimp only [s]
    exact lt_add_of_pos_right 1 (by positivity)
  have hs0 (j : ℕ) : (s j : ℂ) ≠ 0 := by
    exact_mod_cast (show s j ≠ 0 by have := hs j; linarith)
  have hsT : Tendsto s atTop (𝓝 (1 : ℝ)) := by
    have hh := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
    simpa only [add_zero] using hh
  have hsC : Tendsto (fun j : ℕ => (s j : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one, Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hsT
  have hET : Tendsto (fun j : ℕ => E (s j)) atTop
      (𝓝 (HurwitzZeta.expZeta (t : UnitAddCircle) 1)) :=
    (HurwitzZeta.differentiable_expZeta_of_ne_zero htne 1).continuousAt.tendsto.comp hsC
  have hFT (M : ℕ) : Tendsto (fun j : ℕ => F M (s j)) atTop
      (𝓝 (∑ n ∈ Finset.range M, z ^ n / (n : ℂ))) := by
    apply tendsto_finsetSum
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      have he : (fun j : ℕ => z ^ 0 / (0 : ℂ) ^ (s j : ℂ)) = fun _ => (0 : ℂ) := by
        funext j
        rw [Complex.zero_cpow (hs0 j), div_zero]
      simp only [Nat.cast_zero]
      rw [he]
      simpa only [div_zero] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      have hpT : Tendsto (fun j : ℕ => (n : ℂ) ^ (s j : ℂ)) atTop (𝓝 (n : ℂ)) := by
        simpa only [Complex.cpow_one, Function.comp_def] using
          (continuousAt_const_cpow (a := (n : ℂ)) (b := 1) hnC).tendsto.comp hsC
      exact tendsto_const_nhds.div hpT hnC
  have hbound1 (M : ℕ) (hM : 1 ≤ M) :
      ‖HurwitzZeta.expZeta (t : UnitAddCircle) 1 -
        ∑ n ∈ Finset.range M, z ^ n / (n : ℂ)‖ ≤ 4 / ((M : ℝ) * ‖1 - z‖) := by
    exact le_of_tendsto' ((hET.sub (hFT M)).norm) (fun j => hbound (s j) (hs j) M hM)
  have hCT : Tendsto (fun M : ℕ => 4 / ((M : ℝ) * ‖1 - z‖)) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun M : ℕ => 1 / (M : ℝ)) atTop (𝓝 (0 : ℝ))).const_mul (4 / ‖1 - z‖)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
  have hlimit : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ n / (n : ℂ)) atTop
      (𝓝 (HurwitzZeta.expZeta (t : UnitAddCircle) 1)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hCT).2 ε hε)
    refine ⟨max M 1, fun N hN => ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact (hbound1 N ((le_max_right M 1).trans hN)).trans_lt
      (hM N ((le_max_left M 1).trans hN))
  simpa only [hpow] using hlimit

/- Source: Catalan/Stickelberger/CharacterArgument.lean (pinned revision above). -/
lemma arg_one_sub_exp_two_pi (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Complex.arg (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) =
      Real.pi * t - Real.pi / 2 := by
  have hangle0 : 0 < Real.pi * t := mul_pos Real.pi_pos ht.1
  have hangleπ : Real.pi * t < Real.pi := by nlinarith [Real.pi_pos, ht.2]
  have hr : 0 < 2 * Real.sin (Real.pi * t) :=
    mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hangle0 hangleπ)
  have hstrip : Real.pi * t - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have he : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      ((2 * (Real.pi * t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hfactor : 1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      ((2 * Real.sin (Real.pi * t) : ℝ) : ℂ) *
        ((Real.cos (Real.pi * t - Real.pi / 2) : ℂ) +
          (Real.sin (Real.pi * t - Real.pi / 2) : ℂ) * Complex.I) := by
    rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, add_zero, sub_zero,
        Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
    · simp only [Complex.sub_im, Complex.one_im, Complex.add_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, mul_one, add_zero, zero_add, zero_sub,
        Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, Real.sin_two_mul]
      ring
  rw [hfactor]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_mul_cos_add_sin_mul_I hr hstrip

lemma log_one_sub_exp_two_pi_difference (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    -Complex.log (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) +
      Complex.log (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ))) =
      (2 * Complex.I) * ((Real.pi : ℂ) * ((1 / 2 : ℂ) - (t : ℂ))) := by
  have ht' : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I + -(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
    push_cast
    ring
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ)) =
      starRingEnd ℂ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) := by
    rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul, ← Complex.exp_conj]
    apply congrArg Complex.exp
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_mul]
  have hconj : 1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ)) =
      starRingEnd ℂ (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) := by
    rw [map_sub, map_one, hexp]
  have hnorm : ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ))‖ =
      ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ := by
    rw [hconj, Complex.norm_conj]
  have harg := arg_one_sub_exp_two_pi t ht
  have harg' := arg_one_sub_exp_two_pi (1 - t) ht'
  apply Complex.ext
  · simp only [Complex.add_re, Complex.neg_re, Complex.log_re, hnorm]
    norm_num
  · simp only [Complex.add_im, Complex.neg_im, Complex.log_im, harg, harg']
    norm_num
    ring

/- Source: Catalan/Stickelberger/CharacterLZero.lean (pinned revision above). -/
lemma LFunction_zero_ne_zero_of_prime_odd
    (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hodd : χ.Odd) :
    DirichletCharacter.LFunction χ 0 ≠ 0
 := by
  have hinv : χ⁻¹ ≠ 1 := fun h => hχ (inv_eq_one.mp h)
  have hprim : DirichletCharacter.IsPrimitive χ⁻¹ := by
    change DirichletCharacter.conductor χ⁻¹ = p
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp
        (DirichletCharacter.conductor_dvd_level χ⁻¹) with h | h
    · exact (hinv (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)).elim
    · exact h
  have hc1 : DirichletCharacter.completedLFunction χ⁻¹ 1 ≠ 0 := by
    intro hzero
    apply DirichletCharacter.LFunction_apply_one_ne_zero hinv
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 1
      (Or.inl one_ne_zero), hzero, zero_div]
  have hc0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
    intro hzero
    have hfe := hprim.completedLFunction_one_sub (0 : ℂ)
    simp only [sub_zero, inv_inv, hzero, mul_zero] at hfe
    exact hc1 hfe
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0
    (Or.inr (Fact.out : p.Prime).ne_one), hodd.gammaFactor_def,
    zero_add, Complex.Gammaℝ_one, div_one]
  exact hc0

/- Source: Catalan/Stickelberger/CharacterZeroBridge.lean (pinned revision above). -/
lemma LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero
    (hzero : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      HurwitzZeta.hurwitzZeta (t : UnitAddCircle) 0 = (1 / 2 : ℂ) - (t : ℂ))
    (p : ℕ) [hp : Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 =
      -(∑ a : ZMod p, (a.val : ℂ) * χ a) / (p : ℂ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  calc
    DirichletCharacter.LFunction χ 0 =
        ∑ a : ZMod p, χ a * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)) := by
      simp only [DirichletCharacter.LFunction, ZMod.LFunction, neg_zero,
        Complex.cpow_zero, one_mul]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = 0
      · simp only [ha, χ.map_zero' hp.out.ne_one, zero_mul]
      · have haR : (0 : ℝ) < a.val := by exact_mod_cast ZMod.val_pos.mpr ha
        have haLt : (a.val : ℝ) < p := by exact_mod_cast ZMod.val_lt a
        have ht : (a.val : ℝ) / p ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨div_pos haR hpR, (div_lt_one hpR).mpr haLt⟩
        rw [ZMod.toAddCircle_apply, hzero _ ht]
        simp only [Complex.ofReal_div, Complex.ofReal_natCast]
    _ = (∑ a : ZMod p, χ a) / 2 -
        (∑ a : ZMod p, (a.val : ℂ) * χ a) / (p : ℂ) := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = -(∑ a : ZMod p, (a.val : ℂ) * χ a) / (p : ℂ) := by
      rw [χ.sum_eq_zero_of_ne_one hχ]
      ring

/- Source: Catalan/Stickelberger/CharacterSpecialValue.lean (pinned revision above). -/
lemma tendsto_expZeta_one_partial_sums
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (n : ℂ)) / (n : ℂ))
      atTop (𝓝 (HurwitzZeta.expZeta (t : UnitAddCircle) 1)) :=
  tendsto_expZeta_one_partial_sums_of_tail_bound unit_circle_dirichlet_tail_bound t ht

lemma expZeta_one_eq_neg_log
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.expZeta (t : UnitAddCircle) 1 =
      -Complex.log (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) := by
  have hlog := tendsto_unit_circle_log_partial_sums
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))
    (exp_two_pi_norm t) (exp_two_pi_ne_one t ht)
  simp_rw [exp_two_pi_pow] at hlog
  exact tendsto_nhds_unique (tendsto_expZeta_one_partial_sums t ht) hlog

lemma sinZeta_one_eq_of_mem_Ioo
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.sinZeta (t : UnitAddCircle) 1 =
      (Real.pi : ℂ) * ((1 / 2 : ℂ) - (t : ℂ)) := by
  have ht' : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hneg : ((1 - t : ℝ) : UnitAddCircle) = -(t : UnitAddCircle) := by
    rw [AddCircle.coe_sub, show ((1 : ℝ) : UnitAddCircle) = 0 from AddCircle.coe_period (1 : ℝ)]
    exact zero_sub _
  rw [HurwitzZeta.sinZeta_eq, ← hneg, expZeta_one_eq_neg_log t ht,
    expZeta_one_eq_neg_log (1 - t) ht', sub_neg_eq_add,
    log_one_sub_exp_two_pi_difference t ht]
  have h2i : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact mul_div_cancel_left₀ _ h2i

lemma hurwitzZeta_apply_zero_of_mem_Ioo
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.hurwitzZeta (t : UnitAddCircle) 0 =
      (1 / 2 : ℂ) - (t : ℂ) := by
  rw [hurwitzZeta_zero_eq_sine_value_of_mem_Ioo t ht, sinZeta_one_eq_of_mem_Ioo t ht]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

lemma LFunction_zero_eq_neg_weighted_sum
    (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 =
      -(∑ a : ZMod p, (a.val : ℂ) * χ a) / (p : ℂ) :=
  LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero hurwitzZeta_apply_zero_of_mem_Ioo p χ hχ

lemma odd_character_weighted_sum_ne_zero
    (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) (hodd : χ.Odd) :
    (∑ a : ZMod p, (a.val : ℂ) * χ a) ≠ 0 := by
  intro hs
  have hL := LFunction_zero_eq_neg_weighted_sum p χ hχ
  rw [hs, neg_zero, zero_div] at hL
  exact LFunction_zero_ne_zero_of_prime_odd p χ hχ hodd hL

end D5.S3.Analytic.Zeta.CatalanPrimeOddMoment

/-!
The following verbatim source notices apply to this compatibility port.

Source LICENSE:
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

Source NOTICE:
catalan-lean4
Copyright 2026 Yao Xu

This project includes fixed source files from
n-yamaguchi-0729/ClassFieldTheory at commit
2930b56f4b5c33ddab9ef91a45a4811d6f7a683f.
They are modified for Lean v4.35.0-rc3 and the module system; each
changed file carries a notice, and THIRD_PARTY.md records the changes.
They remain under the Apache License 2.0; the upstream repository
provides no NOTICE file.
See vendor/ClassFieldTheory/LICENSE and THIRD_PARTY.md.

Source THIRD_PARTY.md:
# Third-party code and mathematical sources

## ClassFieldTheory

The `vendor/ClassFieldTheory/Lean4/` directory contains 871 Lean source files selected from [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/2930b56f4b5c33ddab9ef91a45a4811d6f7a683f), commit `2930b56f4b5c33ddab9ef91a45a4811d6f7a683f`.

The upstream authors retain credit for those files. Their [Apache-2.0 license](vendor/ClassFieldTheory/LICENSE) is included. The upstream repository has no NOTICE file. Its source files at `2930b56` carry no per-file copyright headers; the retained files, ported from upstream commit `7713795`, carry the upstream authors' headers from that commit.

## Modifications

The retained files use the Lean module system and the visibility declarations required by Lean `v4.35.0-rc3`. They were ported from upstream ClassFieldTheory commit `7713795234690681b4406ae198b07aa95e82716a`, which targets Lean `v4.35.0-rc2`, and updated for Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`. Each changed Lean file has a notice before its `module` header naming the port commit and the kind of change.

[SOURCES.json](vendor/ClassFieldTheory/SOURCES.json) records each file's original upstream commit and path, port commit and path, and reconstruction patch. The patch applies to the original vendored snapshot at project commit `c08bf727e7e0f773edd2f4777fd0d12152f44ed6`; its file hashes are checked against the recorded upstream source before reconstruction. [check_vendor.py](scripts/check_vendor.py) applies that patch and compares the reconstructed bytes with the retained files. The local directory README describes the package layout.

The fixed subset does not include every support module added or split out by the upstream port. To retain its 871 paths, the required fractional-ideal norm/factorization declarations, finite-place unramified normalization, and two principal-unit quotient helpers are merged into retained modules. The multiplicative induced-function module from the separate `ProCGroups` subtree is also inlined into the retained Herbrand module, so the Lake project has no fourth vendor library. These merges are recorded in the affected files' notices and the reconstruction patch.

## Mathlib and Lean

[Mathlib](https://github.com/leanprover-community/mathlib4/tree/c55e6e786f49471c72fbddbec5415808896aec1e) is used at commit `c55e6e786f49471c72fbddbec5415808896aec1e` under its Apache-2.0 license. Mathlib and its transitive packages are fetched using [lake-manifest.json](lake-manifest.json), rather than redistributed in this source tree. Their original licenses and notices remain in those packages.

Lean is selected by [lean-toolchain](lean-toolchain). Its compiler and runtime are installed separately.

## Mathematical references and source acknowledgments

The mathematical theorem is due to Preda Mihăilescu. Yuri Bilu's exposition supplies the principal presentation of the cyclotomic approach followed here; bibliographic references are in the [README](README.md#mathematical-references).

The source comments in [DigitValuation.lean](Catalan/Stickelberger/DigitValuation.lean) and [ClassReduction.lean](Catalan/Stickelberger/ClassReduction.lean) acknowledge the mathematical arguments in [xroblot/SKW](https://github.com/xroblot/SKW/tree/4db8676808a63d892a8f36ead11308ca8dd58520), fixed at commit `4db8676808a63d892a8f36ead11308ca8dd58520`. These acknowledgments are retained. No SKW package or source module is imported or vendored.

Source vendor/ClassFieldTheory/LICENSE is byte-identical to Source LICENSE
above (SHA-256 b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1).
The complete Apache-2.0 text above applies to both, without duplicate printing.
-/
