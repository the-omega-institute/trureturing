/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionBanksLeadingClosure
   generality: G
   mirror-B: none(waiver:private-implementation-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Private leading-block norm closure for the actual positive-composition branch. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionBoundary
import D5.S3.AnalyticClosure.Polylogarithm.CompositionContinuation
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingTransport
import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter Set Topology

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingClosure

open D5.S3.AnalyticClosure.Polylogarithm
open CompositionBoundary CompositionContinuation

local instance (p : Prop) : Decidable p := Classical.propDecidable p
open private inner_arc_decay from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
open private radial_div_uniform_bound from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksIntegralControl
open private polynomialPrimitive leading_remainder_integral_identity
  split_leading_ones from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingTransport
open private sourceWeight admissibleRemainder suffixConstant
  leadingOneRemainder from
  D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction

private def imaginaryPolynomial (P : Polynomial ℂ) : Polynomial ℝ :=
  P.sum fun n a ↦ Polynomial.monomial n a.im

private theorem polynomial_upper_pow_im_eventually_ge (P : Polynomial ℝ) (q ell : ℕ)
    (hq : 1 ≤ q) (hell : 1 ≤ ell) (hdegree : P.natDegree = q)
    (hlead : 0 < P.coeff q) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      c * T ^ (q * ell - 1) ≤ (((P.map Complex.ofRealHom).eval
        ((T : ℂ) + Real.pi * I)) ^ ell).im := by
  have imaginaryPolynomial_coeff : ∀ (P : Polynomial ℂ) (n : ℕ),
      (imaginaryPolynomial P).coeff n = (P.coeff n).im := by
    intro P n
    classical
    rw [imaginaryPolynomial, Polynomial.coeff_sum, Polynomial.sum_def]
    suffices P.coeff n = 0 → 0 = (P.coeff n).im by
      simpa [Polynomial.coeff_monomial, Polynomial.mem_support_iff] using this
    simp_all
  have imaginaryPolynomial_eval : ∀ (P : Polynomial ℂ) (x : ℝ),
      (imaginaryPolynomial P).eval x = (P.eval (x : ℂ)).im := by
    intro P x
    classical
    rw [imaginaryPolynomial, Polynomial.sum_def, Polynomial.eval_finsetSum,
      Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp only [Polynomial.eval_monomial]
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [Complex.mul_im]
    have hpow : ((x : ℂ) ^ n).re = x ^ n ∧ ((x : ℂ) ^ n).im = 0 := by
      have hpowcast : (x : ℂ) ^ n = (x ^ n : ℝ) := (Complex.ofReal_pow x n).symm
      exact ⟨(congrArg Complex.re hpowcast).trans (Complex.ofReal_re _),
        (congrArg Complex.im hpowcast).trans (Complex.ofReal_im _)⟩
    rw [hpow.1, hpow.2]
    ring
  let Q : Polynomial ℝ := P ^ ell
  let R : Polynomial ℝ := imaginaryPolynomial
    (Polynomial.taylor (Real.pi * I) (Q.map Complex.ofRealHom))
  have hqell : 1 ≤ q * ell := Nat.mul_pos (by omega) (by omega)
  have hQdegree : Q.natDegree = q * ell := by
    simp only [Q, Polynomial.natDegree_pow, hdegree, Nat.mul_comm]
  have hQlead : 0 < Q.coeff (q * ell) := by
    rw [← hQdegree, ← Polynomial.leadingCoeff,
      Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff, hdegree]
    positivity
  have hmapDegree : (Q.map Complex.ofRealHom).natDegree = q * ell := by
    simpa only [Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective] using hQdegree
  have hRcoeff : R.coeff (q * ell - 1) =
      (q * ell) * Real.pi * Q.coeff (q * ell) := by
    dsimp only [R]
    rw [imaginaryPolynomial_coeff, Polynomial.taylor_coeff]
    let H : Polynomial ℂ :=
      Polynomial.hasseDeriv (q * ell - 1) (Q.map Complex.ofRealHom)
    have hHdegree : H.natDegree ≤ 1 := by
      calc
        _ ≤ (Q.map Complex.ofRealHom).natDegree - (q * ell - 1) :=
          Polynomial.natDegree_hasseDeriv_le _ _
        _ = 1 := by rw [hmapDegree]; omega
    have hHdegreeTwo : H.natDegree < 2 := lt_of_le_of_lt hHdegree (by norm_num)
    change (H.eval (Real.pi * I)).im = _
    rw [Polynomial.eval_eq_sum_range' hHdegreeTwo]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    dsimp only [H]
    rw [Polynomial.hasseDeriv_coeff, Polynomial.hasseDeriv_coeff]
    simp only [zero_add]
    have hpred : q * ell - 1 + 1 = q * ell := by omega
    have hchoose : (q * ell).choose (q * ell - 1) = q * ell := by
      calc
        _ = (q * ell - 1 + 1).choose (q * ell - 1) := by rw [hpred]
        _ = q * ell - 1 + 1 := Nat.choose_succ_self_right (q * ell - 1)
        _ = q * ell := hpred
    rw [show 1 + (q * ell - 1) = q * ell by omega, Nat.choose_self, hchoose,
      Polynomial.coeff_map, Polynomial.coeff_map]
    push_cast
    norm_num [Complex.mul_re, Complex.mul_im]
    ring
  have hRdegree : R.natDegree = q * ell - 1 := by
    have htaylorDegree : (Polynomial.taylor (Real.pi * I)
        (Q.map Complex.ofRealHom)).natDegree = q * ell := by
      rw [Polynomial.natDegree_taylor]
      exact hmapDegree
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      dsimp only [R]
      rw [imaginaryPolynomial_coeff]
      by_cases hnq : n = q * ell
      · subst n
        rw [← hmapDegree, Polynomial.coeff_taylor_natDegree,
          Polynomial.leadingCoeff, Polynomial.coeff_map]
        simp
      · have hqn : q * ell < n := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (htaylorDegree.symm ▸ hqn)]
        simp
    · rw [hRcoeff]; positivity
  have hRlead : 0 < R.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hRdegree, hRcoeff]; positivity
  have hdenom : ∀ᶠ T : ℝ in atTop,
      R.leadingCoeff * T ^ R.natDegree ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact mul_ne_zero hRlead.ne' (pow_ne_zero _ hT.ne')
  have hratio : Tendsto
      (fun T : ℝ ↦ R.eval T / (R.leadingCoeff * T ^ R.natDegree))
      atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hdenom).mp R.isEquivalent_atTop_lead
  refine ⟨R.leadingCoeff / 2, half_pos hRlead, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hratio.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with T hT hhalf
  have hdenpos : 0 < R.leadingCoeff * T ^ R.natDegree := mul_pos hRlead (pow_pos hT _)
  have hlower : (1 / 2 : ℝ) * (R.leadingCoeff * T ^ R.natDegree) < R.eval T :=
    (lt_div_iff₀ hdenpos).mp hhalf
  have heval : R.eval T = (((P.map Complex.ofRealHom).eval
      ((T : ℂ) + Real.pi * I)) ^ ell).im := by
    rw [show R.eval T = ((Polynomial.taylor (Real.pi * I)
      (Q.map Complex.ofRealHom)).eval (T : ℂ)).im by
        exact imaginaryPolynomial_eval _ T]
    rw [Polynomial.taylor_eval]
    simp only [Q, Polynomial.map_pow, Polynomial.eval_pow]
  rw [hRdegree] at hlower
  rw [← heval]
  nlinarith

private theorem leading_one_upper_boundary_remainder_of_limit
    (q : ℕ) (suffix : List ℕ+) (ρ C : ℝ) (M : ℕ) (P : Polynomial ℝ)
    (t : ℝ) (value : ℂ) (ht : 0 < t) (htρ : t < ρ)
    (hbound : ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          (P.map Complex.ofRealHom).eval (-Complex.log w)‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M)
    (hlimit : Tendsto
      (fun w : ℂ ↦ CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - w))
      (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ))) (𝓝 value)) :
    ‖value - (P.map Complex.ofRealHom).eval
        ((-Real.log t : ℂ) + Real.pi * I)‖ ≤
      C * t * (1 + ‖(-Real.log t : ℂ) + Real.pi * I‖) ^ M := by
  let L : ℂ := (-Real.log t : ℂ) + Real.pi * I
  have hlog := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := -(t : ℂ)) (by simp [ht]) (by simp)
  have hneglog : Tendsto (fun w : ℂ ↦ -Complex.log w)
      (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ))) (𝓝 L) := by
    convert hlog.neg using 1
    simp [L, Real.norm_eq_abs, abs_of_pos ht, sub_eq_add_neg]
    ring
  have hpoly : Tendsto
      (fun w : ℂ ↦ (P.map Complex.ofRealHom).eval (-Complex.log w))
      (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ)))
      (𝓝 ((P.map Complex.ofRealHom).eval L)) :=
    (P.map Complex.ofRealHom).continuous.tendsto L |>.comp hneglog
  have herror : Tendsto
      (fun w : ℂ ↦ ‖CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
        (P.map Complex.ofRealHom).eval (-Complex.log w)‖)
      (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ)))
      (𝓝 ‖value - (P.map Complex.ofRealHom).eval L‖) :=
    (continuous_norm.tendsto _).comp (hlimit.sub hpoly)
  have hnorm : Tendsto (fun w : ℂ ↦ ‖w‖)
      (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ))) (𝓝 t) := by
    convert continuous_norm.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp [Real.norm_eq_abs, abs_of_pos ht]
  have hmajor : Tendsto
      (fun w : ℂ ↦ C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M)
      (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ)))
      (𝓝 (C * t * (1 + ‖L‖) ^ M)) := by
    exact (tendsto_const_nhds.mul hnorm |>.mul
      ((tendsto_const_nhds.add (continuous_norm.tendsto L |>.comp hneglog)).pow M))
  letI : NeBot (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ))) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [Complex.closure_setOfPred_im_lt]
      simp)
  apply le_of_tendsto_of_tendsto herror hmajor
  have hpositive : ∀ᶠ w : ℂ in 𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ)), 0 < ‖w‖ :=
    hnorm.eventually (Ioi_mem_nhds ht)
  have hsmall : ∀ᶠ w : ℂ in 𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ)), ‖w‖ < ρ :=
    hnorm.eventually (Iio_mem_nhds htρ)
  filter_upwards [self_mem_nhdsWithin, hpositive, hsmall] with w hw hw0 hwρ
  apply hbound w
  · rw [Complex.mem_slitPlane_iff]
    right
    exact ne_of_lt hw
  · exact hw0
  · exact hwρ

private theorem leading_one_upper_boundary_remainder_of_extension
    (q : ℕ) (suffix : List ℕ+) (ρ C : ℝ) (M : ℕ) (P : Polynomial ℝ)
    (t : ℝ) (center : ℂ) (r : ℝ) (extension : ℂ → ℂ)
    (ht : 0 < t) (htρ : t < ρ)
    (hbound : ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          (P.map Complex.ofRealHom).eval (-Complex.log w)‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M)
    (hx : (1 + (t : ℂ)) ∈ Metric.ball center r)
    (hextension : AnalyticOnNhd ℂ extension (Metric.ball center r))
    (heq : Set.EqOn extension
      (CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix))
      (Metric.ball center r ∩ {z : ℂ | 0 < z.im})) :
    ‖extension (1 + (t : ℂ)) - (P.map Complex.ofRealHom).eval
        ((-Real.log t : ℂ) + Real.pi * I)‖ ≤
      C * t * (1 + ‖(-Real.log t : ℂ) + Real.pi * I‖) ^ M := by
  have hmap : Tendsto (fun w : ℂ ↦ 1 - w)
      (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ))) (𝓝 (1 + (t : ℂ))) := by
    have hid : Tendsto (fun w : ℂ ↦ w)
        (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ))) (𝓝 (-(t : ℂ))) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_neg_eq_add] using tendsto_const_nhds.sub hid
  have hextensionLimit : Tendsto (fun w : ℂ ↦ extension (1 - w))
      (𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ)))
      (𝓝 (extension (1 + (t : ℂ)))) :=
    (hextension (1 + (t : ℂ)) hx).continuousAt.tendsto.comp hmap
  have hball : ∀ᶠ w : ℂ in 𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ)),
      1 - w ∈ Metric.ball center r :=
    hmap.eventually (Metric.isOpen_ball.mem_nhds hx)
  have hagree :
      (fun w : ℂ ↦ CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - w)) =ᶠ[
      𝓝[{w : ℂ | w.im < 0}] (-(t : ℂ))]
      (fun w : ℂ ↦ extension (1 - w)) := by
    filter_upwards [self_mem_nhdsWithin, hball] with w hw hwball
    exact (heq ⟨hwball, by simpa using hw⟩).symm
  exact leading_one_upper_boundary_remainder_of_limit q suffix ρ C M P t
    (extension (1 + (t : ℂ))) ht htρ hbound (hextensionLimit.congr' hagree.symm)

private theorem norm_pow_sub_pow_le (a b : ℂ) (ell : ℕ) (H : ℝ)
    (hH : 0 ≤ H) (ha : ‖a‖ ≤ H) (hb : ‖b‖ ≤ H) :
    ‖a ^ ell - b ^ ell‖ ≤ ell * ‖a - b‖ * H ^ (ell - 1) := by
  rw [← (Commute.all a b).mul_geom_sum₂ ell, norm_mul]
  calc
    ‖a - b‖ * ‖∑ i ∈ Finset.range ell, a ^ i * b ^ (ell - 1 - i)‖ ≤
        ‖a - b‖ * ∑ i ∈ Finset.range ell,
          ‖a ^ i * b ^ (ell - 1 - i)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ‖a - b‖ * ∑ _i ∈ Finset.range ell, H ^ (ell - 1) := by
      gcongr with i hi
      have hiell : i < ell := Finset.mem_range.mp hi
      rw [norm_mul, norm_pow, norm_pow]
      calc
        ‖a‖ ^ i * ‖b‖ ^ (ell - 1 - i) ≤
            H ^ i * H ^ (ell - 1 - i) := by gcongr
        _ = H ^ (ell - 1) := by
          rw [← pow_add]
          congr 1
          omega
    _ = ell * ‖a - b‖ * H ^ (ell - 1) := by
      simp [mul_assoc, mul_left_comm]

private theorem leading_one_upper_boundary_pow_remainder_of_extension
    (q : ℕ) (suffix : List ℕ+) (ell : ℕ) (ρ C : ℝ) (M : ℕ)
    (P : Polynomial ℝ) (t : ℝ) (center : ℂ) (r : ℝ) (extension : ℂ → ℂ)
    (ht : 0 < t) (htρ : t < ρ) (hC : 0 ≤ C)
    (hbound : ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          (P.map Complex.ofRealHom).eval (-Complex.log w)‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M)
    (hx : (1 + (t : ℂ)) ∈ Metric.ball center r)
    (hextension : AnalyticOnNhd ℂ extension (Metric.ball center r))
    (heq : Set.EqOn extension
      (CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix))
      (Metric.ball center r ∩ {z : ℂ | 0 < z.im})) :
    let L : ℂ := (-Real.log t : ℂ) + Real.pi * I
    let E : ℝ := C * t * (1 + ‖L‖) ^ M
    ‖extension (1 + (t : ℂ)) ^ ell -
        ((P.map Complex.ofRealHom).eval L) ^ ell‖ ≤
      ell * E * (‖(P.map Complex.ofRealHom).eval L‖ + E) ^ (ell - 1) := by
  dsimp only
  let a : ℂ := extension (1 + (t : ℂ))
  let b : ℂ := (P.map Complex.ofRealHom).eval
    ((-Real.log t : ℂ) + Real.pi * I)
  let E : ℝ := C * t *
    (1 + ‖(-Real.log t : ℂ) + Real.pi * I‖) ^ M
  have herror : ‖a - b‖ ≤ E := by
    exact leading_one_upper_boundary_remainder_of_extension q suffix ρ C M P t center r
      extension ht htρ hbound hx hextension heq
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have ha : ‖a‖ ≤ ‖b‖ + E := by
    calc
      ‖a‖ = ‖(a - b) + b‖ := by
        have haeq : a = (a - b) + b := by ring
        exact congrArg norm haeq
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le (a - b) b
      _ ≤ E + ‖b‖ := by gcongr
      _ = ‖b‖ + E := add_comm _ _
  have hb : ‖b‖ ≤ ‖b‖ + E := le_add_of_nonneg_right hE
  have hpower := norm_pow_sub_pow_le a b ell (‖b‖ + E)
    (add_nonneg (norm_nonneg b) hE) ha hb
  calc
    ‖extension (1 + (t : ℂ)) ^ ell -
        ((P.map Complex.ofRealHom).eval
          ((-Real.log t : ℂ) + Real.pi * I)) ^ ell‖ = ‖a ^ ell - b ^ ell‖ := by
          rfl
    _ ≤ ell * ‖a - b‖ * (‖b‖ + E) ^ (ell - 1) := hpower
    _ ≤ ell * E * (‖b‖ + E) ^ (ell - 1) := by gcongr

private theorem norm_neg_log_le_abs_log_norm_add_pi (w : ℂ) :
    ‖-Complex.log w‖ ≤ |Real.log ‖w‖| + Real.pi := by
  rw [norm_neg]
  calc
    ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖w‖| + |Complex.arg w| := by
      rw [Complex.log_re, Complex.log_im]
    _ ≤ |Real.log ‖w‖| + Real.pi := by
      gcongr
      exact Complex.abs_arg_le_pi w

private theorem slit_remainder_majorant_tendsto_zero (C : ℝ) (M : ℕ) (hC : 0 ≤ C) :
    Tendsto (fun w : ℂ ↦ C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M)
      (𝓝[Complex.slitPlane] 0) (𝓝 0) := by
  have hnorm : Tendsto (fun w : ℂ ↦ ‖w‖) (𝓝[Complex.slitPlane] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hnorm0 : Tendsto (fun w : ℂ ↦ ‖w‖) (𝓝 0) (𝓝 0) := by
        have h := (continuous_norm.continuousAt :
          ContinuousAt (fun w : ℂ ↦ ‖w‖) 0)
        change Tendsto (fun w : ℂ ↦ ‖w‖) (𝓝 0) (𝓝 ‖(0 : ℂ)‖) at h
        rw [norm_zero] at h
        exact h
      exact hnorm0.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact norm_pos_iff.mpr (Complex.slitPlane_ne_zero hw)
  have hdecay := (inner_arc_decay Real.pi 1 M Real.pi_pos.le (by omega)).comp hnorm
  have hmajor : Tendsto
      (fun w : ℂ ↦ C * (‖w‖ ^ 1 *
        (1 + Real.pi + |Real.log ‖w‖|) ^ M))
      (𝓝[Complex.slitPlane] 0) (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hdecay.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · exact Filter.Eventually.of_forall fun w ↦ by positivity
  · filter_upwards [self_mem_nhdsWithin] with w hw
    calc
      C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M ≤
          C * ‖w‖ * (1 + (|Real.log ‖w‖| + Real.pi)) ^ M := by
        gcongr
        exact norm_neg_log_le_abs_log_norm_add_pi w
      _ = C * (‖w‖ ^ 1 * (1 + Real.pi + |Real.log ‖w‖|) ^ M) := by
        rw [pow_one]
        ring

private theorem slit_neg_log_norm_tendsto_atTop :
    Tendsto (fun w : ℂ ↦ ‖-Complex.log w‖)
      (𝓝[Complex.slitPlane] 0) atTop := by
  have hnormFull : Tendsto (fun w : ℂ ↦ ‖w‖) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (continuous_norm.continuousAt :
      ContinuousAt (fun w : ℂ ↦ ‖w‖) 0).tendsto
  have hnorm : Tendsto (fun w : ℂ ↦ ‖w‖)
      (𝓝[Complex.slitPlane] 0) (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hnormFull.mono_left inf_le_left, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact norm_ne_zero_iff.mpr (Complex.slitPlane_ne_zero hw)
  have hlog : Tendsto (fun w : ℂ ↦ Real.log ‖w‖)
      (𝓝[Complex.slitPlane] 0) atBot :=
    Real.tendsto_log_nhdsNE_zero.comp hnorm
  have hneg : Tendsto (fun w : ℂ ↦ -Real.log ‖w‖)
      (𝓝[Complex.slitPlane] 0) atTop :=
    tendsto_neg_atBot_atTop.comp hlog
  apply tendsto_atTop_mono' _ (Filter.Eventually.of_forall fun w ↦ ?_) hneg
  calc
    -Real.log ‖w‖ ≤ |(-Complex.log w).re| := by
      rw [Complex.neg_re, Complex.log_re]
      exact le_abs_self _
    _ ≤ ‖-Complex.log w‖ := Complex.abs_re_le_norm _

private theorem admissible_reciprocal_endpoint_of_remainder
    (first : ℕ+) (suffix : List ℕ+) (ell : ℕ) (C ρ : ℝ) (M : ℕ)
    (hfirst : 1 < (first : ℕ)) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hbound : ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued (first :: suffix) (1 - w) -
          (CompositionBoundary.zeta first suffix : ℂ)‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M) :
    Tendsto
        (fun w : ℂ ↦ CompositionContinuation.continued (first :: suffix) (1 - w))
        (𝓝[Complex.slitPlane] 0)
        (𝓝 (CompositionBoundary.zeta first suffix : ℂ)) ∧
      (∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
        CompositionContinuation.continued (first :: suffix) (1 - w) ≠ 0) ∧
      Tendsto
        (fun w : ℂ ↦
          (((1 - w) ^ CompositionDisk.depth suffix /
            CompositionContinuation.continued (first :: suffix) (1 - w)) ^ ell))
        (𝓝[Complex.slitPlane] 0)
        (𝓝 (((CompositionBoundary.zeta first suffix : ℂ)⁻¹) ^ ell)) := by
  have hnormFull : Tendsto (fun w : ℂ ↦ ‖w‖) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (continuous_norm.continuousAt :
      ContinuousAt (fun w : ℂ ↦ ‖w‖) 0).tendsto
  have hnorm : Tendsto (fun w : ℂ ↦ ‖w‖)
      (𝓝[Complex.slitPlane] 0) (𝓝 0) :=
    hnormFull.mono_left inf_le_left
  have hsmall : ∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0, ‖w‖ < ρ :=
    hnorm.eventually (Iio_mem_nhds hρ)
  have hcontinued : Tendsto
      (fun w : ℂ ↦ CompositionContinuation.continued (first :: suffix) (1 - w))
      (𝓝[Complex.slitPlane] 0)
      (𝓝 (CompositionBoundary.zeta first suffix : ℂ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (slit_remainder_majorant_tendsto_zero C M hC)
    · exact Filter.Eventually.of_forall fun w ↦ norm_nonneg _
    · filter_upwards [self_mem_nhdsWithin, hsmall] with w hw hwρ
      exact hbound w hw (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hw)) hwρ
  have hzeta : (CompositionBoundary.zeta first suffix : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (CompositionBoundary.result first suffix
      hfirst).2.2.2.1)
  refine ⟨hcontinued, hcontinued.eventually_ne hzeta, ?_⟩
  have hw : Tendsto (fun w : ℂ ↦ w)
      (𝓝[Complex.slitPlane] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun w : ℂ ↦ 1 - w)
      (𝓝[Complex.slitPlane] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hw
  have hquot := (hone.pow (CompositionDisk.depth suffix)).div hcontinued hzeta
  simpa using hquot.pow ell

private theorem polynomial_aeval_norm_bound (P : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖Polynomial.aeval z P‖ ≤ C * (1 + ‖z‖) ^ P.natDegree := by
  let C : ℝ := ∑ n ∈ P.support, |P.coeff n|
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro z
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    calc
      ‖∑ n ∈ P.support, algebraMap ℝ ℂ (P.coeff n) * z ^ n‖ ≤
          ∑ n ∈ P.support, ‖algebraMap ℝ ℂ (P.coeff n) * z ^ n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ P.support,
          |P.coeff n| * (1 + ‖z‖) ^ P.natDegree := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, norm_pow,
          show algebraMap ℝ ℂ (P.coeff n) = (P.coeff n : ℂ) by rfl,
          Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (pow_le_pow_left₀ (norm_nonneg z) (by linarith [norm_nonneg z]) n).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg z])
            (Polynomial.le_natDegree_of_mem_supp n hn))
      _ = C * (1 + ‖z‖) ^ P.natDegree := by
        rw [Finset.sum_mul]

private theorem leading_one_upper_boundary_pow_im_eventually_pos_of_extension
    (q ell : ℕ) (suffix : List ℕ+) (ρ C : ℝ) (M : ℕ) (P : Polynomial ℝ)
    (hq : 1 ≤ q) (hell : 1 ≤ ell) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hdegree : P.natDegree = q) (hlead : 0 < P.coeff q)
    (hbound : ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          (P.map Complex.ofRealHom).eval (-Complex.log w)‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ (center : ℂ) (r : ℝ) (extension : ℂ → ℂ),
      (1 + (t : ℂ)) ∈ Metric.ball center r →
      AnalyticOnNhd ℂ extension (Metric.ball center r) →
      Set.EqOn extension
        (CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix))
        (Metric.ball center r ∩ {z : ℂ | 0 < z.im}) →
      0 < (extension (1 + (t : ℂ)) ^ ell).im := by
  obtain ⟨c, hc, hpolyLower⟩ :=
    polynomial_upper_pow_im_eventually_ge P q ell hq hell hdegree hlead
  obtain ⟨Cp, hCp, hpolyNorm⟩ := polynomial_aeval_norm_bound P
  let N : ℕ := max M q
  let K : ℕ := M + N * (ell - 1)
  let D : ℝ := ell * C * (C + Cp) ^ (ell - 1)
  have hlogTop : Tendsto (fun t : ℝ ↦ -Real.log t) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hpolyAtZero := hlogTop.eventually hpolyLower
  have hdecay := inner_arc_decay Real.pi 1 K Real.pi_pos.le (by omega)
  have hmajor : Tendsto
      (fun t : ℝ ↦ D * (t ^ 1 * (1 + Real.pi + |Real.log t|) ^ K))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hdecay.const_mul D
  filter_upwards [Ioo_mem_nhdsGT (by positivity : 0 < min ρ 1),
    hlogTop.eventually (eventually_ge_atTop 1), hpolyAtZero,
    hmajor.eventually (Iio_mem_nhds hc)] with t ht hT hpoly hsmall
  intro center r extension hx hextension heq
  let L : ℂ := (-Real.log t : ℂ) + Real.pi * I
  let E : ℝ := C * t * (1 + ‖L‖) ^ M
  let b : ℂ := (P.map Complex.ofRealHom).eval L
  let B : ℝ := 1 + Real.pi + |Real.log t|
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [Real.pi_pos, abs_nonneg (Real.log t)]
  have hL : 1 + ‖L‖ ≤ B := by
    dsimp only [L, B]
    calc
      1 + ‖(-Real.log t : ℂ) + Real.pi * I‖ ≤
          1 + (|((-Real.log t : ℂ) + Real.pi * I).re| +
            |((-Real.log t : ℂ) + Real.pi * I).im|) := by
        gcongr
        exact Complex.norm_le_abs_re_add_abs_im _
      _ = 1 + Real.pi + |Real.log t| := by
        simp [abs_of_pos Real.pi_pos]
        ring
  have hE : E ≤ C * t * B ^ M := by
    dsimp only [E]
    gcongr
    exact mul_nonneg hC ht.1.le
  have hb : ‖b‖ ≤ Cp * B ^ q := by
    have hhom : algebraMap ℝ ℂ = Complex.ofRealHom := by ext x; rfl
    have heval : b = Polynomial.aeval L P := by
      dsimp only [b]
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hhom]
    rw [heval]
    calc
      ‖Polynomial.aeval L P‖ ≤ Cp * (1 + ‖L‖) ^ P.natDegree := hpolyNorm L
      _ ≤ Cp * B ^ q := by rw [hdegree]; gcongr
  have hsum : ‖b‖ + E ≤ (C + Cp) * B ^ N := by
    calc
      ‖b‖ + E ≤ Cp * B ^ q + C * t * B ^ M := add_le_add hb hE
      _ ≤ Cp * B ^ N + C * B ^ N := add_le_add (by
          gcongr
          exact Nat.le_max_right M q) (by
          calc
            C * t * B ^ M ≤ C * 1 * B ^ M := by
              gcongr
              exact (ht.2.trans_le (min_le_right ρ 1)).le
            _ ≤ C * 1 * B ^ N := by
              gcongr
              exact Nat.le_max_left M q
            _ = C * B ^ N := by ring)
      _ = (C + Cp) * B ^ N := by ring
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg hC ht.1.le) (pow_nonneg (by positivity) M)
  have hsum0 : 0 ≤ ‖b‖ + E := add_nonneg (norm_nonneg b) hE0
  have herror := leading_one_upper_boundary_pow_remainder_of_extension
    q suffix ell ρ C M P t center r extension ht.1
      (ht.2.trans_le (min_le_left ρ 1)) hC hbound hx hextension heq
  have herrorMajor : ‖extension (1 + (t : ℂ)) ^ ell - b ^ ell‖ ≤
      D * (t ^ 1 * B ^ K) := by
    calc
      ‖extension (1 + (t : ℂ)) ^ ell - b ^ ell‖ ≤
          ell * E * (‖b‖ + E) ^ (ell - 1) := by simpa only [L, E, b] using herror
      _ ≤ ell * (C * t * B ^ M) * ((C + Cp) * B ^ N) ^ (ell - 1) := by
        calc
          ell * E * (‖b‖ + E) ^ (ell - 1) ≤
              ell * (C * t * B ^ M) * (‖b‖ + E) ^ (ell - 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg ell))
              (pow_nonneg hsum0 _)
          _ ≤ ell * (C * t * B ^ M) * ((C + Cp) * B ^ N) ^ (ell - 1) := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hsum0 hsum (ell - 1))
              (mul_nonneg (Nat.cast_nonneg ell)
                (mul_nonneg (mul_nonneg hC ht.1.le) (pow_nonneg (by linarith) M)))
      _ = D * (t ^ 1 * B ^ K) := by
        dsimp only [D, K]
        simp only [mul_pow, pow_mul, pow_add, pow_one]
        ring
  have himError :
      |(extension (1 + (t : ℂ)) ^ ell).im - (b ^ ell).im| < c := by
    calc
      |(extension (1 + (t : ℂ)) ^ ell).im - (b ^ ell).im| =
          |(extension (1 + (t : ℂ)) ^ ell - b ^ ell).im| := by rw [Complex.sub_im]
      _ ≤ ‖extension (1 + (t : ℂ)) ^ ell - b ^ ell‖ := Complex.abs_im_le_norm _
      _ ≤ D * (t ^ 1 * B ^ K) := herrorMajor
      _ < c := hsmall
  have hcpoly : c ≤ (b ^ ell).im := by
    have hpow : 1 ≤ (-Real.log t) ^ (q * ell - 1) := one_le_pow₀ hT
    have hpoly' : c * (-Real.log t) ^ (q * ell - 1) ≤ (b ^ ell).im := by
      dsimp only [b, L]
      convert hpoly using 1 <;> simp
    exact (le_mul_of_one_le_right hc.le hpow).trans hpoly'
  have hlower := (abs_lt.mp himError).1
  linarith

private theorem leading_one_upper_boundary_reciprocal_im_eventually_neg
    (q ell depth : ℕ) (suffix : List ℕ+) (ρ C : ℝ) (M : ℕ) (P : Polynomial ℝ)
    (hq : 1 ≤ q) (hell : 1 ≤ ell) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hdegree : P.natDegree = q) (hlead : 0 < P.coeff q)
    (hbound : ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          (P.map Complex.ofRealHom).eval (-Complex.log w)‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ (center : ℂ) (r : ℝ) (extension : ℂ → ℂ) (value : ℂ),
      (1 + (t : ℂ)) ∈ Metric.ball center r →
      AnalyticOnNhd ℂ extension (Metric.ball center r) →
      Set.EqOn extension
        (CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix))
        (Metric.ball center r ∩ {z : ℂ | 0 < z.im}) →
      value = (((1 + (t : ℂ)) ^ depth / extension (1 + (t : ℂ))) ^ ell) →
      value.im < 0 := by
  filter_upwards [self_mem_nhdsWithin,
    leading_one_upper_boundary_pow_im_eventually_pos_of_extension
      q ell suffix ρ C M P hq hell hρ hC hdegree hlead hbound] with t ht0 hpositive
  intro center r extension value hx hextension heq hvalue
  have hpow := hpositive center r extension hx hextension heq
  have hne : extension (1 + (t : ℂ)) ^ ell ≠ 0 := by
    intro hz
    rw [hz] at hpow
    simpa using hpow
  change 0 < t at ht0
  have ht : 0 < 1 + t := by linarith
  have hbase : (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) := by norm_num
  have hnum :
      ((1 + (t : ℂ)) ^ depth) ^ ell =
        (((1 + t) ^ (depth * ell) : ℝ) : ℂ) := by
    rw [hbase, ← pow_mul]
    norm_num
  rw [hvalue, div_pow, Complex.div_im, hnum]
  simp only [Complex.ofReal_im, zero_mul, zero_div, Complex.ofReal_re, zero_sub]
  exact neg_lt_zero.mpr <| div_pos (mul_pos (pow_pos ht _) hpow) (Complex.normSq_pos.mpr hne)

private theorem leading_one_continued_norm_bound_of_remainder
    (leadingOneRemainder : ℕ → List ℕ+ → Prop)
    (unpack : ∀ (q : ℕ) (suffix : List ℕ+), leadingOneRemainder q suffix →
      ∃ ρ C : ℝ, ∃ M : ℕ, ∃ P : Polynomial ℝ,
        0 < ρ ∧ ρ < 1 ∧ 0 ≤ C ∧ P.natDegree = q ∧
          (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
            ‖CompositionContinuation.continued
                (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
                (P.map Complex.ofRealHom).eval (-Complex.log w)‖ ≤
              C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M)) :
    ∀ (q : ℕ) (suffix : List ℕ+), leadingOneRemainder q suffix →
      ∃ ρ D : ℝ, ∃ N : ℕ,
        0 < ρ ∧ ρ < 1 ∧ 0 ≤ D ∧
          ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
            ‖CompositionContinuation.continued
                (List.replicate q (1 : ℕ+) ++ suffix) (1 - w)‖ ≤
              D * (1 + ‖-Complex.log w‖) ^ N := by
  intro q suffix hq
  obtain ⟨ρ, C, M, P, hρ0, hρ1, hC, hdegree, herror⟩ := unpack q suffix hq
  obtain ⟨Cp, hCp, hpoly⟩ := polynomial_aeval_norm_bound P
  refine ⟨ρ, C + Cp, max M q, hρ0, hρ1, add_nonneg hC hCp, ?_⟩
  intro w hw hw0 hwρ
  have hw1 : ‖w‖ ≤ 1 := (hwρ.trans hρ1).le
  have hbase : 1 ≤ 1 + ‖-Complex.log w‖ := by
    linarith [norm_nonneg (-Complex.log w)]
  have hhom : algebraMap ℝ ℂ = Complex.ofRealHom := by
    ext x
    rfl
  have heval : Polynomial.eval (-Complex.log w) (P.map Complex.ofRealHom) =
      Polynomial.aeval (-Complex.log w) P := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hhom]
  calc
    ‖CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - w)‖ =
        ‖(CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
              Polynomial.eval (-Complex.log w) (P.map Complex.ofRealHom)) +
          Polynomial.eval (-Complex.log w) (P.map Complex.ofRealHom)‖ := by
            congr 1
            ring
    _ ≤ ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
              Polynomial.eval (-Complex.log w) (P.map Complex.ofRealHom)‖ +
          ‖Polynomial.eval (-Complex.log w) (P.map Complex.ofRealHom)‖ :=
        norm_add_le _ _
    _ ≤ C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M +
          Cp * (1 + ‖-Complex.log w‖) ^ q := by
        exact add_le_add (herror w hw hw0 hwρ) (by
          rw [heval]
          simpa [hdegree] using hpoly (-Complex.log w))
    _ ≤ C * (1 + ‖-Complex.log w‖) ^ max M q +
          Cp * (1 + ‖-Complex.log w‖) ^ max M q := by
        apply add_le_add
        · calc
            C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M ≤
                C * 1 * (1 + ‖-Complex.log w‖) ^ M := by gcongr
            _ ≤ C * 1 * (1 + ‖-Complex.log w‖) ^ max M q := by
              gcongr
              exact Nat.le_max_left M q
            _ = C * (1 + ‖-Complex.log w‖) ^ max M q := by ring
        · gcongr
          exact Nat.le_max_right M q
    _ = (C + Cp) * (1 + ‖-Complex.log w‖) ^ max M q := by ring

private theorem leading_one_reciprocal_endpoint_of_remainder
    (q ell : ℕ) (suffix : List ℕ+) (ρ C : ℝ) (M : ℕ) (P : Polynomial ℝ)
    (hq : 1 ≤ q) (hell : 1 ≤ ell) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hdegree : P.natDegree = q)
    (hbound : ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          (P.map Complex.ofRealHom).eval (-Complex.log w)‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M) :
    Tendsto
        (fun w : ℂ ↦ ‖CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - w)‖)
        (𝓝[Complex.slitPlane] 0) atTop ∧
      (∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
        CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) ≠ 0) ∧
      Tendsto
        (fun w : ℂ ↦ (((1 - w) ^ CompositionDisk.depth
            (List.replicate (q - 1) (1 : ℕ+) ++ suffix) /
          CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w)) ^ ell))
        (𝓝[Complex.slitPlane] 0) (𝓝 0) := by
  let Q : Polynomial ℂ := P.map Complex.ofRealHom
  have hQdegree : Q.natDegree = q := by
    dsimp [Q]
    rw [Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
    exact hdegree
  have hQdegreePos : 0 < Q.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
  have hpoly : Tendsto (fun w : ℂ ↦ ‖Q.eval (-Complex.log w)‖)
      (𝓝[Complex.slitPlane] 0) atTop :=
    Q.tendsto_norm_atTop hQdegreePos slit_neg_log_norm_tendsto_atTop
  have hnormFull : Tendsto (fun w : ℂ ↦ ‖w‖) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (continuous_norm.continuousAt :
      ContinuousAt (fun w : ℂ ↦ ‖w‖) 0).tendsto
  have hnorm : Tendsto (fun w : ℂ ↦ ‖w‖)
      (𝓝[Complex.slitPlane] 0) (𝓝 0) := hnormFull.mono_left inf_le_left
  have hsmall : ∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0, ‖w‖ < ρ :=
    hnorm.eventually (Iio_mem_nhds hρ)
  have herror : Tendsto
      (fun w : ℂ ↦ ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          Q.eval (-Complex.log w)‖)
      (𝓝[Complex.slitPlane] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (slit_remainder_majorant_tendsto_zero C M hC)
    · exact Filter.Eventually.of_forall fun w ↦ norm_nonneg _
    · filter_upwards [self_mem_nhdsWithin, hsmall] with w hw hwρ
      simpa only [Q] using
        hbound w hw (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hw)) hwρ
  have herrorOne : ∀ᶠ w : ℂ in 𝓝[Complex.slitPlane] 0,
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          Q.eval (-Complex.log w)‖ < 1 :=
    herror.eventually (Iio_mem_nhds zero_lt_one)
  have hpolySub : Tendsto (fun w : ℂ ↦ ‖Q.eval (-Complex.log w)‖ + (-1 : ℝ))
      (𝓝[Complex.slitPlane] 0) atTop :=
    tendsto_atTop_add_const_right (𝓝[Complex.slitPlane] 0) (-1) hpoly
  have hcontinued : Tendsto
      (fun w : ℂ ↦ ‖CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - w)‖)
      (𝓝[Complex.slitPlane] 0) atTop := by
    apply tendsto_atTop_mono' _ ?_ hpolySub
    filter_upwards [herrorOne] with w hw
    have htriangle := norm_le_norm_add_norm_sub
      (CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - w))
      (Q.eval (-Complex.log w))
    linarith
  refine ⟨hcontinued, eventually_ne_of_tendsto_norm_atTop hcontinued 0, ?_⟩
  have hcobounded : Tendsto
      (fun w : ℂ ↦ CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - w))
      (𝓝[Complex.slitPlane] 0) (Bornology.cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.mp hcontinued
  have hinv : Tendsto
      (fun w : ℂ ↦ (CompositionContinuation.continued
        (List.replicate q (1 : ℕ+) ++ suffix) (1 - w))⁻¹)
      (𝓝[Complex.slitPlane] 0) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp hcobounded
  have hw : Tendsto (fun w : ℂ ↦ w)
      (𝓝[Complex.slitPlane] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun w : ℂ ↦ 1 - w)
      (𝓝[Complex.slitPlane] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hw
  have hquot := (hone.pow (CompositionDisk.depth
    (List.replicate (q - 1) (1 : ℕ+) ++ suffix))).mul hinv
  simpa [div_eq_mul_inv, zero_pow (by omega : ell ≠ 0)] using hquot.pow ell

private theorem leading_one_remainder_succ : ∀ (q : ℕ) (suffix : List ℕ+),
    leadingOneRemainder q suffix → leadingOneRemainder (q + 1) suffix := by
  intro q suffix hq
  rcases hq with ⟨hsuffix, ρ, C, M, P, hρ0, hρ1, hC, hdegree, hcoeff, hbound⟩
  have hprimitiveCoeff : (polynomialPrimitive P).coeff (q + 1) =
      P.coeff q / (q + 1 : ℝ) := by
    simp [polynomialPrimitive, Polynomial.sum_def]
    by_cases hcoeff : P.coeff q = 0 <;> simp [hcoeff]
  have hsuffixPos : 0 < suffixConstant suffix := by
    rcases hsuffix with rfl | ⟨first, rest, rfl, hfirst⟩
    · simp [suffixConstant]
    · simpa [suffixConstant] using
        (CompositionBoundary.result first rest hfirst).2.2.2.1
  have hprimitiveDegree : (polynomialPrimitive P).natDegree = q + 1 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · change (P.sum fun n a ↦
          Polynomial.C (a / (n + 1 : ℝ)) * Polynomial.X ^ (n + 1)).natDegree ≤ q + 1
      rw [Polynomial.sum_def]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro n hn
      refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
      have hnq : n ≤ q := by
        rw [← hdegree]
        exact Polynomial.le_natDegree_of_mem_supp n hn
      omega
    · rw [hprimitiveCoeff, hcoeff]
      positivity
  have hhom : algebraMap ℝ ℂ = Complex.ofRealHom := rfl
  have hbound' : ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
      ‖CompositionContinuation.continued
            (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
          Polynomial.aeval (-Complex.log w) P‖ ≤
        C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M := by
    simpa only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hhom] using hbound
  obtain ⟨rayConstant, hidentity⟩ :=
    leading_remainder_integral_identity q suffix P ρ C M hρ0 hC hbound'
  let K : ℝ := ∫ t in (0 : ℝ)..1, (1 + (-Real.log t)) ^ M
  have hK : 0 ≤ K := by
    dsimp [K]
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t ht
    by_cases ht0 : t = 0
    · simp [ht0]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hlog : Real.log t ≤ 0 := Real.log_nonpos htpos.le ht.2
      exact pow_nonneg (by linarith) M
  let Q : Polynomial ℝ := polynomialPrimitive P + Polynomial.C rayConstant
  refine ⟨hsuffix, ρ, C * K, M, Q, hρ0, hρ1, mul_nonneg hC hK, ?_, ?_, ?_⟩
  · dsimp [Q]
    rw [Polynomial.natDegree_add_C, hprimitiveDegree]
  · dsimp [Q]
    rw [Polynomial.coeff_add, hprimitiveCoeff, hcoeff, Nat.factorial_succ]
    norm_num
    field_simp
  · intro w hw hw0 hwρ
    let E : ℂ → ℂ := fun u ↦
      CompositionContinuation.continued
          (List.replicate q (1 : ℕ+) ++ suffix) (1 - u) -
        Polynomial.aeval (-Complex.log u) P
    let Ecut : ℂ → ℂ := fun u ↦
      if u ∈ Complex.slitPlane ∧ ‖u‖ < ρ then -E u else 0
    have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hw0)
    have hEcut : ∀ u : ℂ, u ≠ 0 →
        ‖Ecut u‖ ≤ C * ‖u‖ ^ 1 * (1 + ‖-Complex.log u‖) ^ M := by
      intro u hu
      by_cases hcut : u ∈ Complex.slitPlane ∧ ‖u‖ < ρ
      · rw [show Ecut u = -E u by simp [Ecut, hcut], norm_neg, pow_one]
        exact hbound' u hcut.1 (norm_pos_iff.mpr hu) hcut.2
      · rw [show Ecut u = 0 by simp [Ecut, hcut], norm_zero, pow_one]
        exact mul_nonneg (mul_nonneg hC (norm_nonneg u))
          (pow_nonneg (by positivity) M)
    have hcutline : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        Ecut ((t : ℂ) * w) = -E ((t : ℂ) * w) := by
      intro t ht
      apply if_pos
      have htw : (t : ℂ) * w ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff] at hw ⊢
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero, Complex.mul_im, add_zero]
        exact hw.imp (fun h ↦ mul_pos ht.1 h) (mul_ne_zero ht.1.ne')
      refine ⟨htw, ?_⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans_lt hwρ
    have huniform := radial_div_uniform_bound Ecut C 1 M hC (by omega) w hwne hEcut
    have hintegral :
        (∫ t in (0 : ℝ)..1, w *
          (-(CompositionContinuation.continued
                (List.replicate q (1 : ℕ+) ++ suffix) (1 - (t : ℂ) * w) -
              Polynomial.aeval (-Complex.log ((t : ℂ) * w)) P) /
            ((t : ℂ) * w))) =
          ∫ t in (0 : ℝ)..1, w *
            (Ecut ((t : ℂ) * w) / ((t : ℂ) * w)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      by_cases ht0 : t = 0
      · simp [ht0]
      · rw [Set.uIcc_of_le zero_le_one] at ht
        have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        exact congrArg (fun x : ℂ ↦ w * (x / ((t : ℂ) * w)))
          (hcutline t ht').symm
    have hQeval :
        Polynomial.eval (-Complex.log w) (Q.map Complex.ofRealHom) =
          Polynomial.aeval (-Complex.log w) (polynomialPrimitive P) + rayConstant := by
      dsimp [Q]
      rw [Polynomial.map_add, Polynomial.eval_add, Polynomial.map_C, Polynomial.eval_C]
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hhom]
      rfl
    rw [hQeval]
    have hrewrite : CompositionContinuation.continued
        (List.replicate (q + 1) (1 : ℕ+) ++ suffix) (1 - w) -
          (Polynomial.aeval (-Complex.log w) (polynomialPrimitive P) + rayConstant) =
        (CompositionContinuation.continued
            (List.replicate (q + 1) (1 : ℕ+) ++ suffix) (1 - w) -
          Polynomial.aeval (-Complex.log w) (polynomialPrimitive P)) - rayConstant := by
      ring
    rw [hrewrite]
    rw [hidentity w hw hw0 hwρ]
    change ‖(∫ t in (0 : ℝ)..1, w *
        (-(CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix) (1 - (t : ℂ) * w) -
            Polynomial.aeval (-Complex.log ((t : ℂ) * w)) P) /
          ((t : ℂ) * w)))‖ ≤ (C * K) * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M
    rw [hintegral]
    rw [intervalIntegral.integral_const_mul, norm_mul]
    calc
      ‖w‖ * ‖∫ t in (0 : ℝ)..1, Ecut ((t : ℂ) * w) / ((t : ℂ) * w)‖ ≤
          C * ‖w‖ ^ 1 * (1 + ‖-Complex.log w‖) ^ M *
            ∫ t in (0 : ℝ)..1, t ^ (1 - 1) * (1 + (-Real.log t)) ^ M := by
        simpa only [intervalIntegral.integral_const_mul, norm_mul] using huniform
      _ = (C * K) * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M := by
        simp only [pow_one, show 1 - 1 = 0 by omega, pow_zero, one_mul, K]
        ring
private theorem leading_one_remainder_iterate : ∀ (q : ℕ) (suffix : List ℕ+),
    leadingOneRemainder 0 suffix → leadingOneRemainder q suffix := by
  intro q suffix hzero
  induction q with
  | zero => exact hzero
  | succ q ih =>
      simpa only [Nat.succ_eq_add_one] using
        leading_one_remainder_succ q suffix ih
private theorem composition_continued_norm_bound : ∀ ks : List ℕ+,
    (∀ (first : ℕ+) (rest : List ℕ+),
      sourceWeight (first :: rest) ≤ sourceWeight ks → 1 < (first : ℕ) →
        admissibleRemainder first rest) →
    ∃ ρ D : ℝ, ∃ N : ℕ,
      0 < ρ ∧ ρ < 1 ∧ 0 ≤ D ∧
        ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
          ‖CompositionContinuation.continued ks (1 - w)‖ ≤
            D * (1 + ‖-Complex.log w‖) ^ N := by
  intro ks hadmissible
  obtain ⟨q, suffix, hks, hsuffix⟩ := split_leading_ones ks
  have leading_one_remainder_zero : leadingOneRemainder 0 [] := by
    refine ⟨Or.inl rfl, (1 / 2 : ℝ), 0, 0, 1, by norm_num, by norm_num,
      by norm_num, by simp, ?_, ?_⟩
    · simp [suffixConstant]
    · intro w _hw _hw0 _hwrho
      rw [show List.replicate 0 (1 : ℕ+) ++ [] = [] by simp,
        (CompositionSlit.result).1]
      norm_num
  have leading_one_remainder_zero_of_admissible : ∀
      (first : ℕ+) (suffix : List ℕ+),
      admissibleRemainder first suffix → leadingOneRemainder 0 (first :: suffix) := by
    intro first suffix hadmissible
    rcases hadmissible with ⟨hfirst, ρ, C, M, hρ0, hρ1, hC, hbound⟩
    refine ⟨Or.inr ⟨first, suffix, rfl, hfirst⟩, ρ, C, M,
      Polynomial.C (CompositionBoundary.zeta first suffix), hρ0, hρ1, hC,
      by simp, by simp [suffixConstant], ?_⟩
    intro w hw hw0 hwrho
    simpa using hbound w hw hw0 hwrho
  have hzero : leadingOneRemainder 0 suffix := by
    rcases hsuffix with rfl | ⟨first, rest, rfl, hfirst⟩
    · exact leading_one_remainder_zero
    · apply leading_one_remainder_zero_of_admissible first rest
      apply hadmissible first rest
      · rw [hks]
        induction q with
        | zero => simp [sourceWeight]
        | succ q ih =>
            simp [List.replicate_succ, sourceWeight]
            omega
      · exact hfirst
  obtain ⟨ρ, D, N, hρ0, hρ1, hD, hbound⟩ :=
    leading_one_continued_norm_bound_of_remainder leadingOneRemainder (by
      intro q suffix hq
      rcases hq with
        ⟨_hsuffix, ρ, C, M, P, hρ0, hρ1, hC, hdegree, _hcoeff, herror⟩
      exact ⟨ρ, C, M, P, hρ0, hρ1, hC, hdegree, herror⟩)
      q suffix (leading_one_remainder_iterate q suffix hzero)
  refine ⟨ρ, D, N, hρ0, hρ1, hD, ?_⟩
  simpa only [← hks] using hbound

end D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksLeadingClosure
