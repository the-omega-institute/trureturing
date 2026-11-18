/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerEndpointRH
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerEndpointRH
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The endpoint real-power Robin inequality fails eventually on prefix lcms under RH. -/

import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion

/-! The sharp Mertens envelope and the actual lcm corrections leave a strictly
positive endpoint margin. All analytic corrections refer to the same cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset Filter
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.LcmPowerEndpointRH

open LcmPowerEndpointExpansion (sigmaKappa G)
open RHSharpArithmeticEnvelope (D)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass firstLiMass_lt_third)

private def mertensProduct (x : ℝ) : ℝ :=
  ∏ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹

private lemma B_product_bridge (x : ℝ) :
    RHSharpArithmeticEnvelope.B x = Real.eulerMascheroniConstant +
      Real.log (Real.log (Chebyshev.theta x)) - Real.log (mertensProduct x) := by
  have hnz (p : ℕ) (hp : p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime) :
      (1 - (1 : ℝ) / p)⁻¹ ≠ 0 := by
    have hpp := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hfrac : (1 : ℝ) / p < 1 := (div_lt_one (by linarith)).mpr hp1
    exact inv_ne_zero (by linarith)
  unfold mertensProduct
  rw [Real.log_prod hnz]
  simp_rw [Real.log_inv, sum_neg_distrib]
  unfold RHSharpArithmeticEnvelope.B Mertens.E₃
  ring

private lemma B_envelope_bridge (x : ℝ) :
    LcmPowerEndpointExpansion.B x = RHSharpArithmeticEnvelope.B x := by
  rw [B_product_bridge]
  have hnz (p : ℕ) (hp : p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime) :
      (1 - (1 : ℝ) / p)⁻¹ ≠ 0 := by
    have hpp := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hfrac : (1 : ℝ) / p < 1 := (div_lt_one (by linarith)).mpr hp1
    exact inv_ne_zero (by linarith)
  unfold mertensProduct
  rw [Real.log_prod hnz]
  simp_rw [Real.log_inv, sum_neg_distrib]
  unfold LcmPowerEndpointExpansion.B LcmPowerEndpointExpansion.primeCutoff
  ring

private lemma eventual_positive_log (hRH : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop,
      1 < Chebyshev.psi x ∧ 0 < Real.log (G (3 / 2) (Nat.lcmUpto ⌊x⌋₊)) := by
  let eta : ℝ := (1 / 2 - (3 / 2) * firstLiMass) / 10
  have heta : 0 < eta := by
    dsimp [eta]
    linarith [firstLiMass_lt_third]
  have hA := LcmPowerEndpointExpansion.A_scaled_limit.eventually_lt_const
    (show (2 : ℝ) < 2 + eta by linarith)
  have hJ := LcmPowerEndpointExpansion.J_scaled_limit.eventually_lt_const
    (show (1 : ℝ) < 1 + eta by linarith)
  have hT := LcmPowerEndpointExpansion.endpoint_euler_tail_lower eta heta
  have hB := (RHSharpArithmeticEnvelope.actual_B_lower_endpoint hRH).1 eta heta
  filter_upwards [hA, hJ, hT, hB, eventually_gt_atTop (1 : ℝ)]
    with x ha hj ht hb hx
  have hpsi : 1 < Chebyshev.psi x := hb.1.trans_le (Chebyshev.theta_le_psi x)
  refine ⟨hpsi, ?_⟩
  have hd : 0 < D x :=
    mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos hx)
  have hDb : D x * RHSharpArithmeticEnvelope.B x < -2 + firstLiMass + eta := by
    linarith [(abs_lt.mp hb.2).2]
  have hC := mul_nonneg hd.le
    (LcmPowerEndpointExpansion.C_nonneg (by norm_num : (0 : ℝ) < 3 / 2) x)
  have heq := LcmPowerEndpointExpansion.log_G_decomposition
    (κ := (3 / 2 : ℝ)) (by norm_num) hpsi
  rw [B_envelope_bridge] at heq
  have hscaled := congrArg (fun v : ℝ => D x * v) heq
  change D x * LcmPowerEndpointExpansion.A x < 2 + eta at ha
  change D x * LcmPowerEndpointExpansion.J x < 1 + eta at hj
  change 2 - eta < D x * LcmPowerEndpointExpansion.T (3 / 2) x at ht
  have hpositive : 0 < D x * Real.log (G (3 / 2) (Nat.lcmUpto ⌊x⌋₊)) := by
    dsimp [eta] at hDb ha hj ht
    nlinarith [firstLiMass_lt_third]
  exact pos_of_mul_pos_right hpositive hd.le

/-- Under RH the endpoint inequality is eventually reversed on every prefix lcm. -/
theorem result (hRH : RiemannHypothesis) :
    ∃ M₀ : ℕ, 3 ≤ M₀ ∧ ∀ m : ℕ, M₀ ≤ m →
      (Real.exp Real.eulerMascheroniConstant * (Nat.lcmUpto m : ℝ) *
        Real.log (Real.log (Nat.lcmUpto m : ℝ))) ^ (3 / 2 : ℝ) /
          (riemannZeta ((3 / 2 : ℝ) : ℂ)).re < sigmaKappa (3 / 2) (Nat.lcmUpto m) := by
  have hm := tendsto_natCast_atTop_atTop.eventually (eventual_positive_log hRH)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hm
  refine ⟨max M 3, le_max_right _ _, ?_⟩
  intro m hm
  have hh := hM m ((le_max_left _ _).trans hm)
  simp only [Nat.floor_natCast] at hh
  have hpsi : 1 < Chebyshev.psi (m : ℝ) := hh.1
  have hg := LcmPowerEndpointExpansion.G_pos (κ := (3 / 2 : ℝ))
    (by norm_num) hpsi
  simp only [Nat.floor_natCast] at hg
  have hg1 : 1 < G (3 / 2) (Nat.lcmUpto m) := (Real.log_pos_iff hg.le).mp hh.2
  have hz : 0 < (riemannZeta ((3 / 2 : ℝ) : ℂ)).re :=
    riemannZeta_re_pos_of_one_lt (by norm_num)
  have hn : 0 < (Nat.lcmUpto m : ℝ) := by exact_mod_cast Nat.lcmUpto_pos m
  have hlog : Real.log (Nat.lcmUpto m : ℝ) = Chebyshev.psi (m : ℝ) :=
    (Chebyshev.psi_eq_log_lcmUpto m).symm
  have hbase : 0 < Real.exp Real.eulerMascheroniConstant * (Nat.lcmUpto m : ℝ) *
      Real.log (Real.log (Nat.lcmUpto m : ℝ)) := by
    exact mul_pos (mul_pos (Real.exp_pos _) hn) (by rw [hlog]; exact Real.log_pos hpsi)
  have hden := Real.rpow_pos_of_pos hbase (3 / 2 : ℝ)
  unfold G at hg1
  have hprod := (lt_div_iff₀ hden).mp hg1
  exact (div_lt_iff₀ hz).mpr (by nlinarith)

end D5.S3.Arith.Robin.Analytic.LcmPowerEndpointRH
