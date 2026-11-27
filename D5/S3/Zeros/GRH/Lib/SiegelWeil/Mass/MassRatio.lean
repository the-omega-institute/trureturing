/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/Mass/MassRatio
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/Mass/MassRatio
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.Mass.MassRatio. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/Mass/MassRatio.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.OneVector.OneVector
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Mass formula for unimodular hermitian lattices, ratio of consecutive masses. This
file gives only the ratio of consecutive masses in large rank, up to an explicit error uniform among
CM fields with enough roots of unity (so unramified over the real subfield), a splitting character
and a self-dual rank-one lattice. The proof uses Siegel's formula for vectors of norm one and a
Gauss sum bound. Source: W. T. Gan, J. Hanke, J.-K. Yu, On an exact mass formula of Shimura, Duke
Math. J. 107 (2001); M. Kirschmer, Definite quadratic and hermitian forms with small class number
(2016), 4.2.7, 4.2.9.

This file: Ratio of consecutive masses of unimodular hermitian lattices, explicit error uniform in
field. -/

open NumberField Real MeasureTheory Set stdLattice Matrix

/-- For a CM field E with Weil data, f infinite places and root discriminant rd: if 8f ≤ 2^u and
j ≥ 4u + 12, then log(mass_{j+1} / mass_j) differs from f·log(rd^{j+1/2} j! / (2π)^{j+1}) by
at most 2/2^u.

Known result: Mass formula for unimodular hermitian lattices: ratio of consecutive masses. -/
lemma abs_log_mass_ratio_sub_le E [Field.{0} E] [CMType E] [WeilData E] j u (hu : 8 * numInfPlaces
  E ≤ 2 ^ u) (hj : 4 * u + 12 ≤ j) : |log (mass E (j + 1)) - log (mass E j) - numInfPlaces E *
  ((j + 1 / 2) * log (rootDiscr E) + log j.factorial - (j + 1) * log (2 * π))| ≤ 2 / 2 ^ u := by
  have h := classSum_norm_eq (by simp; lia) (Kf E (Fin j ⊕ Unit)) (.indicator 1 (id (.symm
    ⟨isOpen_stdLattice, isCompact_stdLattice.isClosed⟩))) (fun _ k _ ↦
    if_congr (mulVec_mem_intVectors_iff k) rfl rfl)
    (.intro isCompact_stdLattice (by simp)) (star_one _) (by simp)
  erw [funext (ENNReal.coe_indicator _ _),
    withDensity_indicator_one isOpen_stdLattice.measurableSet] at h
  extract_lets F σ at h
  obtain ⟨z, _, _, c, _⟩ := @idealZeta_intAdeles_pow_le E _ _ u.succ u 1
    (finrank_eq_two_mul_card_infinitePlace E ▸ by lia), mass_pos E j.succ,
    classSum_card_norm_one_eq_mass E j, (isOpen_codifferent E 1).measurableSet, congr(log ‖$(h.2)‖)
  obtain ⟨b, hF⟩ := (lintegral_add_compl (‖F ·‖ₑ) c).trans_le (lintegral_gauss_sum_le_idealZeta
    (le_two_of_pow_le_ofReal z) (by simp; lia) _),
    setIntegral_congr_fun (f := F) (μ := volume) c fun z k ↦ setIntegral_congr_fun
    isOpen_stdLattice.measurableSet fun x h ↦ congrArg _ (by simpa [← mul_add, ← star_dotProduct]
    using ((ψf_half _).trans (k _ (mul_mem (sub_mem (dot_mem h h) (one_mem _)) traceOneAdele_mem))))
  simp [σ, classSum_stdRatPoints_eq_mass, NNReal.coe_tsum, coe_stdLattice, ← ite_and, apply_ite,
    indicator, volume_pi_pi, fun s ↦ @Eq.trans ℝ (ncard s) _ _ (by simp) (tsum_subtype s 1),
    Measure.real, abs_discr_eq_rootDiscr_pow] at *
  obtain ⟨⟨x, hx⟩, _⟩ := mul_right_surjective₀ (hF.trans_ne (by simp)) (∫ z, F z), rootDiscr_pos E
  have ⟨_, _⟩ : x ≠ 0 ∧ Integrable F := by grind [Complex.ofReal_eq_zero, mass_pos, integral_undef]
  grw [z, ← enorm_integral_le_lintegral_enorm, ← enorm_integral_le_lintegral_enorm] at b
  simp (disch := finiteness) [*, ← hx, volÔ_eq, ← ENNReal.toReal_le_toReal, pow_succ,
    ENNReal.toReal_add, add_mul, setIntegral_compl, ← sub_one_mul, log_mul, log_div, log_sqrt] at *
  grind [x.log_re, x.log.abs_re_le_norm, Complex.norm_log_one_add_half_le_self (b.trans (by
    simp [field, one_le_pow₀]))]
