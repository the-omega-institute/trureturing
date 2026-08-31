/- GID: D5/S3/Weil/ZetaCore/OffLineStrongNegativeCertificate
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaCore/OffLineStrongNegativeCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Extract a shifted witness and strong negative certificate from an off-line zero. -/

import D5.S3.Weil.ZetaCore.OffLinePickWitness
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/- Search audit (2026-08-31):
   * `rg xi_reading_differentiable D5/S3/Zeros/CompletedZeta.lean`
     found the existing proof that `xiReading` is entire.
   * `rg eventually_eq_zero_or_eventually_ne_zero .lake/packages/mathlib/Mathlib`
     found Mathlib's local isolated-zeros principle.
   * `rg eqOn_of_preconnected .lake/packages/mathlib/Mathlib` found the
     analytic identity theorem used to reject the locally-zero branch.
   * No repository declaration supplies the existential shift; the frozen
     one-point theorem requires that shift and its nonvanishing as inputs. -/

namespace D5.S3.Weil.ZetaCore.OffLineStrongNegativeCertificate

open Filter Set
open D5.S3.Zeros.CompletedZeta
open D5.S3.Weil.ZetaCore.OffLinePickWitness
open scoped Topology

/-- An off-line zero admits a shifted nonzero evaluation, hence the frozen
one-point computation supplies the source's strong negative certificate. -/
theorem off_line_strong_negative_certificate
    (rho : ℂ) (delta gamma : ℝ)
    (h_repr : rho = (1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (gamma : ℂ))
    (h_delta : 0 < delta) (h_zero : xiReading rho = 0) :
    ∃ omega : ℝ, 0 < omega ∧ omega < delta ∧
      xiReading (rho - (2 * omega : ℂ)) ≠ 0 ∧
      (let zrho : ℂ := -(gamma : ℂ) + Complex.I * ((delta - omega : ℝ) : ℂ)
       diagonalValue omega zrho = -1 / (omega * (delta - omega)) ∧
       diagonalValue omega zrho < 0 ∧
       diagonalValue omega zrho ≤ -4 / delta ^ 2) := by
  let h : ℂ → ℂ := fun t => xiReading (rho - 2 * t)
  have h_differentiable : Differentiable ℂ h := by
    dsimp only [h]
    exact xi_reading_differentiable.comp (by fun_prop)
  have h_analytic : AnalyticOnNhd ℂ h Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_differentiable
  have h_at_half_rho : h (rho / 2) ≠ 0 := by
    have hxi_zero : xiReading (0 : ℂ) ≠ 0 := by
      unfold xiReading
      norm_num
    dsimp only [h]
    rw [show rho - 2 * (rho / 2) = 0 by ring]
    exact hxi_zero
  let center : ℂ := ((delta / 2 : ℝ) : ℂ)
  rcases (h_analytic center (Set.mem_univ center)).eventually_eq_zero_or_eventually_ne_zero with
    h_locally_zero | h_isolated
  · have h_identically_zero : h = fun _ => 0 :=
      h_analytic.eq_of_eventuallyEq analyticOnNhd_const h_locally_zero
    exact (h_at_half_rho (by simpa using congrFun h_identically_zero (rho / 2))).elim
  · let omegaSeq : ℕ → ℝ := fun n =>
      delta / 2 + delta / 4 * (1 / ((n : ℝ) + 1))
    have h_inv :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h_seq_real : Tendsto omegaSeq atTop (nhds (delta / 2)) := by
      dsimp only [omegaSeq]
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul h_inv)
    have h_seq_complex :
        Tendsto (fun n => (omegaSeq n : ℂ)) atTop (nhds center) := by
      simpa only [center] using h_seq_real.ofReal
    have h_seq_ne_center (n : ℕ) : (omegaSeq n : ℂ) ≠ center := by
      have h_term_pos :
          0 < delta / 4 * (1 / ((n : ℝ) + 1)) := by
        positivity
      have h_real_ne : omegaSeq n ≠ delta / 2 := by
        dsimp only [omegaSeq]
        nlinarith
      dsimp only [center]
      exact fun h_eq => h_real_ne (Complex.ofReal_inj.mp h_eq)
    have h_seq_punctured :
        Tendsto (fun n => (omegaSeq n : ℂ)) atTop (nhdsWithin center {center}ᶜ) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨h_seq_complex, Filter.Eventually.of_forall fun n => by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using h_seq_ne_center n⟩
    obtain ⟨n, hn⟩ := (h_seq_punctured.eventually h_isolated).exists
    have h_inv_pos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h_inv_le_one : 1 / ((n : ℝ) + 1) ≤ 1 := by
      exact (div_le_one (by positivity)).2 (by norm_num)
    have h_delta_div_four : 0 < delta / 4 :=
      div_pos h_delta (by norm_num)
    have h_omega_pos : 0 < omegaSeq n := by
      dsimp only [omegaSeq]
      nlinarith [mul_pos h_delta_div_four h_inv_pos]
    have h_term_le : delta / 4 * (1 / ((n : ℝ) + 1)) ≤ delta / 4 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left h_inv_le_one h_delta_div_four.le
    have h_omega_lt : omegaSeq n < delta := by
      dsimp only [omegaSeq]
      nlinarith
    have h_shift : xiReading (rho - (2 * omegaSeq n : ℂ)) ≠ 0 := by
      simpa only [h] using hn
    refine ⟨omegaSeq n, h_omega_pos, h_omega_lt, h_shift, ?_⟩
    exact off_line_one_point_pick_witness rho delta gamma (omegaSeq n)
      h_repr h_delta h_omega_pos h_omega_lt h_zero h_shift

end D5.S3.Weil.ZetaCore.OffLineStrongNegativeCertificate
