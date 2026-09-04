/- GID: D5/S3/Zeros/CriticalZeroTransverseGap
   generality: I
   mirror-B: D5/B/S3/Zeros/CriticalZeroTransverseGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A critical-line zero has its first positive normal jet at its multiplicity. -/

import D5.S3.Zeros.NormalJetFormula
import Mathlib.Analysis.Calculus.Taylor

/- Library-search audit trail (2026-09-02):
   * Repository searches found the canonical critical-line reading, normal intensity, and normal
     jet in `NormalJetFormula`, but no theorem exposing the four transverse-gap clauses.
   * Pinned Mathlib has no exact whole-statement theorem. The proof applies
     `taylor_isLittleO_univ`, `IsLittleO.isBigO`, and `iteratedDeriv_comp_neg`. -/

noncomputable section

namespace D5.S3.Zeros.CriticalZeroTransverseGap

open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.NormalJetFormula
open D5.S3.Zeros.Symmetry.ZetaConjugationCovariance
open Filter Set
open Asymptotics
open scoped ComplexConjugate Topology

/-- At a zero of multiplicity `r`, every lower normal jet vanishes, the depth-`r` jet is the
positive square of the leading tangential coefficient, and the actual normal intensity has the
corresponding transverse asymptotic. The last conjunct records the simple-zero specialization. -/
theorem critical_zero_transverse_gap (r : ℕ) (hr : 0 < r) (t0 : ℝ)
    (hvanish : ∀ j < r, iteratedDeriv j criticalXi t0 = 0)
    (hlead : iteratedDeriv r criticalXi t0 ≠ 0) :
    (∀ m < r, normalJet t0 m = 0) ∧
    normalJet t0 r =
      (iteratedDeriv r criticalXi t0 / (r.factorial : ℝ)) ^ 2 ∧
    0 < normalJet t0 r ∧
    (fun delta : ℝ =>
        normalIntensity delta t0 -
          (iteratedDeriv r criticalXi t0 / (r.factorial : ℝ)) ^ 2 *
            delta ^ (2 * r))
      =O[𝓝 0] (fun delta : ℝ => delta ^ (2 * r + 2)) ∧
    (r = 1 →
      (fun delta : ℝ =>
          normalIntensity delta t0 - iteratedDeriv 1 criticalXi t0 ^ 2 * delta ^ 2)
        =O[𝓝 0] (fun delta : ℝ => delta ^ 4)) := by
  have hformula := (normal_jet_formula t0).1
  have hjetLow : ∀ m < r, normalJet t0 m = 0 := by
    intro m hm
    rw [hformula m]
    apply Finset.sum_eq_zero
    intro j hj
    have hjle : j ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hjr : j < r
    · simp [hvanish j hjr]
    · have hother : 2 * m - j < r := by omega
      simp [hvanish (2 * m - j) hother]
  have hjetLead :
      normalJet t0 r =
        (iteratedDeriv r criticalXi t0 / (r.factorial : ℝ)) ^ 2 := by
    rw [hformula r, Finset.sum_eq_single r]
    · have hsub : 2 * r - r = r := by omega
      rw [hsub]
      have heven : Even (r + r) := ⟨r, rfl⟩
      rw [heven.neg_one_pow]
      field_simp [Nat.factorial_ne_zero]
    · intro j hj hjne
      have hjle : j ≤ 2 * r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      by_cases hjr : j < r
      · simp [hvanish j hjr]
      · have hother : 2 * r - j < r := by omega
        simp [hvanish (2 * r - j) hother]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  have hjetLeadPos : 0 < normalJet t0 r := by
    rw [hjetLead]
    positivity
  let f : ℝ → ℝ := fun delta => normalIntensity delta t0
  have hsmooth : ContDiff ℝ ⊤ f := by
    have hxi : ContDiff ℂ ⊤ xiReading :=
      (xi_reading_differentiable.differentiableOn.analyticOnNhd isOpen_univ).contDiff
    have hline : ContDiff ℝ ⊤ (fun delta : ℝ =>
        (1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (t0 : ℂ)) := by
      exact (contDiff_const.add Complex.ofRealCLM.contDiff).add contDiff_const
    have hpath : ContDiff ℝ ⊤ (fun delta : ℝ =>
        xiReading ((1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (t0 : ℂ))) :=
      (hxi.restrict_scalars ℝ).comp hline
    have hre : ContDiff ℝ ⊤ (fun delta : ℝ =>
        (xiReading ((1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (t0 : ℂ))).re) :=
      Complex.reCLM.contDiff.comp hpath
    have him : ContDiff ℝ ⊤ (fun delta : ℝ =>
        (xiReading ((1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (t0 : ℂ))).im) :=
      Complex.imCLM.contDiff.comp hpath
    change ContDiff ℝ ⊤ (fun delta : ℝ =>
      Complex.normSq
        (xiReading ((1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (t0 : ℂ))))
    simpa only [Complex.normSq_apply] using (hre.mul hre).add (him.mul him)
  have heven : Function.Even f := by
    intro delta
    let s : ℂ := (1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (t0 : ℂ)
    have hs : (1 / 2 : ℂ) + ((-delta : ℝ) : ℂ) + Complex.I * (t0 : ℂ) =
        1 - conj s := by
      apply Complex.ext
      · norm_num [s]
        ring
      · norm_num [s]
    change Complex.normSq
        (xiReading ((1 / 2 : ℂ) + ((-delta : ℝ) : ℂ) + Complex.I * (t0 : ℂ))) =
      Complex.normSq (xiReading s)
    rw [hs, xi_reading_one_sub_conj, Complex.normSq_conj]
  have hodd (n : ℕ) (hn : Odd n) : iteratedDeriv n f 0 = 0 := by
    have hfunctions : (fun delta : ℝ => f (-delta)) = f := funext heven
    have hderiv := congrFun (congrArg (iteratedDeriv n) hfunctions) 0
    rw [iteratedDeriv_comp_neg] at hderiv
    simp only [neg_zero, hn.neg_one_pow, neg_smul, one_smul] at hderiv
    linarith
  have hderivLow (k : ℕ) (hk : k < 2 * r) : iteratedDeriv k f 0 = 0 := by
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
    · subst k
      have hmr : m < r := by omega
      have hj := hjetLow m hmr
      simpa [normalJet, f, Nat.factorial_ne_zero] using hj
    · subst k
      exact hodd (2 * m + 1) (by simp)
  have hderivNext : iteratedDeriv (2 * r + 1) f 0 = 0 :=
    hodd (2 * r + 1) (by simp)
  have htaylorLead (delta : ℝ) :
      taylorWithinEval f (2 * r + 1) univ 0 delta =
        (iteratedDeriv r criticalXi t0 / (r.factorial : ℝ)) ^ 2 *
          delta ^ (2 * r) := by
    rw [taylor_within_apply, Finset.sum_eq_single (2 * r)]
    · simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
      have hcoefficient :
          ((2 * r).factorial : ℝ)⁻¹ * iteratedDeriv (2 * r) f 0 =
            (iteratedDeriv r criticalXi t0 / (r.factorial : ℝ)) ^ 2 := by
        have hj := hjetLead
        rw [normalJet] at hj
        simpa [f, div_eq_inv_mul] using hj
      calc
        ((2 * r).factorial : ℝ)⁻¹ * delta ^ (2 * r) *
              iteratedDeriv (2 * r) f 0 =
            (((2 * r).factorial : ℝ)⁻¹ * iteratedDeriv (2 * r) f 0) *
              delta ^ (2 * r) := by ring
        _ = _ := by rw [hcoefficient]
    · intro k hk hne
      have hklt : k < 2 * r ∨ k = 2 * r + 1 := by
        have := Finset.mem_range.mp hk
        omega
      rcases hklt with hklt | rfl
      · simp [iteratedDerivWithin_univ, hderivLow k hklt]
      · simp [iteratedDerivWithin_univ, hderivNext]
    · simp
  have hpoly (delta : ℝ) :
      taylorWithinEval f (2 * r + 2) univ 0 delta =
        (iteratedDeriv r criticalXi t0 / (r.factorial : ℝ)) ^ 2 *
            delta ^ (2 * r) +
          ((2 * r + 2).factorial : ℝ)⁻¹ *
            iteratedDeriv (2 * r + 2) f 0 * delta ^ (2 * r + 2) := by
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, taylorWithinEval_succ,
      htaylorLead]
    simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
    have hfactorial :
        (((2 * r + 1 : ℕ) : ℝ) + 1) * ((2 * r + 1).factorial : ℝ) =
          ((2 * r + 1 + 1).factorial : ℝ) := by
      norm_cast
    rw [hfactorial]
    ring
  have hremainder :
      (fun delta : ℝ => f delta - taylorWithinEval f (2 * r + 2) univ 0 delta)
        =O[𝓝 0] (fun delta : ℝ => delta ^ (2 * r + 2)) :=
    by
      simpa only [sub_zero] using
        (taylor_isLittleO_univ (n := 2 * r + 2) (x₀ := 0)
          (hsmooth.of_le (by simp))).isBigO
  have hfinalTerm :
      (fun delta : ℝ =>
          ((2 * r + 2).factorial : ℝ)⁻¹ * iteratedDeriv (2 * r + 2) f 0 *
            delta ^ (2 * r + 2))
        =O[𝓝 0] (fun delta : ℝ => delta ^ (2 * r + 2)) := by
    exact (isBigO_refl (fun delta : ℝ => delta ^ (2 * r + 2)) (𝓝 0)).const_mul_left _
  have hasymptotic :
      (fun delta : ℝ =>
          normalIntensity delta t0 -
            (iteratedDeriv r criticalXi t0 / (r.factorial : ℝ)) ^ 2 *
              delta ^ (2 * r))
        =O[𝓝 0] (fun delta : ℝ => delta ^ (2 * r + 2)) := by
    refine (hremainder.add hfinalTerm).congr_left ?_
    intro delta
    rw [hpoly delta]
    simp only [f]
    ring
  refine ⟨hjetLow, hjetLead, hjetLeadPos, hasymptotic, ?_⟩
  intro hrOne
  subst r
  simpa using hasymptotic

end D5.S3.Zeros.CriticalZeroTransverseGap
