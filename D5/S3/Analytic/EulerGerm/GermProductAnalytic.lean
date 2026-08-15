/- GID: D5/S3/Analytic/EulerGerm/GermProductAnalytic
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden Euler germ prime product is analytic on its convergence half-plane. -/

import Mathlib
import D5.S3.Analytic.EulerGerm.GermProductConvergence

/- Provenance: Native proof over pinned mathlib. -/
/- SEARCH RECEIPT (2026-08-15): searched the repository D5 tree for
   `germLocalFactor`, `germ_excited_norm_summable`,
   `germLocalFactor_eq_one_add`, `germLocalFactor_multipliable`, and existing
   locally-uniform product arguments. Reused the first three declarations from
   the frozen Euler-germ files; the last is not needed as a premise because the
   locally uniform M-test below proves the stronger convergence statement.

   Read pinned mathlib source at
   `Mathlib/Analysis/Complex/LocallyUniformLimit.lean:135-137` for
   `TendstoLocallyUniformlyOn.differentiableOn`, and at lines 170-177 for
   `differentiableOn_tsum_of_summable_norm`. Read
   `Mathlib/Analysis/Normed/Module/MultipliableUniformlyOn.lean:130-140` for
   `hasProdLocallyUniformlyOn_one_add` and its locally uniform product bound.
   Read `Mathlib/Topology/Algebra/InfiniteSum/UniformOn.lean:145-164`, where
   `HasProdLocallyUniformlyOn` is definitionally a
   `TendstoLocallyUniformlyOn` of finite products. Read the direct power-norm
   comparison at `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:950-954`,
   and the holomorphy conversion at
   `Mathlib/Analysis/Complex/CauchyIntegral.lean:625-632`.

   The repository near-neighbor
   `D5/S3/Weil/ZetaGamma/GammaSeries.lean:422-429` uses differentiability of
   the factors of an infinite product indexed by the naturals, not by the
   primes, and has no reusable theorem for this germ. No direct
   theorem for analyticity of this prime product was found. -/

namespace D5.S3.Analytic.EulerGerm.GermProductAnalytic

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GermProductConvergence

noncomputable section

private theorem o5Beta_nonneg (v : ℕ) : 0 ≤ o5Beta v := by
  cases v with
  | zero => rw [o5_beta_zero]
  | succ v =>
      have hgrowth := o5_beta_growth (v + 1)
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt : 1 < Real.sqrt 5 := by nlinarith
      have hinv : 0 < 1 / Real.goldenRatio := one_div_pos.mpr Real.goldenRatio_pos
      have hv : (1 : ℝ) ≤ (v + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le v)
      have hmul : Real.sqrt 5 ≤ Real.sqrt 5 * (v + 1 : ℕ) := by
        nlinarith
      nlinarith

private theorem germ_mode_norm_le (p : Nat.Primes) {σ : ℝ} {s : ℂ}
    (hs : σ < s.re) (v : ℕ) :
    ‖(p : ℂ) ^ (-s * (o5Beta v : ℂ))‖ ≤
      ‖(p : ℂ) ^ (-(σ : ℂ) * (o5Beta v : ℂ))‖ := by
  apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.prop.pos
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith [o5Beta_nonneg v]

private theorem germLocalFactor_differentiableOn (p : Nat.Primes) (σ : ℝ)
    (hσ : 1 / Real.goldenRatio ^ 2 < σ) :
    DifferentiableOn ℂ (fun s : ℂ => germLocalFactor s p) {s : ℂ | σ < s.re} := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  let u : ℕ → ℝ := fun v =>
    ‖(p : ℂ) ^ (-(σ : ℂ) * (o5Beta v : ℂ))‖
  have htail : Summable (fun v : ℕ =>
      ‖(p : ℂ) ^ (-(σ : ℂ) * (o5Beta (v + 1) : ℂ))‖) := by
    simpa using
      ((germ_excited_norm_summable (σ : ℂ) (by simpa using hσ)).prod_factor p)
  have hu : Summable u := by
    apply (summable_nat_add_iff (f := u) 1).1
    simpa [u, Nat.add_comm] using htail
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hterms : ∀ v : ℕ,
      DifferentiableOn ℂ (fun s : ℂ =>
        (p : ℂ) ^ (-s * (o5Beta v : ℂ))) U := by
    intro v
    have hbase : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    exact ((differentiable_id.neg.mul_const (o5Beta v : ℂ)).const_cpow
      (.inl hbase)).differentiableOn
  have hsum := Complex.differentiableOn_tsum_of_summable_norm hu hterms hU
    (fun v s hs => germ_mode_norm_le p hs v)
  simpa [germLocalFactor, U] using hsum

private theorem germProduct_differentiableOn (σ : ℝ)
    (hσ : 1 / Real.goldenRatio ^ 2 < σ) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∏' p : Nat.Primes, germLocalFactor s p)
      {s : ℂ | σ < s.re} := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  let f : Nat.Primes → ℂ → ℂ := fun p s => germLocalFactor s p - 1
  let u : Nat.Primes → ℝ := fun p =>
    ∑' v : ℕ, ‖(p : ℂ) ^ (-(σ : ℂ) * (o5Beta (v + 1) : ℂ))‖
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hnorm : Summable (fun q : Nat.Primes × ℕ =>
      ‖(q.1 : ℂ) ^ (-(σ : ℂ) * (o5Beta (q.2 + 1) : ℂ))‖) := by
    simpa using germ_excited_norm_summable (σ : ℂ) (by simpa using hσ)
  have hu : Summable u := by
    simpa [u] using hnorm.prod
  have hbound : ∀ p : Nat.Primes, ∀ s ∈ U, ‖f p s‖ ≤ u p := by
    intro p s hs
    have hsσ : σ < s.re := hs
    have hsHalf : 1 / Real.goldenRatio ^ 2 < s.re := lt_trans hσ hsσ
    have hsNorm : Summable (fun v : ℕ =>
        ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖) := by
      exact (germ_excited_norm_summable s hsHalf).prod_factor p
    have hσNorm : Summable (fun v : ℕ =>
        ‖(p : ℂ) ^ (-(σ : ℂ) * (o5Beta (v + 1) : ℂ))‖) := by
      exact hnorm.prod_factor p
    change ‖germLocalFactor s p - 1‖ ≤ u p
    rw [germLocalFactor_eq_one_add s p p.prop hsHalf]
    simp only [add_sub_cancel_left]
    refine (norm_tsum_le_tsum_norm hsNorm).trans ?_
    exact hsNorm.tsum_le_tsum (fun v => germ_mode_norm_le p hsσ (v + 1)) hσNorm
  have hcts : ∀ p : Nat.Primes, ContinuousOn (f p) U := by
    intro p
    simpa [Pi.sub_def, f, U] using (germLocalFactor_differentiableOn p σ hσ).continuousOn.sub
      (continuousOn_const : ContinuousOn (fun _ : ℂ => (1 : ℂ)) U)
  have hprod := hu.hasProdLocallyUniformlyOn_one_add hU
    (Filter.Eventually.of_forall hbound) hcts
  have hfinite : ∀ J : Finset Nat.Primes,
      DifferentiableOn ℂ (fun s : ℂ => ∏ p ∈ J, (1 + f p s)) U := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
        simp only [Finset.prod_empty]
        exact (differentiableOn_const (1 : ℂ) :
          DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) U)
    | @insert p J hp ih =>
        simp only [Finset.prod_insert hp]
        have hfactor : DifferentiableOn ℂ (fun s : ℂ => 1 + f p s) U := by
          simpa [f] using germLocalFactor_differentiableOn p σ hσ
        exact hfactor.mul ih
  have hlimit := hprod.differentiableOn (Filter.Eventually.of_forall hfinite) hU
  simpa [f, U] using hlimit

/-- The golden Euler germ prime product is holomorphic throughout its full
convergence half-plane. -/
theorem germProduct_analyticOnNhd :
    AnalyticOnNhd ℂ (fun s : ℂ => ∏' p : Nat.Primes, germLocalFactor s p)
      {s : ℂ | 1 / Real.goldenRatio ^ 2 < s.re} := by
  intro s hs
  change 1 / Real.goldenRatio ^ 2 < s.re at hs
  let σ : ℝ := (1 / Real.goldenRatio ^ 2 + s.re) / 2
  have hσ : 1 / Real.goldenRatio ^ 2 < σ := by
    dsimp [σ]
    linarith
  have hsσ : σ < s.re := by
    dsimp [σ]
    linarith
  have hU : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact (germProduct_differentiableOn σ hσ).analyticAt (hU.mem_nhds hsσ)

end

end D5.S3.Analytic.EulerGerm.GermProductAnalytic
