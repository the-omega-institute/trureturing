/- GID: D5/S3/Analytic/Resolvent/XiGlobalGrowth
   generality: I
   mirror-B: D5/B/S3/Analytic/Resolvent/XiGlobalGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the actual pole-removed xi function uniformly on the complex plane. -/

import D5.S3.Analytic.CompletedZetaMellinReconstruction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
The compact-to-tail argument in `theta_tail_global` is adapted from
`Lc/LiCriterion/XiGrowth.lean` in nicholasbulka/li-criterion-rh-equivalence-lean,
revision `35df682f3b709ffe5fbcfdd452dfa964bd622b87`.

Copyright 2026 Nicholas Bulka

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. The full terms are in the repository-root
`LICENSE`; the upstream archive has no NOTICE file.
Authors: Nicholas Bulka.

Modified for this repository's Lean 4.33.0 / Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`: the imported source's whole-line
modified-kernel development is replaced by the already-frozen symmetric
theta-tail reconstruction, and only the live compact-to-tail construction is
retained. Replace this
adapted construction with a direct import only when a dependency accepted by
this repository's pinned manifest exports the same uniform theta-tail bound.
-/

noncomputable section

namespace D5.S3.Analytic.Resolvent.XiGlobalGrowth

open MeasureTheory Set Filter Topology

private theorem theta_tail_global :
    ∃ B p : ℝ, 0 < B ∧ 0 < p ∧ ∀ t : ℝ, 1 ≤ t →
      |HurwitzZeta.evenKernel 0 t - 1| ≤ B * Real.exp (-p * t) := by
  obtain ⟨p, hp, hO⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub 0
  obtain ⟨b, hb⟩ := hO.bound
  obtain ⟨T, hT⟩ := eventually_atTop.1 hb
  let T' : ℝ := max T 1
  have hcompact : IsCompact (Icc (1 : ℝ) T') := isCompact_Icc
  have hcont : ContinuousOn (fun t : ℝ => HurwitzZeta.evenKernel 0 t - 1)
      (Icc (1 : ℝ) T') := by
    refine ContinuousOn.sub ?_ continuousOn_const
    exact (HurwitzZeta.continuousOn_evenKernel 0).mono
      (fun t ht => lt_of_lt_of_le zero_lt_one ht.1)
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max (max b 0) (max (M * Real.exp (p * T')) 0) + 1, p, by positivity, hp, ?_⟩
  intro t ht
  let B := max (max b 0) (max (M * Real.exp (p * T')) 0) + 1
  change |HurwitzZeta.evenKernel 0 t - 1| ≤ B * Real.exp (-p * t)
  rcases le_or_gt t T' with htt | htt
  · have h1 : |HurwitzZeta.evenKernel 0 t - 1| ≤ M := by
      simpa using hM t ⟨ht, htt⟩
    have h2 : M * Real.exp (p * T') * Real.exp (-p * t) ≤
        B * Real.exp (-p * t) := by
      have : M * Real.exp (p * T') ≤ B := by
        have hleft := le_max_left (M * Real.exp (p * T')) 0
        have hright := le_max_right (max b 0) (max (M * Real.exp (p * T')) 0)
        dsimp [B]
        linarith [le_trans hleft hright]
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    refine h1.trans ?_ |>.trans h2
    have hexp : (1 : ℝ) ≤ Real.exp (p * T') * Real.exp (-p * t) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    nlinarith [abs_nonneg (HurwitzZeta.evenKernel 0 t - 1),
      Real.exp_pos (p * T'), Real.exp_pos (-p * t)]
  · have htT : T ≤ t := (le_max_left T 1).trans htt.le
    have h1 : ‖HurwitzZeta.evenKernel 0 t - 1‖ ≤
        b * ‖Real.exp (-p * t)‖ := by
      simpa using hT t htT
    have hbB : b ≤ B := by
      have hleft := le_max_left b 0
      have hright := le_max_left (max b 0) (max (M * Real.exp (p * T')) 0)
      dsimp [B]
      linarith [le_trans hleft hright]
    have hnorm : ‖Real.exp (-p * t)‖ = Real.exp (-p * t) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.norm_eq_abs, hnorm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hbB (Real.exp_pos _).le)

private theorem parameter_log_bound (q : ℝ) (hq : 0 < q) :
    ∃ D : ℝ, 0 < D ∧ ∀ r t : ℝ, 1 ≤ r → 0 < t →
      r * Real.log t ≤ q * t + D * r * (1 + Real.log r) := by
  refine ⟨2 + |Real.log q|, by positivity, ?_⟩
  intro r t hr ht
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos hq ht) hr0)
  rw [Real.log_div (mul_pos hq ht).ne' hr0.ne', Real.log_mul hq.ne' ht.ne'] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hr0.le
  have hcancel : r * (q * t / r - 1) = q * t - r := by field_simp
  rw [hcancel] at hscaled
  have hqlog := neg_abs_le (Real.log q)
  have hqmul := mul_le_mul_of_nonneg_left hqlog hr0.le
  have hcross : 0 ≤ |Real.log q| * r * Real.log r := by positivity
  nlinarith

private theorem symmetric_power_bound (s : ℂ) (t : ℝ) (ht : 1 < t) :
    ‖(t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)‖ ≤
      2 * Real.exp ((1 + ‖s‖) * Real.log t) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hpow (z : ℂ) (hz : z.re ≤ 1 + ‖s‖) :
      ‖(t : ℂ) ^ z‖ ≤ Real.exp ((1 + ‖s‖) * Real.log t) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Real.rpow_def_of_pos ht0]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.log_nonneg ht.le]
  have h1 := hpow (s / 2) (by
    simp only [Complex.div_ofNat_re]
    nlinarith [Complex.re_le_norm s, norm_nonneg s])
  have h2 := hpow ((1 - s) / 2) (by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    nlinarith [Complex.abs_re_le_norm s, neg_abs_le s.re, norm_nonneg s])
  exact (norm_add_le _ _).trans (by linarith)

private theorem theta_mellin_uniform_majorant :
  ∃ A p D : ℝ, 0 < A ∧ 0 < p ∧ 0 < D ∧
    ∀ s : ℂ, ∀ t : ℝ, 1 < t →
      ‖((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2) *
        ((t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)) / (t : ℂ)‖ ≤
        A * Real.exp (D * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖))) *
          Real.exp (-(p / 2) * t) := by
  obtain ⟨B, p, hB, hp, htail⟩ := theta_tail_global
  obtain ⟨D, hD, hparam⟩ := parameter_log_bound (p / 2) (by positivity)
  refine ⟨B, p, D, hB, hp, hD, ?_⟩
  intro s t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hnorm : ‖(((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2‖ =
      |HurwitzZeta.evenKernel 0 t - 1| / 2 := by
    rw [norm_div, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
    norm_num
  have hb := mul_le_mul (htail t ht.le) (symmetric_power_bound s t ht)
    (norm_nonneg _) (by positivity : 0 ≤ B * Real.exp (-p * t))
  have hnum : ‖(((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2‖ *
      ‖(t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)‖ ≤
      B * Real.exp (-p * t) * Real.exp ((1 + ‖s‖) * Real.log t) := by
    rw [hnorm]; nlinarith
  have hdiv : ‖((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2) *
      ((t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)) / (t : ℂ)‖ ≤
      B * Real.exp (-p * t) * Real.exp ((1 + ‖s‖) * Real.log t) := by
    rw [norm_div, norm_mul, Complex.norm_of_nonneg ht0.le]
    exact (div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ht.le).trans hnum
  apply hdiv.trans
  rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hB.le
  apply Real.exp_le_exp.mpr
  have h := hparam (1 + ‖s‖) t (by linarith [norm_nonneg s]) ht0
  linarith

private theorem completed_integral_bound :
    ∃ K D : ℝ, 0 < K ∧ 0 < D ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤
        K * Real.exp (D * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖))) := by
  obtain ⟨A, p, D, hA, hp, hD, hmajor⟩ := theta_mellin_uniform_majorant
  have hpneg : -(p / 2) < 0 := by linarith
  refine ⟨A * (Real.exp (-(p / 2)) / (p / 2)), D, by positivity, hD, ?_⟩
  intro s
  have hmellin :
      (∫ t in Ioi (1 : ℝ), ((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2) *
        ((t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)) / (t : ℂ)) =
        completedRiemannZeta₀ s := by
    have h := CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction.2.1 s
    change completedRiemannZeta s = _ at h
    rw [completedRiemannZeta_eq] at h
    exact (sub_left_inj.mp (sub_left_inj.mp h)).symm
  rw [← hmellin]
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi hpneg 1).const_mul
      (A * Real.exp (D * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖)))))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall
      (fun t ht => hmajor s t ht)))
  refine h.trans_eq ?_
  rw [integral_const_mul, integral_exp_mul_Ioi hpneg]
  simp only [mul_one, neg_div_neg_eq]
  ring

/-- The classical pole-removed xi reading has a global order-one exponential bound. -/
theorem xi_reading_norm_le_exp_log_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖D5.S3.Zeros.CompletedZeta.xiReading s‖ ≤
        Real.exp (C * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖))) := by
  obtain ⟨K, D, hK, hD, hbound⟩ := completed_integral_bound
  refine ⟨D + K + 3, by positivity, ?_⟩
  intro s
  let r := 1 + ‖s‖
  let L := r * (1 + Real.log r)
  have hr : 1 ≤ r := by dsimp [r]; linarith [norm_nonneg s]
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hrL : r ≤ L := by dsimp [L]; nlinarith
  have hL : 1 ≤ L := hr.trans hrL
  have hn : ‖s‖ ≤ r := by dsimp [r]; linarith
  have hn1 : ‖s - 1‖ ≤ r := by
    simpa [r, add_comm] using norm_sub_le s (1 : ℂ)
  have hpoly : ‖s * (s - 1)‖ ≤ Real.exp (2 * L) := by
    rw [norm_mul]
    calc
      ‖s‖ * ‖s - 1‖ ≤ r * r := mul_le_mul hn hn1 (norm_nonneg _) hr0.le
      _ ≤ Real.exp L * Real.exp L := mul_le_mul
        (hrL.trans (by linarith [Real.add_one_le_exp L] : L ≤ Real.exp L))
        (hrL.trans (by linarith [Real.add_one_le_exp L] : L ≤ Real.exp L)) hr0.le
        (Real.exp_pos _).le
      _ = Real.exp (2 * L) := by rw [← Real.exp_add]; congr 1; ring
  have hprod : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤
      K * Real.exp ((D + 2) * L) := by
    rw [norm_mul]
    have h := mul_le_mul hpoly (hbound s) (norm_nonneg _) (Real.exp_pos _).le
    refine h.trans_eq ?_
    dsimp only [L, r]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hexp : 1 ≤ Real.exp ((D + 2) * L) := Real.one_le_exp (by positivity)
  have hxi : ‖D5.S3.Zeros.CompletedZeta.xiReading s‖ ≤
      (K + 1) * Real.exp ((D + 2) * L) := by
    rw [D5.S3.Zeros.CompletedZeta.xiReading, norm_mul]
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    have h := norm_add_le (s * (s - 1) * completedRiemannZeta₀ s) (1 : ℂ)
    norm_num only [norm_one] at h
    nlinarith
  apply hxi.trans
  have hconst : K + 1 ≤ Real.exp ((K + 1) * L) :=
    (by linarith [Real.add_one_le_exp (K + 1)] : K + 1 ≤ Real.exp (K + 1)).trans
      (Real.exp_le_exp.mpr (by nlinarith))
  calc
    (K + 1) * Real.exp ((D + 2) * L) ≤
        Real.exp ((K + 1) * L) * Real.exp ((D + 2) * L) :=
      mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le
    _ = Real.exp ((D + K + 3) * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖))) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [L, r]
      ring

#print axioms xi_reading_norm_le_exp_log_linear

end D5.S3.Analytic.Resolvent.XiGlobalGrowth
