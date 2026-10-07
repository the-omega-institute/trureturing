/- GID: D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.FarBand
import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43Uniform

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Lemma43R

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag
open scoped ENNReal NNReal

/-- `n^{1/16}`, as four nested square roots. -/
noncomputable def r16 (n : ℕ) : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))))

theorem r16_pos {n : ℕ} (hn : 0 < (n : ℝ)) : 0 < r16 n :=
  Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 hn)))

theorem r16_pow {n : ℕ} (hn : 0 ≤ (n : ℝ)) : r16 n ^ 16 = (n : ℝ) := by
  have h1 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn
  have h2 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt (n : ℝ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) ^ 2 = Real.sqrt (Real.sqrt (n : ℝ)) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h4 : r16 n ^ 2 = Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  calc r16 n ^ 16 = ((((r16 n ^ 2) ^ 2) ^ 2) ^ 2) := by ring
    _ = (n : ℝ) := by rw [h4, h3, h2, h1]

theorem log_le_r16 {n : ℕ} (hn : 2073600 ≤ n) : Real.log n ≤ 16 * r16 n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have h2 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_pos.2 h1
  have h3 : (0 : ℝ) < Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) := Real.sqrt_pos.2 h2
  have h4 : (0 : ℝ) < r16 n := r16_pos hn0
  have hlog : Real.log (r16 n) = Real.log n / 16 := by
    rw [r16, Real.log_sqrt h3.le, Real.log_sqrt h2.le, Real.log_sqrt h1.le,
      Real.log_sqrt hn0.le]
    ring
  have hle := Real.log_le_sub_one_of_pos h4
  rw [hlog] at hle
  linarith

theorem r16_ge {n : ℕ} (hn : 2073600 ≤ n) : (2.4 : ℝ) ≤ r16 n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h4 : (0 : ℝ) < r16 n := r16_pos hn0
  have hpow : r16 n ^ 16 = (n : ℝ) := r16_pow hn0.le
  by_contra hcon
  push Not at hcon
  have hlt : r16 n ^ 16 ≤ (2.4 : ℝ) ^ 16 := pow_le_pow_left₀ h4.le hcon.le 16
  rw [hpow] at hlt
  norm_num at hlt
  linarith

/-- **The twin of `HJ.junk_endpoint_le_three` at the doubled endpoint.**  `0.0477` against `3` at
`n₁`; the proof budget is `41·(log n)³/n ≤ 3`, i.e. `(log n)³/n ≤ 0.0731`, against an actual
`0.0302` from `log n ≤ 16·n^{1/16}`. -/
theorem junk_endpoint_two_log {n : ℕ} (hn : 2073600 ≤ n) {t : ℝ}
    (hts : Real.sqrt t ≤ 4 * Real.sqrt (Real.log n) / (n : ℝ)) (ht : 0 ≤ t) :
    2 * Real.log n * Real.sqrt t
      + ((n : ℝ) + 2) / 2 * (2 * Real.log n * Real.sqrt t) ^ 2 ≤ 3 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hL1 : (1 : ℝ) ≤ Real.log n := by linarith
  have hsL : (0 : ℝ) ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
  have hsL2 : Real.sqrt (Real.log n) ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  have hst : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hst2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht

  have hsLle : Real.sqrt (Real.log n) ≤ Real.log n := by nlinarith [hsL, hsL2, hL1]
  have hlin : 2 * Real.log n * Real.sqrt t ≤ 8 * Real.log n ^ 3 / (n : ℝ) := by
    have h1 : Real.sqrt t ≤ 4 * Real.log n / (n : ℝ) := by
      refine le_trans hts ?_
      rw [div_le_div_iff₀ hn0 hn0]; nlinarith [hsLle, hn0]
    have h2 : 2 * Real.log n * Real.sqrt t ≤ 2 * Real.log n * (4 * Real.log n / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    refine le_trans h2 ?_
    rw [show 2 * Real.log n * (4 * Real.log n / (n : ℝ)) = 8 * Real.log n ^ 2 / (n : ℝ) by ring,
      div_le_div_iff₀ hn0 hn0]
    have hL23 : Real.log n ^ 2 ≤ Real.log n ^ 3 := by nlinarith [hL1]
    nlinarith [hL23, hn0]
  have htle : t ≤ 16 * Real.log n / (n : ℝ) ^ 2 := by
    have h1 : Real.sqrt t ^ 2 ≤ (4 * Real.sqrt (Real.log n) / (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hst hts 2
    rw [hst2, div_pow, mul_pow, hsL2] at h1
    calc t ≤ 4 ^ 2 * Real.log n / (n : ℝ) ^ 2 := h1
      _ = 16 * Real.log n / (n : ℝ) ^ 2 := by norm_num
  have hquad : ((n : ℝ) + 2) / 2 * (2 * Real.log n * Real.sqrt t) ^ 2
      ≤ 33 * Real.log n ^ 3 / (n : ℝ) := by
    have hexp : (2 * Real.log n * Real.sqrt t) ^ 2 = 4 * Real.log n ^ 2 * t := by
      rw [mul_pow, mul_pow, hst2]; ring
    rw [hexp]
    have hb : 4 * Real.log n ^ 2 * t ≤ 4 * Real.log n ^ 2 * (16 * Real.log n / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left htle (by positivity)
    have hfac : ((n : ℝ) + 2) / 2 * (4 * Real.log n ^ 2 * (16 * Real.log n / (n : ℝ) ^ 2))
        = 32 * ((n : ℝ) + 2) * Real.log n ^ 3 / (n : ℝ) ^ 2 := by field_simp; ring
    calc ((n : ℝ) + 2) / 2 * (4 * Real.log n ^ 2 * t)
        ≤ ((n : ℝ) + 2) / 2 * (4 * Real.log n ^ 2 * (16 * Real.log n / (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 32 * ((n : ℝ) + 2) * Real.log n ^ 3 / (n : ℝ) ^ 2 := hfac
      _ ≤ 33 * Real.log n ^ 3 / (n : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) hn0]
          have hkey : 0 ≤ (33 * (n : ℝ) - 32 * ((n : ℝ) + 2)) * (Real.log n ^ 3 * (n : ℝ)) :=
            mul_nonneg (by linarith) (by positivity)
          nlinarith [hkey]

  have hcube : Real.log n ^ 3 ≤ 4096 * r16 n ^ 3 := by
    have h := log_le_r16 hn
    have h0 : (0 : ℝ) ≤ Real.log n := by linarith
    calc Real.log n ^ 3 ≤ (16 * r16 n) ^ 3 := pow_le_pow_left₀ h0 h 3
      _ = 4096 * r16 n ^ 3 := by ring
  have hpow : r16 n ^ 16 = (n : ℝ) := r16_pow hn0.le
  have hr : (2.4 : ℝ) ≤ r16 n := r16_ge hn
  have hr0 : (0 : ℝ) < r16 n := r16_pos hn0
  have h13 : (2.4 : ℝ) ^ 13 ≤ r16 n ^ 13 := pow_le_pow_left₀ (by norm_num) hr 13
  have hn16 : r16 n ^ 13 * r16 n ^ 3 = (n : ℝ) := by rw [← hpow]; ring
  have hstep : 41 * Real.log n ^ 3 ≤ 167936 * r16 n ^ 3 := by nlinarith [hcube]
  have h24 : (87000 : ℝ) ≤ r16 n ^ 13 := le_trans (by norm_num) h13
  have hfin : 41 * (Real.log n ^ 3 / (n : ℝ)) ≤ 3 := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ hn0]
    calc 41 * Real.log n ^ 3 ≤ 167936 * r16 n ^ 3 := hstep
      _ ≤ 3 * (r16 n ^ 13 * r16 n ^ 3) := by nlinarith [h24, pow_pos hr0 3]
      _ = 3 * (n : ℝ) := by rw [hn16]
  have hlin' : 2 * Real.log n * Real.sqrt t ≤ 8 * (Real.log n ^ 3 / (n : ℝ)) := by
    rw [mul_div_assoc'] at *; linarith [hlin]
  have hquad' : ((n : ℝ) + 2) / 2 * (2 * Real.log n * Real.sqrt t) ^ 2
      ≤ 33 * (Real.log n ^ 3 / (n : ℝ)) := by
    rw [mul_div_assoc'] at *; linarith [hquad]
  linarith [hlin', hquad', hfin]

/-- **The four-piece radial bound.**  `pieces_at_params` on `(0, Ymid]` and `FarBand.far_le` on
`(Ymid, Y1]`, summed.  The far band contributes at most `1`, so `K` becomes `K + 1`. -/
theorem pieces_four {t A Ymid Y1 : ℝ} {n : ℕ} (hn : 0 < n) (ht : 0 ≤ t)
    (hts : Real.sqrt t ≤ 1 / 2) (hA1 : 1 ≤ A) (hAY : A ≤ Ymid)
    (hY : Ymid * Real.sqrt t ≤ 1 / 2)
    (hb2 : 2 ≤ (n : ℝ) * Real.sqrt t / 2)
    (hLb : (n : ℝ) * Real.sqrt t / 2 / 2 ≤ A)
    (hbA : (n : ℝ) * Real.sqrt t / 2 ≤ 2 * A)
    (hJ2 : ∀ y ∈ Ioc (1 : ℝ) A,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3)
    (hJ3 : ∀ y ∈ Ioc A Ymid,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3)
    (hmid0 : 0 < Ymid) (hmidY1 : Ymid ≤ Y1) (hY1 : Y1 * Real.sqrt t ≤ 1 / 2)
    (hlam : 0 < 2 * (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid
      - ((n : ℝ) + 2) / 2 * Real.sqrt t)
    (hfar : (n : ℝ) * Real.sqrt t / 2
      * (Real.exp (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid
          - (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid ^ 2)
        / ((2 * (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid
            - ((n : ℝ) + 2) / 2 * Real.sqrt t) * (Real.sqrt (2 * π) * Ymid))) ≤ 1) :
    ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc (0 : ℝ) Y1, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ (Real.exp 6 + Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) + 2 * Real.exp 3 + 1)
        * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have hst : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hp0 : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 2 := by positivity
  have hc0 : (0 : ℝ) ≤ ((n : ℝ) + 2) / 2 := by positivity
  have hint1 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)))
      (Ioc (0 : ℝ) Ymid) := integrableOn_pieces (n := n) le_rfl hY
  have hint2 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)))
      (Ioc Ymid Y1) := integrableOn_pieces (n := n) hmid0.le hY1
  have hint0 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)))
      (Ioc (0 : ℝ) (0 : ℝ)) := by simp
  have hsplit := setIntegral_Ioc_split₃ (f := fun y : ℝ =>
      Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)))
    (le_refl (0 : ℝ)) hmid0.le hmidY1 hint0 hint1 hint2
  have hzero : ∫ y in Ioc (0 : ℝ) (0 : ℝ),
      Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)) = 0 := by simp
  rw [hzero, zero_add] at hsplit
  have hnear := pieces_at_params (n := n) hn ht hts hA1 hAY hY hb2 hLb hbA hJ2 hJ3
  have hfarb := FarBand.far_le (s := Real.sqrt t) (c := ((n : ℝ) + 2) / 2) (Y₀ := Ymid)
    (Y₁ := Y1) (p := (n : ℝ) * Real.sqrt t / 2) hst hc0 hmid0 hp0 hY1 hlam hint2
  have hexp1 : (1 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2 * t / 8) := Real.one_le_exp (by positivity)
  rw [hsplit, mul_add]
  have hfar2 : (n : ℝ) * Real.sqrt t / 2
      * ∫ y in Ioc Ymid Y1, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ 1 * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
    refine le_trans (le_trans hfarb hfar) ?_
    linarith
  linarith [hnear, hfar2]

/-- `log n·√T ≤ 1/4` — the quarter version of `Lemma43Uniform.logn_sqrtT_le`, needed because the
split point is `2·log n`. -/
theorem logn_sqrtT_le_quarter {n : ℕ} (hn : 2073600 ≤ n) :
    Real.log n * Real.sqrt (ChainDrift.horizon n) ≤ 1 / 4 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := by linarith [six_le_log hn]
  have hTnn : (0 : ℝ) ≤ ChainDrift.horizon n := (horizon_pos (by omega)).le
  have hcube : (Real.log n) ^ 3 ≤ 216 * Real.sqrt n := log_cube_le (by omega)
  have hsn : (1440 : ℝ) ≤ Real.sqrt n := by
    rw [show (1440 : ℝ) = Real.sqrt (1440 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0.le
  have h256 : 256 * (Real.log n) ^ 3 ≤ (n : ℝ) ^ 2 := by nlinarith [hcube, hsn, hsq]
  have hsqeq : (Real.log n * Real.sqrt (ChainDrift.horizon n)) ^ 2
      = 16 * (Real.log n) ^ 3 / (n : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hTnn, horizon_eq]; ring
  have hkey : (Real.log n * Real.sqrt (ChainDrift.horizon n)) ^ 2 ≤ 1 / 16 := by
    rw [hsqeq, div_le_iff₀ (by positivity)]; linarith
  have hx0 : 0 ≤ Real.log n * Real.sqrt (ChainDrift.horizon n) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  nlinarith [hkey, hx0]

/-- `12 ≤ log n` at the threshold (`e¹² = 162 755 ≤ 2 073 600`). -/
theorem twelve_le_log {n : ℕ} (hn : 2073600 ≤ n) : (12 : ℝ) ≤ Real.log n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  rw [Real.le_log_iff_exp_le hn0]
  have h12 : Real.exp 12 = Real.exp 1 ^ (12 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  calc Real.exp 12 = Real.exp 1 ^ (12 : ℕ) := h12
    _ ≤ (2.7182818286 : ℝ) ^ (12 : ℕ) := pow_le_pow_left₀ (Real.exp_pos 1).le he 12
    _ ≤ 2073600 := by norm_num
    _ ≤ (n : ℝ) := hnR

/-- `pieces_four`'s constant: `Lemma43Uniform.Kc + 1`. -/
noncomputable def KcR : ℝ := Kc + 1

/-- Lemma 4.3's per-`t` constant at the reach window. -/
noncomputable def C1cR (a₀ α : ℝ) (n : ℕ) : ℝ :=
  rhoC a₀ α n ^ n / (2 * (n : ℝ)) + Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * KcR

theorem KcR_nonneg : 0 ≤ KcR := by unfold KcR Kc; positivity

theorem C1cR_nonneg {a₀ α : ℝ} {n : ℕ} (hα : 0 < α) : 0 ≤ C1cR a₀ α n := by
  have hr : 0 ≤ rhoC a₀ α n := rhoC_nonneg hα
  refine add_nonneg (div_nonneg (pow_nonneg hr _) (by positivity)) ?_
  exact mul_nonneg (by positivity) KcR_nonneg

theorem C1cR_pos {a₀ α : ℝ} {n : ℕ} (hn : 0 < n) (hα : 0 < α) (ha₀ : 0 < a₀) :
    0 < C1cR a₀ α n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < rhoC a₀ α n := by
    unfold rhoC
    have : (0 : ℝ) < (Real.sqrt a₀)⁻¹ / α := by positivity
    positivity
  have h1 : 0 < rhoC a₀ α n ^ n / (2 * (n : ℝ)) := by positivity
  have h2 : 0 ≤ Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * KcR :=
    mul_nonneg (by positivity) KcR_nonneg
  unfold C1cR; linarith

/-- `((n+2)/2)·t ≤ 1/100` for `t ≤ T` — the far band's `a ≥ 0.49`. -/
theorem ct_le {n : ℕ} (hn : 2073600 ≤ n) {t : ℝ} (htT : t ≤ ChainDrift.horizon n) :
    ((n : ℝ) + 2) / 2 * t ≤ 1 / 100 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hlm : 9216 * Real.log n ≤ (n : ℝ) := WindowR.log_mul_le hn
  have h2 : ((n : ℝ) + 2) / 2 * t ≤ ((n : ℝ) + 2) / 2 * ChainDrift.horizon n :=
    mul_le_mul_of_nonneg_left htT (by positivity)
  refine le_trans h2 ?_
  rw [horizon_eq,
    show ((n : ℝ) + 2) / 2 * (16 * Real.log n / (n : ℝ) ^ 2)
      = 8 * ((n : ℝ) + 2) * Real.log n / (n : ℝ) ^ 2 by ring,
    div_le_div_iff₀ (by positivity) (by norm_num)]
  have hLn : Real.log n ≤ Real.log n * (n : ℝ) := by nlinarith [hL, hn0]
  have hmul : 9216 * Real.log n * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hlm hn0.le
  nlinarith [hmul, hLn, hL, hn0]

/-- `((n+2)/2)·√t ≤ 3·√(log n)` for `t ≤ T`. -/
theorem cs_le {n : ℕ} (hn : 2073600 ≤ n) {t : ℝ} (htT : t ≤ ChainDrift.horizon n) :
    ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ 3 * Real.sqrt (Real.log n) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hslpos : (0 : ℝ) < Real.sqrt (Real.log n) := Real.sqrt_pos.2 (by linarith)
  have hsT : Real.sqrt (ChainDrift.horizon n) = 4 * Real.sqrt (Real.log n) / (n : ℝ) :=
    sqrtT_eq (by omega) (horizon_eq n)
  have h1 : Real.sqrt t ≤ Real.sqrt (ChainDrift.horizon n) := Real.sqrt_le_sqrt htT
  have h2 : ((n : ℝ) + 2) / 2 * Real.sqrt t
      ≤ ((n : ℝ) + 2) / 2 * Real.sqrt (ChainDrift.horizon n) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine le_trans h2 ?_
  rw [hsT, show ((n : ℝ) + 2) / 2 * (4 * Real.sqrt (Real.log n) / (n : ℝ))
    = 2 * ((n : ℝ) + 2) * Real.sqrt (Real.log n) / (n : ℝ) by ring,
    div_le_iff₀ hn0]
  nlinarith [hslpos, hn0, hnR]

/-- **The far band's two numeric side conditions**, as a standalone lemma: `pieces_four`'s `hlam`
and `hfar` at the split point `Ymid ≥ 2·log n`. -/
theorem far_numerics {t Ymid : ℝ} {n : ℕ} (hn : 2073600 ≤ n)
    (hstpos : 0 < Real.sqrt t) (hst2 : Real.sqrt t ^ 2 = t)
    (hYmid0 : 0 < Ymid) (hYmidL : 2 * Real.log n ≤ Ymid)
    (hpYmid : (n : ℝ) * Real.sqrt t / 2 ≤ Ymid)
    (hct : ((n : ℝ) + 2) / 2 * t ≤ 1 / 100)
    (hcs : ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ 3 * Real.sqrt (Real.log n)) :
    (0 < 2 * (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid
        - ((n : ℝ) + 2) / 2 * Real.sqrt t)
      ∧ (n : ℝ) * Real.sqrt t / 2
        * (Real.exp (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid
            - (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid ^ 2)
          / ((2 * (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid
              - ((n : ℝ) + 2) / 2 * Real.sqrt t) * (Real.sqrt (2 * π) * Ymid))) ≤ 1 := by
  have hL12 : (12 : ℝ) ≤ Real.log n := twelve_le_log hn
  have hsl2 : Real.sqrt (Real.log n) ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  have hslpos : (0 : ℝ) < Real.sqrt (Real.log n) := Real.sqrt_pos.2 (by linarith)
  have hsl346 : (3.46 : ℝ) ≤ Real.sqrt (Real.log n) := by
    rw [show (3.46 : ℝ) = Real.sqrt (3.46 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  set aq : ℝ := 1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2 with haqdef
  have haq : (49 : ℝ) / 100 ≤ aq := by rw [haqdef, hst2]; linarith
  have h3sl : 3 * Real.sqrt (Real.log n) ≤ 98 / 100 * Real.log n := by
    nlinarith [hsl2, hsl346, hslpos]
  have hcs098 : ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ 98 / 100 * Real.log n := le_trans hcs h3sl
  have hcsL : ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ Real.log n := by linarith
  have haqY : 98 / 100 * Real.log n ≤ aq * Ymid := by
    have h1 : (49 : ℝ) / 100 * (2 * Real.log n) ≤ aq * Ymid :=
      mul_le_mul haq hYmidL (by linarith) (by linarith)
    linarith
  have hlam : (11 : ℝ) ≤ 2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t := by
    linarith [haqY, hcsL, hL12]
  have hkey : ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ aq * Ymid := le_trans hcs098 haqY
  have hC0 : ((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid - aq * Ymid ^ 2 ≤ 0 := by
    have h := mul_le_mul_of_nonneg_right hkey hYmid0.le
    nlinarith [h]
  have hpi2 : (2 : ℝ) ≤ Real.sqrt (2 * π) := by
    have h4 : (4 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    have h5 := Real.sqrt_le_sqrt h4
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h5
  refine ⟨by linarith, ?_⟩
  have hexp1 : Real.exp (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid - aq * Ymid ^ 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_le_exp.2 hC0
  have hprod11 : (11 : ℝ) * 2
      ≤ (2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t) * Real.sqrt (2 * π) :=
    mul_le_mul hlam hpi2 (by norm_num) (by linarith)
  have hden : (22 : ℝ) * Ymid
      ≤ (2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t) * (Real.sqrt (2 * π) * Ymid) := by
    calc (22 : ℝ) * Ymid = (11 * 2) * Ymid := by ring
      _ ≤ ((2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t) * Real.sqrt (2 * π)) * Ymid :=
          mul_le_mul_of_nonneg_right hprod11 hYmid0.le
      _ = (2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t) * (Real.sqrt (2 * π) * Ymid) := by
          ring
  have hnum : (0 : ℝ) < (2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t)
      * (Real.sqrt (2 * π) * Ymid) := by linarith [hden, hYmid0]
  rw [mul_div_assoc', div_le_one hnum]
  have hp0 : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 2 := by positivity
  have hprod : (n : ℝ) * Real.sqrt t / 2
      * Real.exp (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid - aq * Ymid ^ 2) ≤ Ymid := by
    nlinarith [hexp1, hpYmid, hp0, Real.exp_pos (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid
      - aq * Ymid ^ 2)]
  linarith [hprod, hden, hYmid0]

/-- Lemma 4.3's per-`t` constant at the reach window, with the small-`t` branch's `e²`. -/
noncomputable def C1R (α : ℝ) (n : ℕ) : ℝ := Real.exp 2 * C1cR (a0C n) α n

theorem C1R_pos {α : ℝ} {n : ℕ} (hn : 2 ≤ n) (hα : 0 < α) : 0 < C1R α n :=
  mul_pos (Real.exp_pos 2)
    (C1cR_pos (by omega) hα (lt_of_lt_of_le zero_lt_one (a0C_ge_one hn)))

theorem eight_sub_pos {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < 8 - 8 / (n : ℝ) ^ 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
  have h2 : 8 / (n : ℝ) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ h1]; nlinarith
  linarith

theorem C4_pos {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    0 < 4 * C1R α n * (8 - 8 / (n : ℝ) ^ 2) :=
  mul_pos (by linarith [C1R_pos (α := α) (n := n) (by omega) hα]) (eight_sub_pos (by omega))

open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA

end D5.S3.Arith.Lattices.Klartag.Lemma43R
