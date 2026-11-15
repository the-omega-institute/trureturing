/- GID: D5/S3/Quantum/Approximate/SolovayKitaevRate
   generality: G
   mirror-B: D5/B/S3/Quantum/Approximate/SolovayKitaevRate
   mirror-E: none(waiver:kernel-checked-content)
   anchors: []
   utility: none
   digest: Scalar error decay and logarithmic level elimination for the fivefold word recursion. -/

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore.
Adapted from zblore/csd-lean4@9b2d2c17e926ae13795119c5f2f62e85ea240c2d:
https://github.com/zblore/csd-lean4/blob/9b2d2c17e926ae13795119c5f2f62e85ea240c2d/CsdLean4/Mathlib/QuantumInfo/SolovayKitaevCount.lean
(original declarations QuantumInfo.SU2.skExponent, log_three_halves_pos, skExponent_pos,
skLevel, one_le_log_ratio, log_ratio_pos, log_ratio_le_three_halves_pow,
skLevel_rpow_le, five_pow_skLevel_le, skErr, skErr_zero, skErr_succ,
rpow_three_halves, skErr_nonneg, skErr_le_base, step_arith, step_bound), and
https://github.com/zblore/csd-lean4/blob/9b2d2c17e926ae13795119c5f2f62e85ea240c2d/CsdLean4/Mathlib/QuantumInfo/SolovayKitaevStep.lean#L190
(original declaration CSD.SolovayKitaev.skError_le_rpow).
Full license: docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.
All scalar and logarithmic estimates in this module are licensed reuse.
Retirement condition: for each ported declaration mapped above, use the mathlib
revision resolved by this repository's unchanged lake-manifest.json. Retire that
ported declaration when an importable replacement in that revision accepts its
full current telescope and direct application typechecks at every current consumer
site, with only the standard axiom closure. Replace those uses by the mathlib
application and delete the port; upstream acceptance alone does not trigger this.

-/

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic

@[expose] public section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Approximate.SolovayKitaevRate
noncomputable section
noncomputable def skExponent : ℝ := Real.log 5 / Real.log (3 / 2)

theorem log_three_halves_pos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)

theorem skExponent_pos : 0 < skExponent :=
  div_pos (Real.log_pos (by norm_num)) log_three_halves_pos




noncomputable def skLevel (b ε : ℝ) : ℕ := ⌈Real.log (Real.log ε / Real.log b) / Real.log (3 / 2)⌉₊

section Level

variable {b ε : ℝ} (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε) (hεb : ε ≤ b)

include hb hb1 hε hεb

theorem one_le_log_ratio : 1 ≤ Real.log ε / Real.log b := by
  have hlb : Real.log b < 0 := Real.log_neg hb hb1
  have hmono : Real.log ε ≤ Real.log b := Real.log_le_log hε hεb
  rw [le_div_iff_of_neg hlb]
  linarith

theorem log_ratio_pos : 0 < Real.log ε / Real.log b :=
  lt_of_lt_of_le zero_lt_one (one_le_log_ratio hb hb1 hε hεb)


theorem log_ratio_le_three_halves_pow :
    Real.log ε / Real.log b ≤ (3 / 2 : ℝ) ^ skLevel b ε := by
  have hR : 0 < Real.log ε / Real.log b := log_ratio_pos hb hb1 hε hεb
  have hceil : Real.log (Real.log ε / Real.log b) / Real.log (3 / 2 : ℝ)
      ≤ (skLevel b ε : ℝ) := Nat.le_ceil _
  have hmul : Real.log (Real.log ε / Real.log b)
      ≤ (skLevel b ε : ℝ) * Real.log (3 / 2 : ℝ) := by
    rw [div_le_iff₀ log_three_halves_pos] at hceil
    exact hceil
  have hexp : Real.log ε / Real.log b
      ≤ Real.exp ((skLevel b ε : ℝ) * Real.log (3 / 2 : ℝ)) := by
    rw [← Real.exp_log hR]
    exact Real.exp_le_exp.2 hmul
  rwa [show Real.exp ((skLevel b ε : ℝ) * Real.log (3 / 2 : ℝ))
      = (3 / 2 : ℝ) ^ skLevel b ε from by
        rw [← Real.log_pow, Real.exp_log (by positivity)]] at hexp


theorem skLevel_rpow_le : b ^ ((3 / 2 : ℝ) ^ skLevel b ε) ≤ ε := by
  have hR : 0 < Real.log ε / Real.log b := log_ratio_pos hb hb1 hε hεb
  have hbR : b ^ (Real.log ε / Real.log b) = ε := by
    rw [Real.rpow_def_of_pos hb, mul_div_cancel₀ _ (ne_of_lt (Real.log_neg hb hb1)),
      Real.exp_log hε]
  calc b ^ ((3 / 2 : ℝ) ^ skLevel b ε)
      ≤ b ^ (Real.log ε / Real.log b) :=
        Real.rpow_le_rpow_of_exponent_ge hb hb1.le (log_ratio_le_three_halves_pow hb hb1 hε hεb)
    _ = ε := hbR


theorem five_pow_skLevel_le :
    (5 : ℝ) ^ skLevel b ε ≤ 5 * (Real.log ε / Real.log b) ^ skExponent := by
  have hR : 0 < Real.log ε / Real.log b := log_ratio_pos hb hb1 hε hεb
  have hR1 : 1 ≤ Real.log ε / Real.log b := one_le_log_ratio hb hb1 hε hεb
  set t : ℝ := Real.log (Real.log ε / Real.log b) / Real.log (3 / 2 : ℝ) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact div_nonneg (Real.log_nonneg hR1) log_three_halves_pos.le
  have hlt : (skLevel b ε : ℝ) < t + 1 := by
    rw [skLevel, ← ht]
    exact Nat.ceil_lt_add_one ht0
  have hstep : (5 : ℝ) ^ skLevel b ε ≤ (5 : ℝ) ^ (t + 1) := by
    rw [← Real.rpow_natCast (5 : ℝ) (skLevel b ε)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
  have hsplit : (5 : ℝ) ^ (t + 1) = 5 * (5 : ℝ) ^ t := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
  have hpow : (5 : ℝ) ^ t = (Real.log ε / Real.log b) ^ skExponent := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5),
      Real.rpow_def_of_pos hR, skExponent, ht]
    congr 1
    field_simp
  calc (5 : ℝ) ^ skLevel b ε ≤ (5 : ℝ) ^ (t + 1) := hstep
    _ = 5 * (5 : ℝ) ^ t := hsplit
    _ = 5 * (Real.log ε / Real.log b) ^ skExponent := by rw [hpow]

end Level

noncomputable def skErr (e : ℝ) : ℕ → ℝ
  | 0 => e
  | n + 1 => 33 * skErr e n ^ ((3 : ℝ) / 2)

@[simp] theorem skErr_zero (e : ℝ) : skErr e 0 = e := rfl

theorem skErr_succ (e : ℝ) (n : ℕ) : skErr e (n + 1) = 33 * skErr e n ^ ((3 : ℝ) / 2) := rfl

theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = Real.sqrt x ^ 3 := by
  obtain ⟨t, ht0, htsq, hteq⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ^ 2 = x ∧ Real.sqrt x = t :=
    ⟨Real.sqrt x, Real.sqrt_nonneg x, Real.sq_sqrt hx, rfl⟩
  rw [hteq, ← htsq, ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0,
    show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

theorem skErr_nonneg {e : ℝ} (he : 0 ≤ e) (n : ℕ) : 0 ≤ skErr e n := by
  induction n with
  | zero => simpa using he
  | succ n ih =>
      rw [skErr_succ]
      positivity


theorem skErr_le_base {e : ℝ} (he : 0 ≤ e) (hs : Real.sqrt e ≤ 1 / 33) (n : ℕ) :
    skErr e n ≤ e := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h0 : 0 ≤ skErr e n := skErr_nonneg he n
      have hsle : Real.sqrt (skErr e n) ≤ 1 / 33 := le_trans (Real.sqrt_le_sqrt ih) hs
      have hsq : Real.sqrt (skErr e n) ^ 2 = skErr e n := Real.sq_sqrt h0
      have hcube : Real.sqrt (skErr e n) ^ 3 = skErr e n * Real.sqrt (skErr e n) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hsq]
      rw [skErr_succ, rpow_three_halves h0, hcube]
      calc 33 * (skErr e n * Real.sqrt (skErr e n)) ≤ 33 * (skErr e n * (1 / 33)) := by gcongr
        _ = skErr e n := by ring
        _ ≤ e := ih


theorem step_arith {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    4 * (Real.sqrt 2 * t + t ^ 2) * t ^ 2 * (1 + (Real.sqrt 2 * t + t ^ 2)) ≤ 33 * t ^ 3 := by
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2' : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hqt : Real.sqrt 2 * t ≤ 3 / 4 := by nlinarith
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  have hb : 4 * (Real.sqrt 2 + t) * (1 + (Real.sqrt 2 * t + t ^ 2)) ≤ 33 := by
    have hA : Real.sqrt 2 + t ≤ 2 := by linarith
    have hB : 1 + (Real.sqrt 2 * t + t ^ 2) ≤ 2 := by linarith
    have hA0 : (0 : ℝ) ≤ Real.sqrt 2 + t := by linarith
    have hB0 : (0 : ℝ) ≤ 1 + (Real.sqrt 2 * t + t ^ 2) := by positivity
    nlinarith [hA, hB, hA0, hB0]
  have ht3 : (0 : ℝ) ≤ t ^ 3 := by positivity
  calc 4 * (Real.sqrt 2 * t + t ^ 2) * t ^ 2 * (1 + (Real.sqrt 2 * t + t ^ 2))
      = t ^ 3 * (4 * (Real.sqrt 2 + t) * (1 + (Real.sqrt 2 * t + t ^ 2))) := by ring
    _ ≤ t ^ 3 * 33 := by gcongr
    _ = 33 * t ^ 3 := by ring


theorem step_bound {ε : ℝ} (hε : 0 ≤ ε) (hs : Real.sqrt ε ≤ 1 / 2) :
    4 * (Real.sqrt 2 * Real.sqrt ε + ε) * ε * (1 + (Real.sqrt 2 * Real.sqrt ε + ε))
      ≤ 33 * ε ^ ((3 : ℝ) / 2) := by
  obtain ⟨t, ht0, htsq, hteq⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ^ 2 = ε ∧ Real.sqrt ε = t :=
    ⟨Real.sqrt ε, Real.sqrt_nonneg ε, Real.sq_sqrt hε, rfl⟩
  rw [rpow_three_halves hε, hteq, ← htsq]
  rw [hteq] at hs
  exact step_arith ht0 hs



theorem skError_le_rpow {C : ℝ} (hC : 0 < C) {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hrec : ∀ n, ε (n + 1) ≤ C * ε n ^ ((3 : ℝ) / 2)) (n : ℕ) :
    C ^ 2 * ε n ≤ (C ^ 2 * ε 0) ^ ((3 : ℝ) / 2) ^ n := by
  have hC2 : ((C ^ 2 : ℝ)) ^ ((3 : ℝ) / 2) = C ^ 3 := by
    rw [show (C ^ 2 : ℝ) = C ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast C 2).symm,
      ← Real.rpow_mul hC.le,
      show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  have hzero : (0 : ℝ) ≤ C ^ 2 * ε 0 := mul_nonneg (sq_nonneg C) (hε 0)
  induction n with
  | zero => simp
  | succ n ih =>
      have hbase : (0 : ℝ) ≤ C ^ 2 * ε n := mul_nonneg (sq_nonneg C) (hε n)
      set X := ε n ^ ((3 : ℝ) / 2) with hX
      have h1 : C ^ 2 * ε (n + 1) ≤ C ^ 3 * X := by
        calc C ^ 2 * ε (n + 1) ≤ C ^ 2 * (C * X) :=
              mul_le_mul_of_nonneg_left (hrec n) (sq_nonneg C)
          _ = C ^ 3 * X := by ring
      have h2 : (C ^ 2 * ε n) ^ ((3 : ℝ) / 2) = C ^ 3 * X := by
        rw [Real.mul_rpow (sq_nonneg C) (hε n), hC2, hX]
      calc C ^ 2 * ε (n + 1) ≤ C ^ 3 * X := h1
        _ = (C ^ 2 * ε n) ^ ((3 : ℝ) / 2) := h2.symm
        _ ≤ ((C ^ 2 * ε 0) ^ ((3 : ℝ) / 2) ^ n) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow hbase ih (by norm_num)
        _ = (C ^ 2 * ε 0) ^ ((3 : ℝ) / 2) ^ (n + 1) := by
            rw [← Real.rpow_mul hzero]
            congr 1


end
end D5.S3.Quantum.Approximate.SolovayKitaevRate
