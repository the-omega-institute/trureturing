/- GID: D5/S3/Arith/Additive/Waring/WaringIndStep2Estimates
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringIndStep2.lean#L1-L493
   Modified for this repository. Local imports use their D5 module paths.
   This file contains one segment of a split upstream module.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import D5.S3.Arith.Additive.Waring.WaringIndStep
import D5.S3.Arith.Additive.Waring.WaringLemma7
import D5.S3.Arith.Additive.Waring.WaringHolder
import D5.S3.Arith.Additive.Waring.WaringQuadSum
import D5.S3.Arith.Additive.Waring.WaringCoeffBound
import D5.S3.Arith.Additive.Waring.WaringQuadratic
import D5.S3.Arith.Additive.Waring.WaringLemma8Form

open Finset intervalIntegral

namespace Waring

/-- **加强版归纳命题**（`M ≤ N`）：求和长度 `M` 可以小于系数尺度的 `N`，
但界仍然用 `N`。 -/
def MeanValueBoundS (d : ℕ) : Prop :=
  ∃ R : ℕ → ℝ, (∀ c, 0 < R c) ∧
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
      (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
      (∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
        ≤ R c * (N : ℝ) ^ (8 ^ (d - 1) - d)

/-- `B = Σ_{h≠0, |h|≤M} ‖b_h‖^m`，其中 `m = 8^{d−2}`。 -/
noncomputable def SigTerm (a : ℕ → ℤ) (d M : ℕ) (α : ℝ) : ℝ :=
  ∑ h ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
    ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2))

/-- `(A+B)^4 ≤ 8(A^4 + B^4)`（`A, B ≥ 0`）。 -/
theorem pow_four_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A + B) ^ 4 ≤ 8 * (A ^ 4 + B ^ 4) := by
  have h := add_pow_le_two_pow A B hA hB 4 (by norm_num)
  norm_num at h
  linarith

/-- 纯代数整理（第 2–4 步）：
`(2^{m−1}·((M+1)^m + (2M)^{m−1}·T))^4 ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·T^4)`。 -/
theorem pointwise_alg (M m : ℕ) (Tv : ℝ) (hTv : 0 ≤ Tv) :
    (2 ^ (m - 1) * ((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv)) ^ 4
      ≤ 2 ^ (4 * (m - 1)) * 8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4) := by
  have h1 : (2 ^ (m - 1) * ((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv)) ^ 4
      = 2 ^ (4 * (m - 1))
        * (((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv) ^ 4) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (m - 1) 4]
  rw [h1]
  have hA0 : (0 : ℝ) ≤ (M + 1 : ℝ) ^ m := by positivity
  have hB0 : (0 : ℝ) ≤ (2 * (M : ℝ)) ^ (m - 1) * Tv := by positivity
  have h2 := pow_four_bound _ _ hA0 hB0
  have h3 : (((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv) ^ 4)
      ≤ 8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4) := by
    refine le_trans h2 (le_of_eq ?_)
    congr 2
    · rw [← pow_mul, Nat.mul_comm m 4]
    · rw [mul_pow, ← pow_mul, Nat.mul_comm (m - 1) 4]
  calc 2 ^ (4 * (m - 1))
        * (((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv) ^ 4)
      ≤ 2 ^ (4 * (m - 1)) * (8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 ^ (4 * (m - 1)) * 8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4) := by ring

/-- **第 1–4 步（点态）**：`‖S‖^{8^{d−1}} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·B^4)`。 -/
theorem pointwise_bound {d : ℕ} (hd : 3 ≤ d) (a : ℕ → ℤ) {M : ℕ} (hM1 : 1 ≤ M) (α : ℝ) :
    ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1))
      ≤ 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
          ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * (SigTerm a d M α) ^ 4) := by
  have hm1 : 1 ≤ 8 ^ (d - 2) := by
    have h : (0 : ℕ) < 8 ^ (d - 2) := pow_pos (by norm_num) _
    omega
  have hpt := normSq_pow_le (fun n => polyEval a d n) M α (8 ^ (d - 2)) hm1 hM1
  have hTv : 0 ≤ SigTerm a d M α := by
    apply Finset.sum_nonneg
    intro h _
    positivity
  have hpow : 8 ^ (d - 1) = (2 * 8 ^ (d - 2)) * 4 := by
    have h1 : d - 1 = (d - 2) + 1 := by omega
    rw [h1, pow_succ]
    ring
  rw [hpow, pow_mul]
  exact le_trans (pow_le_pow_left₀ (by positivity) hpt 4)
    (pointwise_alg M (8 ^ (d - 2)) (SigTerm a d M α) hTv)

/-- **第 5 步（积分）**：
`∫‖S‖^{8m} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·∫B^4)`。 -/
theorem integral_bound {d : ℕ} (hd : 3 ≤ d) (a : ℕ → ℤ) {M : ℕ} (hM1 : 1 ≤ M) :
    (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
      ≤ 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
          ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * ∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4) := by
  set g : ℝ → ℝ := fun α => 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
      ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
        + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * (SigTerm a d M α) ^ 4) with hg
  have hcont1 : Continuous fun α : ℝ =>
      ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)) := by
    unfold expSum e
    fun_prop
  have hcont2 : Continuous fun α : ℝ => (SigTerm a d M α) ^ 4 := by
    unfold SigTerm T e
    fun_prop
  have hcontg : Continuous g := by
    rw [hg]
    simp only [mul_assoc]
    unfold SigTerm T e
    fun_prop
  have hmono : (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
      ≤ ∫ α in (0 : ℝ)..1, g α := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      (hcont1.intervalIntegrable 0 1) (hcontg.intervalIntegrable 0 1) ?_
    intro α _
    rw [hg]
    exact pointwise_bound hd a hM1 α
  have hsplit : (∫ x in (0 : ℝ)..1, ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
        + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * SigTerm a d M x ^ 4))
      = (M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
        + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
          * (∫ x in (0 : ℝ)..1, SigTerm a d M x ^ 4) := by
    have step1 : (∫ x in (0 : ℝ)..1, ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
          + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * SigTerm a d M x ^ 4))
        = (∫ x in (0 : ℝ)..1, ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))))
          + (∫ x in (0 : ℝ)..1, ((2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * SigTerm a d M x ^ 4)) :=
      intervalIntegral.integral_add intervalIntegrable_const
        ((continuous_const.mul hcont2).intervalIntegrable 0 1)
    rw [step1, intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    ring
  have hgi : (∫ α in (0 : ℝ)..1, g α)
      = 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
          ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * ∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4) := by
    rw [hg]
    simp only [mul_assoc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsplit]
  exact le_trans hmono (le_of_eq hgi)

/-- 展开 `∫ (Σ_h ‖b_h‖^m)^4`（`m = 8^{d−2} = 2s`，`s = 4·8^{d−3}`）。 -/
theorem four_sum_eq {d : ℕ} (hd : 3 ≤ d) (a : ℕ → ℤ) (M : ℕ) :
    (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
      = ∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ Q1 ∈ QSet (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)),
        ∑ Q2 ∈ QSet (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)),
        ∑ Q3 ∈ QSet (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)),
        ∑ Q4 ∈ QSet (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)),
          (if Q1 + Q2 + Q3 + Q4 = 0 then
            (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1
              * BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2
              * BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3
              * BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ)
          else 0) := by
  have hs1 : 1 ≤ 4 * 8 ^ (d - 3) := by
    have h : 0 < 4 * 8 ^ (d - 3) := by positivity
    omega
  have h2s : 2 * (4 * 8 ^ (d - 3)) = 8 ^ (d - 2) := by
    have h1 : d - 2 = (d - 3) + 1 := by omega
    rw [h1, pow_succ]
    ring
  have h := integral_sum_pow_four (fun n => polyEval a d n) M (4 * 8 ^ (d - 3)) hs1
  rw [h2s] at h
  exact h

/-- `P(k)` 的显式形式（`R` 固定）。 -/
def MVSBound (k : ℕ) (R : ℕ → ℝ) : Prop :=
  ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a k ≠ 0 →
    (∀ j, j ≤ k → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (k - j)) →
    (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a k n) M α‖ ^ (8 ^ (k - 1)))
      ≤ R c * (N : ℝ) ^ (8 ^ (k - 1) - k)

set_option maxHeartbeats 4000000 in
/-- **第 7 步**：`P(d−1) ⇒ ∫₀¹‖b_h‖^{8^{d−2}} ≤ max(R(C),1)·N^{8^{d−2}−(d−1)}`。 -/
theorem integral_norm_T_pow_le_R {d : ℕ} (hd : 3 ≤ d) {R₀ : ℕ → ℝ}
    (hMV : MVSBound (d - 1) R₀) :
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
    (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
    ∀ h ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      (∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2)))
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
  intro c N M hN hM1 hMN a had ha
  have hd1 : 1 ≤ d := by omega
  have hexp : (d - 1) - 1 = d - 2 := by omega
  intro h hS
  rw [Finset.mem_erase, Finset.mem_Icc] at hS
  obtain ⟨hne, hle1, hle2⟩ := hS
  have main : ∀ (g : ℤ), 0 < g → g.toNat ≤ M →
      (∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α g‖ ^ (8 ^ (d - 2)))
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
    intro g hg hgM
    rw [integral_norm_T_pow_eq (a := a) (d := d) (N := M) (h := g) hg hgM (8 ^ (d - 2))]
    -- 次数从 `d` 降到 `d−1`
    have hstep : (∫ β in (0 : ℝ)..1,
        ‖expSum (fun n => polyEval (diffCoeff a d g) d n) (M - g.toNat) β‖ ^ (8 ^ (d - 2)))
        = ∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) (M - g.toNat) β‖ ^
            (8 ^ (d - 2)) := by
      apply intervalIntegral.integral_congr
      intro β _
      have hfun : (fun n => polyEval (diffCoeff a d g) d n)
          = (fun n => polyEval (diffCoeff a d g) (d - 1) n) := by
        funext n
        exact polyEval_eq_of_last_zero (diffCoeff a d g) hd1 (diffCoeff_eq_zero_of_le le_rfl) n
      rw [hfun]
    rw [hstep]
    rcases Nat.eq_zero_or_pos (M - g.toNat) with h0 | h1pos
    · -- 长度为零：指数和只有一项
      rw [h0]
      have hpt : ∀ β : ℝ,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2)) ≤ 1 := by
        intro β
        have hnorm : ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ = 1 := by
          unfold expSum
          rw [Finset.range_one, Finset.sum_singleton, norm_e]
        rw [hnorm, one_pow]
      have hcont : Continuous fun β : ℝ =>
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2)) := by
        unfold expSum e
        fun_prop
      have hbound : (∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2))) ≤ 1 := by
        calc (∫ β in (0 : ℝ)..1,
              ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2)))
            ≤ ∫ β in (0 : ℝ)..1, (1 : ℝ) :=
              intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable 0 1)
                intervalIntegrable_const (fun x _ => hpt x)
          _ = 1 := by simp
      refine le_trans hbound ?_
      have h1 : (1 : ℝ) ≤ max (R₀ (coeffConst c d)) 1 := le_max_right _ _
      have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := one_le_pow₀ (by exact_mod_cast hN)
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) :=
            mul_le_mul h1 h2 (by norm_num) (by linarith)
    · -- 一般情形：用 `P(d−1)`
      have htoNatZ : ((g.toNat : ℕ) : ℤ) = g := Int.toNat_of_nonneg (le_of_lt hg)
      have habs : |g| ≤ (N : ℤ) := by
        have h2 : ((g.toNat : ℕ) : ℤ) ≤ (N : ℤ) := by
          have h3 : g.toNat ≤ N := le_trans hgM hMN
          exact_mod_cast h3
        rw [htoNatZ] at h2
        rw [abs_of_pos hg]
        exact h2
      have hcoeff : ∀ j, j ≤ d - 1 →
          |diffCoeff a d g j| ≤ (coeffConst c d : ℤ) * (N : ℤ) ^ ((d - 1) - j) := by
        intro j hj
        exact diffCoeff_bound' (a := a) (d := d) (h := g) (c := c) (N := N) ha habs j (by omega)
      have hblast : diffCoeff a d g (d - 1) ≠ 0 := by
        rw [diffCoeff_last hd1 g]
        exact mul_ne_zero had (by exact_mod_cast (show d ≠ 0 by omega))
      have hres := hMV (coeffConst c d) N (M - g.toNat) hN h1pos (by omega)
        (diffCoeff a d g) hblast hcoeff
      rw [hexp] at hres
      refine le_trans hres ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `h < 0`：换成 `−h > 0`
    have htoNat : (-h).toNat ≤ M := by
      have h1 : (((-h).toNat : ℕ) : ℤ) = -h := Int.toNat_of_nonneg (by omega)
      have h2 : (((-h).toNat : ℕ) : ℤ) ≤ (M : ℤ) := by rw [h1]; linarith
      exact_mod_cast h2
    have heq : (∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2)))
        = ∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α (-h)‖ ^ (8 ^ (d - 2)) := by
      apply intervalIntegral.integral_congr
      intro α _
      have hh := norm_T_neg (f := fun n => polyEval a d n) (N := M) (h := -h) (by omega) htoNat α
      show ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2))
        = ‖T (fun n => polyEval a d n) M α (-h)‖ ^ (8 ^ (d - 2))
      rw [show ‖T (fun n => polyEval a d n) M α h‖ = ‖T (fun n => polyEval a d n) M α (-h)‖ by
        simpa using hh]
    rw [heq]
    exact main (-h) (by omega) htoNat
  · -- `h > 0`
    have htoNatM : h.toNat ≤ M := by
      have h1 : ((h.toNat : ℕ) : ℤ) = h := Int.toNat_of_nonneg (by omega)
      have h2 : ((h.toNat : ℕ) : ℤ) ≤ (M : ℤ) := by rw [h1]; exact hle2
      exact_mod_cast h2
    exact main h hpos htoNatM

/-- `2·(4·8^{d−3}) = 8^{d−2}`（`d ≥ 3`）。 -/
theorem two_mul_s {d : ℕ} (hd : 3 ≤ d) : 2 * (4 * 8 ^ (d - 3)) = 8 ^ (d - 2) := by
  have h1 : d - 2 = (d - 3) + 1 := by omega
  rw [h1, pow_succ]
  ring

/-- `1 ≤ 4·8^{d−3}`。 -/
theorem one_le_s (d : ℕ) : 1 ≤ 4 * 8 ^ (d - 3) := by
  have h : 0 < 4 * 8 ^ (d - 3) := by positivity
  omega

/-- **每个 `BCount` 的上界**（第 6 步前半 + 第 7 步）。 -/
theorem BCount_le_Rtot {d : ℕ} (hd : 3 ≤ d) {R₀ : ℕ → ℝ}
    (hMV : MVSBound (d - 1) R₀) :
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
    (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
    ∀ (h : ℤ), h ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0 → ∀ Q : ℤ,
      (BCount (fun n => polyEval a d n) M h (4 * 8 ^ (d - 3)) Q : ℝ)
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
  intro c N M hN hM1 hMN a had ha h hS Q
  have h1 := BCount_le_integral (fun n => polyEval a d n) M h (4 * 8 ^ (d - 3))
    (one_le_s d) Q
  rw [two_mul_s hd] at h1
  exact le_trans h1 (integral_norm_T_pow_le_R hd hMV c N M hN hM1 hMN a had ha h hS)

/-- **第 8 步**：四重和被 `Rtot^4` 乘「满足 `Q₁+…+Q₄ = 0` 的项数」控制。 -/
theorem four_sum_le_count {d : ℕ} (hd : 3 ≤ d) {R₀ : ℕ → ℝ}
    (hMV : MVSBound (d - 1) R₀) :
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
    (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
    (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
      ≤ (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1))) ^ 4
        * (∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ Q1 ∈ QSet (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)),
          ∑ Q2 ∈ QSet (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)),
          ∑ Q3 ∈ QSet (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)),
          ∑ Q4 ∈ QSet (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)),
            (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0)) := by
  intro c N M hN hM1 hMN a had ha
  rw [four_sum_eq hd a M]
  set Rt : ℝ := max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) with hRt
  have hRtpos : 0 < Rt := by
    rw [hRt]
    have h1 : (0 : ℝ) < max (R₀ (coeffConst c d)) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have h3 : (0 : ℝ) < (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
      have : (0:ℝ) < N := by exact_mod_cast hN
      positivity
    exact mul_pos h1 h3
  have hRt0 : 0 ≤ Rt := le_of_lt hRtpos
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum (fun h1 h1S => Finset.sum_le_sum (fun h2 h2S =>
    Finset.sum_le_sum (fun h3 h3S => Finset.sum_le_sum (fun h4 h4S =>
    Finset.sum_le_sum (fun Q1 Q1S => Finset.sum_le_sum (fun Q2 Q2S =>
    Finset.sum_le_sum (fun Q3 Q3S => Finset.sum_le_sum (fun Q4 Q4S => ?_))))))))
  have hB1 : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h1 h1S Q1
  have hB2 : (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h2 h2S Q2
  have hB3 : (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h3 h3S Q3
  have hB4 : (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h4 h4S Q4
  have hC1 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ) := by
    positivity
  have hC2 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ) := by
    positivity
  have hC3 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ) := by
    positivity
  have hC4 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ) := by
    positivity
  have hP : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
      * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ)
      * (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ)
      * (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ) ≤ Rt ^ 4 := by
    have h12 : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
        * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ) ≤ Rt * Rt :=
      mul_le_mul hB1 hB2 hC2 hRt0
    have h123 : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
        * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ)
        * (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ) ≤ Rt * Rt * Rt :=
      mul_le_mul h12 hB3 hC3 (by positivity)
    have h1234 := mul_le_mul h123 hB4 hC4 (by positivity)
    calc (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
          * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ)
          * (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ)
          * (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ)
        ≤ Rt * Rt * Rt * Rt := h1234
      _ = Rt ^ 4 := by ring
  by_cases hc : Q1 + Q2 + Q3 + Q4 = 0
  · rw [if_pos hc, if_pos hc, mul_one]
    exact hP
  · rw [if_neg hc, if_neg hc, mul_zero]

end Waring
