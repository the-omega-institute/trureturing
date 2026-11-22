/- GID: D5/S3/Arith/Additive/Waring/WaringTheorem1
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringTheorem1.lean#L1-L146
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

import D5.S3.Arith.Additive.Waring.WaringLemma6
import D5.S3.Arith.Additive.Waring.WaringLemma3
import D5.S3.Arith.Additive.Waring.WaringSymm

open Finset

namespace Waring

/-- **Theorem 1（`k = 2`，Jameson Lemma 8）**：`∫₀¹|θ_N|⁸ ≤ 44592·N⁶`（`N ≥ 1`）。 -/
theorem sqEqCount_le (N : ℕ) (hN : 1 ≤ N) : sqEqCount N ≤ 44592 * N ^ 6 := by
  classical
  have hNQ : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  set K : ℕ := 4 * N ^ 2 with hK
  have hKZ : (K : ℤ) = 4 * (N : ℤ) ^ 2 := by
    rw [hK]
    push_cast
    ring
  have hKQ : (K : ℚ) = 4 * (N : ℚ) ^ 2 := by
    rw [hK]
    push_cast
    ring
  -- 常数
  set A : ℚ := 4 * (N : ℚ) * ((N : ℚ) + 1) with hA
  set B : ℚ := 8 * (N : ℚ) * ((2 * N : ℕ) : ℚ) with hB
  have hAf : (0 : ℚ) ≤ A := by
    rw [hA]
    positivity
  have hBf : (0 : ℚ) ≤ B := by
    rw [hB]
    positivity
  have hAK : A ≤ 8 * (N : ℚ) ^ 2 := by
    rw [hA]
    nlinarith
  have hBK : B = 16 * (N : ℚ) ^ 2 := by
    rw [hB]
    push_cast
    ring
  -- 1) 归约到对称和
  have h1 : (sqEqCount N : ℚ) ≤ ∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ((Q N (2 * N) n : ℚ)) ^ 2 := by
    have h := sqEqCount_le_sum_Q_sq N
    rw [← hKZ] at h
    exact_mod_cast h
  -- 2) 对称拆分
  have h2 : (∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ((Q N (2 * N) n : ℚ)) ^ 2)
      = ((Q N (2 * N) 0 : ℚ)) ^ 2
        + 2 * ∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), ((Q N (2 * N) n : ℚ)) ^ 2 := by
    have hnat := sum_Icc_symm_eq (K : ℤ) (by positivity)
      (fun n => Q N (2 * N) n ^ 2) (fun n => by rw [Q_neg])
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) hnat
    push_cast at hcast
    exact hcast
  -- 3) 正半边的界
  have hs1 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs) ≤ 2 * (K : ℚ) := by
    rw [sum_int_Icc_eq_sum_nat_Icc K (fun m => sigmaMinusOne m)]
    exact sum_sigmaMinusOne_le K
  have hs2 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs ^ 2) ≤ 6 * (K : ℚ) := by
    rw [sum_int_Icc_eq_sum_nat_Icc K (fun m => sigmaMinusOne m ^ 2)]
    exact sum_sigmaMinusOne_sq_le K
  have h3 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), ((Q N (2 * N) n : ℚ)) ^ 2)
      ≤ 8448 * (N : ℚ) ^ 6 := by
    -- 逐项界
    have hbound : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), ((Q N (2 * N) n : ℚ)) ^ 2)
        ≤ ∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), (A + B * sigmaMinusOne n.natAbs) ^ 2 := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      rw [Finset.mem_Icc] at hn
      have hn0 : n ≠ 0 := by omega
      have hq := Q_le_sigma N (2 * N) hn0
      have hq' : (Q N (2 * N) n : ℚ) ≤ A + B * sigmaMinusOne n.natAbs := by
        rw [hA, hB]
        exact hq
      exact pow_le_pow_left₀ (by positivity) hq' 2
    refine le_trans hbound ?_
    -- 展开
    have hexp : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), (A + B * sigmaMinusOne n.natAbs) ^ 2)
        = (K : ℚ) * A ^ 2 + 2 * A * B * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs)
          + B ^ 2 * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs ^ 2) := by
      have hpt : ∀ n : ℤ, (A + B * sigmaMinusOne n.natAbs) ^ 2
          = A ^ 2 + 2 * A * B * sigmaMinusOne n.natAbs
            + B ^ 2 * sigmaMinusOne n.natAbs ^ 2 := fun n => by ring
      rw [Finset.sum_congr rfl (fun n _ => hpt n)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hcardK : ((Finset.Icc (1 : ℤ) (K : ℤ)).card : ℚ) = (K : ℚ) := by
        rw [Int.card_Icc]
        simp
      have e1 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), A ^ 2) = (K : ℚ) * A ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardK]
      have e2 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), 2 * A * B * sigmaMinusOne n.natAbs)
          = 2 * A * B * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs) := by
        rw [Finset.mul_sum]
      have e3 : (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), B ^ 2 * sigmaMinusOne n.natAbs ^ 2)
          = B ^ 2 * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs ^ 2) := by
        rw [Finset.mul_sum]
      rw [e1, e2, e3]
    rw [hexp]
    -- 代入界
    have hm1 : 2 * A * B * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs)
        ≤ 2 * A * B * (2 * (K : ℚ)) := by
      apply mul_le_mul_of_nonneg_left hs1
      positivity
    have hm2 : B ^ 2 * (∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), sigmaMinusOne n.natAbs ^ 2)
        ≤ B ^ 2 * (6 * (K : ℚ)) := by
      apply mul_le_mul_of_nonneg_left hs2
      positivity
    have htarget : (K : ℚ) * A ^ 2 + 2 * A * B * (2 * (K : ℚ)) + B ^ 2 * (6 * (K : ℚ))
        ≤ 8448 * (N : ℚ) ^ 6 := by
      have hA2 : A ^ 2 ≤ 64 * (N : ℚ) ^ 4 := by
        have h := pow_le_pow_left₀ hAf hAK 2
        calc A ^ 2 ≤ (8 * (N : ℚ) ^ 2) ^ 2 := h
          _ = 64 * (N : ℚ) ^ 4 := by ring
      rw [hBK, hKQ]
      nlinarith [hA2, hAK, hNQ, sq_nonneg (N : ℚ)]
    linarith
  -- 4) 零点的界
  have h4 : ((Q N (2 * N) 0 : ℚ)) ^ 2 ≤ 1089 * (N : ℚ) ^ 6 := by
    have hq0 := Q_zero_le N (2 * N)
    have hcast : (Q N (2 * N) 0 : ℚ) ≤ 33 * (N : ℚ) ^ 3 := by
      have h : ((Q N (2 * N) 0 : ℕ) : ℚ)
          ≤ ((((2 * N + 1) ^ 2 + 4 * N * (N + 1) * (2 * N + 1) : ℕ)) : ℚ) := by
        exact_mod_cast hq0
      refine le_trans h ?_
      push_cast
      nlinarith
    calc ((Q N (2 * N) 0 : ℚ)) ^ 2 ≤ (33 * (N : ℚ) ^ 3) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hcast 2
      _ = 1089 * (N : ℚ) ^ 6 := by ring
  -- 5) 汇总
  have hfin : (sqEqCount N : ℚ) ≤ ((44592 * N ^ 6 : ℕ) : ℚ) := by
    push_cast
    calc (sqEqCount N : ℚ)
        ≤ ∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ((Q N (2 * N) n : ℚ)) ^ 2 := h1
      _ = ((Q N (2 * N) 0 : ℚ)) ^ 2
          + 2 * ∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ), ((Q N (2 * N) n : ℚ)) ^ 2 := h2
      _ ≤ 1089 * (N : ℚ) ^ 6 + 2 * (8448 * (N : ℚ) ^ 6) := by linarith [h3, h4]
      _ ≤ 44592 * (N : ℚ) ^ 6 := by nlinarith [hNQ]
  exact_mod_cast hfin

/-- **Theorem 1（`k = 2`）的积分形式**：`∫₀¹|θ_N|⁸ ≤ 44592·N⁶`（`N ≥ 1`）。 -/
theorem integral_normSq_pow_four_le (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, (Complex.normSq (theta N α)) ^ 4) ≤ 44592 * (N : ℝ) ^ 6 := by
  rw [integral_normSq_pow_four_eq]
  have h := sqEqCount_le N hN
  have h' : (sqEqCount N : ℝ) ≤ ((44592 * N ^ 6 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

end Waring
