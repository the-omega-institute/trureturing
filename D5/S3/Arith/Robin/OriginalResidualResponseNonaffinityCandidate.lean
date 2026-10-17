/- GID: D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate
   mirror-E: none(waiver:finite-analytic-inequality)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt, mathlib/module/Mathlib.NumberTheory.Bertrand]
   utility: none
   digest: The original Mobius floor response has a quantitative defect from every affine vector on its complete integer block. -/

import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
UNCOMPILED candidate. This file has not been submitted to Lean, the kernel,
Reg, a current report or CI. It does not modify an original/frozen owner.

The final theorem concerns the literal original `response`, with its original
natural floors and every original Mobius row. Its affine coordinates are
exactly the original partial-cell Gram coordinates `(1, m/N)`.

Every private helper below is consumed by the final nonaffinity proof. There
are no added axioms, admitted goals, `sorry`, surrogate response definitions,
good-height hypotheses or supplied sign assumptions.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open D5.S3.Arith.Robin.OriginalResidualFiniteTransfer (coefficient response)

namespace D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate

private theorem moebius_divisor_sum_zero {t : ℕ} (ht : t ≠ 1) :
    (∑ d ∈ t.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f t)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply,
    if_neg ht] using h

private theorem full_divisor_coefficient_sum {N t : ℕ}
    (hN : 0 < N) (ht : 1 < t) :
    (∑ d ∈ t.divisors, coefficient N d) =
      ArithmeticFunction.vonMangoldt t / Real.log (N : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hzero := moebius_divisor_sum_zero (t := t) (by omega)
  have hlog :
      (∑ d ∈ t.divisors,
        (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) =
        -ArithmeticFunction.vonMangoldt t := by
    simpa only [ArithmeticFunction.log_apply] using
      (ArithmeticFunction.sum_moebius_mul_log_eq (n := t))
  calc
    (∑ d ∈ t.divisors, coefficient N d) =
        (Real.log (N : ℝ) *
            (∑ d ∈ t.divisors, (ArithmeticFunction.moebius d : ℝ)) -
          ∑ d ∈ t.divisors,
            (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) /
          Real.log (N : ℝ) := by
      simp only [coefficient]
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : (d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      rw [Real.log_div hN0 hd0]
      ring
    _ = ArithmeticFunction.vonMangoldt t / Real.log (N : ℝ) := by
      rw [hzero, hlog]
      ring

private theorem proper_divisor_lt_block_cutoff {N t d : ℕ}
    (ht0 : 0 < t) (htN : t < 2 * N) (hdt : d ∣ t) (hdne : d ≠ t) :
    d < N := by
  obtain ⟨k, hk⟩ := hdt
  have hk2 : 2 ≤ k := by
    by_contra! h
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with hk0 | hk1
    · rw [hk0, Nat.mul_zero] at hk
      omega
    · rw [hk1, Nat.mul_one] at hk
      exact hdne hk.symm
  have hdouble : 2 * d ≤ t := by
    calc
      2 * d = d * 2 := Nat.mul_comm 2 d
      _ ≤ d * k := Nat.mul_le_mul_left d hk2
      _ = t := hk.symm
  omega

/-- The literal original truncated divisor sum: the only removed divisor is t. -/
private theorem filtered_coefficient_sum_eq {N t : ℕ}
    (hN : 3 ≤ N) (hNt : N < t) (htN : t < 2 * N) :
    (∑ d ∈ (Ioc 0 N).filter (fun d => d ∣ t), coefficient N d) =
      (ArithmeticFunction.vonMangoldt t -
        (ArithmeticFunction.moebius t : ℝ) * Real.log ((N : ℝ) / t)) /
          Real.log (N : ℝ) := by
  classical
  have ht0 : 0 < t := by omega
  have hset : (Ioc 0 N).filter (fun d => d ∣ t) = t.divisors.erase t := by
    ext d
    constructor
    · intro hd
      rcases Finset.mem_filter.mp hd with ⟨hdI, hdt⟩
      rcases Finset.mem_Ioc.mp hdI with ⟨_, hdN⟩
      exact Finset.mem_erase.mpr ⟨by omega,
        Nat.mem_divisors.mpr ⟨hdt, ht0.ne'⟩⟩
    · intro hd
      rcases Finset.mem_erase.mp hd with ⟨hdne, hdmem⟩
      have hdt := (Nat.mem_divisors.mp hdmem).1
      have hdpos := Nat.pos_of_mem_divisors hdmem
      have hdN := proper_divisor_lt_block_cutoff ht0 htN hdt hdne
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hdpos, hdN.le⟩, hdt⟩
  rw [hset, Finset.sum_erase_eq_sub (Nat.mem_divisors_self t ht0.ne'),
    full_divisor_coefficient_sum (N := N) (t := t) (by omega) (by omega),
    coefficient]
  ring

private theorem floor_cast_increment (m d : ℕ) :
    (((m + 1) / d : ℕ) : ℝ) - ((m / d : ℕ) : ℝ) =
      if d ∣ m + 1 then 1 else 0 := by
  by_cases hd : d ∣ m + 1
  · rw [Nat.succ_div_of_dvd hd, if_pos hd, Nat.cast_add, Nat.cast_one]
    ring
  · rw [Nat.succ_div_of_not_dvd hd, if_neg hd]
    ring

/-- This is an increment of the original response, without replacing its floors. -/
private theorem response_succ_increment (N m : ℕ) :
    response N (m + 1) - response N m =
      (∑ d ∈ Ioc 0 N, coefficient N d / d) -
        ∑ d ∈ (Ioc 0 N).filter (fun d => d ∣ m + 1), coefficient N d := by
  classical
  have hsum :
      (∑ d ∈ Ioc 0 N, coefficient N d * ((m + 1) / d : ℕ)) -
        (∑ d ∈ Ioc 0 N, coefficient N d * (m / d : ℕ)) =
          ∑ d ∈ (Ioc 0 N).filter (fun d => d ∣ m + 1), coefficient N d := by
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    rw [← mul_sub, floor_cast_increment]
    by_cases hd : d ∣ m + 1 <;> simp only [hd, if_true, if_false, mul_one, mul_zero]
  calc
    response N (m + 1) - response N m =
        (∑ d ∈ Ioc 0 N, coefficient N d / d) -
          ((∑ d ∈ Ioc 0 N, coefficient N d * ((m + 1) / d : ℕ)) -
            ∑ d ∈ Ioc 0 N, coefficient N d * (m / d : ℕ)) := by
      simp only [response, Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := by rw [hsum]

private theorem response_increment {N t : ℕ} (ht : 0 < t) :
    response N t - response N (t - 1) =
      (∑ d ∈ Ioc 0 N, coefficient N d / d) -
        ∑ d ∈ (Ioc 0 N).filter (fun d => d ∣ t), coefficient N d := by
  have h := response_succ_increment N (t - 1)
  simpa only [Nat.sub_add_cancel (show 1 ≤ t by omega)] using h

private theorem prime_filtered_coefficient_sum {N p : ℕ}
    (hN : 3 ≤ N) (hp : p.Prime) (hNp : N < p) (hpN : p < 2 * N) :
    (∑ d ∈ (Ioc 0 N).filter (fun d => d ∣ p), coefficient N d) = 1 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [filtered_coefficient_sum_eq hN hNp hpN,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hp]
  simp only [Int.cast_neg, Int.cast_one]
  calc
    (Real.log (p : ℝ) - (-1) * Real.log ((N : ℝ) / p)) /
        Real.log (N : ℝ) = Real.log (N : ℝ) / Real.log (N : ℝ) := by
      rw [Real.log_div hN0 hp0]
      congr 1
      ring
    _ = 1 := div_self hL.ne'

private theorem even_composite_filtered_coefficient_sum_le {N t : ℕ}
    (hN : 3 ≤ N) (hNt : N < t) (htN : t < 2 * N)
    (htwo : 2 ∣ t) (htprime : ¬t.Prime) :
    (∑ d ∈ (Ioc 0 N).filter (fun d => d ∣ t), coefficient N d) ≤
      Real.log (2 : ℝ) / Real.log (N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have htr : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [filtered_coefficient_sum_eq hN hNt htN]
  by_cases hpp : IsPrimePow t
  · have hmu : ArithmeticFunction.moebius t = 0 :=
      ArithmeticFunction.moebius_apply_isPrimePow_not_prime hpp htprime
    have hLambda : ArithmeticFunction.vonMangoldt t = Real.log (2 : ℝ) := by
      rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp,
        (Nat.minFac_eq_two_iff t).mpr htwo]
      norm_num
    simpa only [hmu, Int.cast_zero, zero_mul, sub_zero, hLambda] using
      (le_refl (Real.log (2 : ℝ) / Real.log (N : ℝ)))
  · have hLambda : ArithmeticFunction.vonMangoldt t = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    have hmu : (ArithmeticFunction.moebius t : ℝ) ≤ 1 := by
      exact_mod_cast
        ((le_abs_self (ArithmeticFunction.moebius t)).trans
          (ArithmeticFunction.abs_moebius_le_one (n := t)))
    have hratio_gt : 1 < (t : ℝ) / N :=
      (one_lt_div hNr).mpr (by exact_mod_cast hNt)
    have hratio_lt : (t : ℝ) / N < 2 :=
      (div_lt_iff₀ hNr).mpr (by exact_mod_cast htN)
    have hratio_log : 0 < Real.log ((t : ℝ) / N) := Real.log_pos hratio_gt
    have hratio_log_lt : Real.log ((t : ℝ) / N) < Real.log (2 : ℝ) :=
      Real.log_lt_log (div_pos htr hNr) hratio_lt
    have hnum :
        0 - (ArithmeticFunction.moebius t : ℝ) * Real.log ((N : ℝ) / t) ≤
          Real.log (2 : ℝ) := by
      calc
        0 - (ArithmeticFunction.moebius t : ℝ) * Real.log ((N : ℝ) / t) =
            (ArithmeticFunction.moebius t : ℝ) * Real.log ((t : ℝ) / N) := by
          rw [Real.log_div hNr.ne' htr.ne', Real.log_div htr.ne' hNr.ne']
          ring
        _ ≤ 1 * Real.log ((t : ℝ) / N) :=
          mul_le_mul_of_nonneg_right hmu hratio_log.le
        _ = Real.log ((t : ℝ) / N) := one_mul _
        _ ≤ Real.log (2 : ℝ) := hratio_log_lt.le
    rw [hLambda]
    exact div_le_div_of_nonneg_right hnum hL.le

private theorem exists_internal_even_composite {N : ℕ} (hN : 3 ≤ N) :
    ∃ c : ℕ, N < c ∧ c < 2 * N ∧ 2 ∣ c ∧ ¬c.Prime := by
  by_cases htwoN : 2 ∣ N
  · have hmod : N % 2 = 0 := Nat.mod_eq_zero_of_dvd htwoN
    have hN4 : 4 ≤ N := by omega
    have htwo : 2 ∣ N + 2 := dvd_add htwoN (dvd_refl 2)
    refine ⟨N + 2, by omega, by omega, htwo, ?_⟩
    intro hp
    rcases (Nat.dvd_prime hp).mp htwo with hbad | hbad <;> omega
  · have hmod : N % 2 = 1 := by
      have hnzero : N % 2 ≠ 0 := by
        simpa only [Nat.dvd_iff_mod_eq_zero] using htwoN
      omega
    have htwo : 2 ∣ N + 1 :=
      Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    refine ⟨N + 1, by omega, by omega, htwo, ?_⟩
    intro hp
    rcases (Nat.dvd_prime hp).mp htwo with hbad | hbad <;> omega

private theorem exists_internal_prime {N : ℕ} (hN : 3 ≤ N) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p < 2 * N := by
  obtain ⟨p, hp, hNp, hpN⟩ :=
    Nat.exists_prime_lt_and_le_two_mul N (by omega)
  refine ⟨p, hp, hNp, ?_⟩
  by_contra! hnot
  have heq : p = 2 * N := by omega
  have htwo : 2 ∣ p := by
    rw [heq]
    exact ⟨N, rfl⟩
  rcases (Nat.dvd_prime hp).mp htwo with hbad | hbad <;> omega

/-- No affine vector in the original Gram coordinates equals the exact response
on its complete original integer block, for any N ≥ 3. -/
theorem response_not_affine_on_original_block {N : ℕ} (hN : 3 ≤ N) :
    ¬∃ α β : ℝ, ∀ m ∈ Ico N (2 * N),
      response N m = α + β * ((m : ℝ) / N) := by
  classical
  rintro ⟨α, β, hAff⟩
  obtain ⟨p, hp, hNp, hpN⟩ := exists_internal_prime hN
  obtain ⟨c, hNc, hcN, htwo, hcprime⟩ := exists_internal_even_composite hN
  have hAff_step (t : ℕ) (hNt : N < t) (htN : t < 2 * N) :
      response N t - response N (t - 1) = β / (N : ℝ) := by
    rw [hAff t (Finset.mem_Ico.mpr ⟨by omega, htN⟩),
      hAff (t - 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩),
      Nat.cast_sub (show 1 ≤ t by omega), Nat.cast_one]
    ring
  have hprime_step := response_increment (N := N) (t := p) (by omega)
  rw [hAff_step p hNp hpN,
    prime_filtered_coefficient_sum hN hp hNp hpN] at hprime_step
  have hcomposite_step := response_increment (N := N) (t := c) (by omega)
  rw [hAff_step c hNc hcN] at hcomposite_step
  have hcomposite_sum :=
    even_composite_filtered_coefficient_sum_le hN hNc hcN htwo hcprime
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog2 : Real.log (2 : ℝ) < Real.log (N : ℝ) :=
    Real.log_lt_log (by norm_num) (by exact_mod_cast (show 2 < N by omega))
  have hratio : Real.log (2 : ℝ) / Real.log (N : ℝ) < 1 :=
    (div_lt_one hL).mpr hlog2
  linarith

/-!
UNCOMPILED INSERTION FRAGMENT r2067. This file is not a standalone module.
No parser, elaborator, kernel, build, report, registry or CI has run on it.

Insert this body immediately before the final
`end D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate`
in the COMPLETE r2036 candidate. There are intentionally no imports or new
namespace commands: the original `response` open, finite-sum scope, imports
and PRIVATE helper context are required. Importing r2036 separately would
not expose those private helpers. The original r2036 file is unchanged.

The response gap below is derived by calling r2036's actual original
prime/composite coefficient suppliers and literal-floor increment identity.
It is not an assumed gap. Four error terms then cancel the same affine
function in the exact original coordinates (1,m/N). The four index slots
need not be distinct; adjacent prime/composite indices and a repeated
midpoint are allowed throughout.
-/

/-- Every affine function in the original Gram coordinates has a definite
pointwise defect from the original response somewhere on its original block.
This is a conditional source extension of the uncompiled r2036 context. -/
theorem response_affine_defect_lower_bound {N : ℕ} (hN : 3 ≤ N) :
    ∀ α β : ℝ, ∃ m ∈ Ico N (2 * N),
      (1 - Real.log (2 : ℝ) / Real.log (N : ℝ)) / 4 ≤
        |response N m - α - β * ((m : ℝ) / N)| := by
  classical
  intro α β
  by_contra! hsmall
  let δ : ℝ := 1 - Real.log (2 : ℝ) / Real.log (N : ℝ)
  let E : ℕ → ℝ := fun m => response N m - α - β * ((m : ℝ) / N)
  obtain ⟨p, hp, hNp, hpN⟩ := exists_internal_prime hN
  obtain ⟨c, hNc, hcN, htwo, hcprime⟩ := exists_internal_even_composite hN

  -- Actual suppliers: the prime divisor sum is 1, and the even-composite
  -- divisor sum is at most log(2)/log(N), in the ORIGINAL coefficient owner.
  have hpinc := response_increment (N := N) (t := p) (by omega)
  rw [prime_filtered_coefficient_sum hN hp hNp hpN] at hpinc
  have hcinc := response_increment (N := N) (t := c) (by omega)
  have hcomposite :=
    even_composite_filtered_coefficient_sum_le hN hNc hcN htwo hcprime
  have hresponse_gap : δ ≤
      (response N c - response N (c - 1)) -
        (response N p - response N (p - 1)) := by
    dsimp only [δ]
    linarith only [hpinc, hcinc, hcomposite]

  -- Subtracting any affine function changes every increment by the same
  -- beta/N. Consequently the four-point combination cancels it exactly.
  have herror_step (t : ℕ) (ht : 0 < t) :
      E t - E (t - 1) =
        response N t - response N (t - 1) - β / (N : ℝ) := by
    dsimp only [E]
    rw [Nat.cast_sub (show 1 ≤ t by omega), Nat.cast_one]
    ring
  have herror_gap : δ ≤ (E c - E (c - 1)) - (E p - E (p - 1)) := by
    rw [herror_step c (by omega), herror_step p (by omega)]
    linarith only [hresponse_gap]

  have hsmallE (m : ℕ) (hm : m ∈ Ico N (2 * N)) : |E m| < δ / 4 := by
    simpa only [E, δ] using hsmall m hm
  have hc0 : |E c| < δ / 4 :=
    hsmallE c (mem_Ico.mpr ⟨by omega, hcN⟩)
  have hc1 : |E (c - 1)| < δ / 4 :=
    hsmallE (c - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
  have hp0 : |E p| < δ / 4 :=
    hsmallE p (mem_Ico.mpr ⟨by omega, hpN⟩)
  have hp1 : |E (p - 1)| < δ / 4 :=
    hsmallE (p - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
  have hc_hi : E c < δ / 4 := (abs_lt.mp hc0).2
  have hcprev_lo : -(δ / 4) < E (c - 1) := (abs_lt.mp hc1).1
  have hp_lo : -(δ / 4) < E p := (abs_lt.mp hp0).1
  have hpprev_hi : E (p - 1) < δ / 4 := (abs_lt.mp hp1).2
  linarith only [herror_gap, hc_hi, hcprev_lo, hp_lo, hpprev_hi]

end D5.S3.Arith.Robin.OriginalResidualResponseNonaffinityCandidate
