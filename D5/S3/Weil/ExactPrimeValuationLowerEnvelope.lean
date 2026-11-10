/- GID: D5/S3/Weil/ExactPrimeValuationLowerEnvelope
   generality: G
   mirror-B: D5/B/S3/Weil/ExactPrimeValuationLowerEnvelope
   mirror-E: none(waiver:qualitative-asymptotic-estimate)
   anchors: []
   utility: none
   digest: Arbitrarily late Gronwall lower witnesses in every fixed finite exact prime-valuation fibre. -/

import D5.S3.Weil.PrimeValuationGap
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp

/-!
The finite prime set and its complete exponent function are fixed before any
Gronwall witness is chosen. Successive replacements of the p-part by p^(A p)
preserve all other valuations. The resulting integer is at most a fixed
multiple of the original integer and retains the product of the prescribed
local factors in its actual sigma/n ratio. The elementary upstream sigma
bound forces the new integer past the requested threshold.
The finite-replacement strategy was supplied by the caller in the task brief.

The local factors and fixed-scale limit are reused from PrimeValuationGap. No growing-profile uniformity,
explicit threshold, or assertion of RH is part of the conclusion.
-/

set_option autoImplicit false

namespace D5.S3.Weil.ExactPrimeValuationLowerEnvelope

open Filter
open scoped BigOperators Topology
open D5.S3.Arith.Robin.PaddingRatio

local notation "Z" => (fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℝ) / n)

/-- One replacement, with the exact selected valuation, preservation of every
other valuation, a size bound, and an actual normalized-sigma lower bound. -/
private theorem replace_prime_part {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (a : ℕ) :
    ∃ m : ℕ, m ≠ 0 ∧ m.factorization p = a ∧
      (∀ q : ℕ, q ≠ p → m.factorization q = n.factorization q) ∧
      m ≤ p ^ a * n ∧ (1 - (p : ℝ)⁻¹ ^ (a + 1)) * Z n ≤ Z m := by
  let q := ordCompl[p] n
  have hq : q ≠ 0 := (Nat.ordCompl_pos p hn).ne'
  have hcop : p.Coprime q := Nat.coprime_ordCompl hp hn
  have hdecomp : n = p ^ n.factorization p * q :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hZn : Z n =
      (1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1)) /
        (1 - (p : ℝ)⁻¹) * Z q := by
    calc
      Z n = Z (p ^ n.factorization p * q) := congrArg Z hdecomp
      _ = _ := D5.S3.Weil.PrimeValuationGap.normalized_sigma_pow_mul hp hcop _
  have hZm : Z (p ^ a * q) =
      (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) * Z q :=
    D5.S3.Weil.PrimeValuationGap.normalized_sigma_pow_mul hp hcop a
  have hnonneg : 0 ≤
      (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) * Z q := by
    rw [← hZm]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hret : 1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1) ≤ 1 :=
    sub_le_self _ (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) _)
  refine ⟨p ^ a * q, mul_ne_zero (pow_ne_zero a hp.ne_zero) hq, ?_, ?_, ?_, ?_⟩
  · rw [Nat.factorization_mul (pow_ne_zero a hp.ne_zero) hq,
      Finsupp.add_apply, hp.factorization_pow]
    simp only [q, Nat.factorization_ordCompl, Finsupp.single_eq_same,
      Finsupp.erase_same, add_zero]
  · intro r hr
    rw [Nat.factorization_mul (pow_ne_zero a hp.ne_zero) hq,
      Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_of_ne hr, zero_add]
    dsimp only [q]
    rw [Nat.factorization_ordCompl, Finsupp.erase_ne hr]
  · exact Nat.mul_le_mul_left (p ^ a) (Nat.ordCompl_le n p)
  · calc
      (1 - (p : ℝ)⁻¹ ^ (a + 1)) * Z n =
          (1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1)) *
            ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) * Z q) := by
        rw [hZn]
        ring
      _ ≤ 1 * ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) * Z q) :=
        mul_le_mul_of_nonneg_right hret hnonneg
      _ = Z (p ^ a * q) := by rw [one_mul, ← hZm]

/-- The finite surgery is constructed by induction; no finite-strip supplier
is assumed. The next replacement preserves all already prescribed primes. -/
private theorem finite_exact_valuation_surgery (S : Finset ℕ) (A : ℕ → ℕ) :
    (∀ p ∈ S, p.Prime) → ∀ n : ℕ, n ≠ 0 →
      ∃ m : ℕ, m ≠ 0 ∧ (∀ p ∈ S, m.factorization p = A p) ∧
        m ≤ (∏ p ∈ S, p ^ A p) * n ∧
        (∏ p ∈ S, (1 - (p : ℝ)⁻¹ ^ (A p + 1))) * Z n ≤ Z m := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _ n hn
      refine ⟨n, hn, ?_, ?_, ?_⟩ <;> simp
  | @insert p S hpS ih =>
      intro hS n hn
      have hp : p.Prime := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ q ∈ S, q.Prime :=
        fun q hq => hS q (Finset.mem_insert_of_mem hq)
      obtain ⟨k, hk, hkval, hksize, hkZ⟩ := ih hS' n hn
      obtain ⟨m, hm, hmp, hmval, hmsize, hmZ⟩ := replace_prime_part hp hk (A p)
      refine ⟨m, hm, ?_, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with hqp | hqS
        · subst q
          exact hmp
        · have hqp : q ≠ p := fun e => hpS (e ▸ hqS)
          exact (hmval q hqp).trans (hkval q hqS)
      · calc
          m ≤ p ^ A p * k := hmsize
          _ ≤ p ^ A p * ((∏ q ∈ S, q ^ A q) * n) :=
            Nat.mul_le_mul_left _ hksize
          _ = (∏ q ∈ insert p S, q ^ A q) * n := by
            rw [Finset.prod_insert hpS, mul_assoc]
      · calc
          (∏ q ∈ insert p S, (1 - (q : ℝ)⁻¹ ^ (A q + 1))) * Z n =
              (1 - (p : ℝ)⁻¹ ^ (A p + 1)) *
                ((∏ q ∈ S, (1 - (q : ℝ)⁻¹ ^ (A q + 1))) * Z n) := by
            rw [Finset.prod_insert hpS, mul_assoc]
          _ ≤ (1 - (p : ℝ)⁻¹ ^ (A p + 1)) * Z k :=
            mul_le_mul_of_nonneg_left hkZ
              (D5.S3.Weil.PrimeValuationGap.retention_pos hp (A p)).le
          _ ≤ Z m := hmZ

/-- Every fixed exact finite-prime valuation fibre has arbitrarily late
Gronwall lower witnesses at its retained Euler-factor product. The empty set
and zero prescribed exponents are included in the same construction. -/
theorem exact_finite_prime_valuation_robin_lower_envelope (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (A : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ m ≥ max N 5041, (∀ p ∈ S, m.factorization p = A p) ∧
      (∏ p ∈ S, (1 - (p : ℝ)⁻¹ ^ (A p + 1))) - ε ≤ robinRatio m := by
  classical
  let R : ℝ := ∏ p ∈ S, (1 - (p : ℝ)⁻¹ ^ (A p + 1))
  let c : ℕ := ∏ p ∈ S, p ^ A p
  let B : ℕ := max N 5041
  let E : ℝ := Real.exp Real.eulerMascheroniConstant
  have hR : 0 < R := Finset.prod_pos (fun p hp =>
    D5.S3.Weil.PrimeValuationGap.retention_pos (hS p hp) (A p))
  have hc : 0 < c := Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos (A p))
  have hE : 0 < E := Real.exp_pos _
  let δ : ℝ := min (1 / 4) (ε / (4 * R))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδquarter : δ ≤ 1 / 4 := min_le_left _ _
  have hδone : 0 < 1 - δ := by linarith only [hδquarter]
  have hδplus : 0 < 1 + δ := by linarith only [hδ]
  have hbudget : δ * (4 * R) ≤ ε :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * R)).mp (min_le_right _ _)
  have hRδ : 0 ≤ R * δ := mul_nonneg hR.le hδ.le
  have htwo : 2 * R * δ ≤ ε := by nlinarith only [hbudget, hRδ]
  have happrox : R - ε ≤ R * (1 - δ) / (1 + δ) := by
    apply (le_div_iff₀ hδplus).mpr
    nlinarith only [htwo, mul_nonneg hε.le hδ.le]
  let K : ℝ := R * (E * (1 - δ))
  have hK : 0 < K := mul_pos hR (mul_pos hE hδone)
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hgrowth : ∀ᶠ n : ℕ in atTop,
      (B : ℝ) < K * Real.log (Real.log (n : ℝ)) := by
    filter_upwards [hloglog.eventually (eventually_gt_atTop ((B : ℝ) / K))] with n hn
    simpa only [mul_comm] using (div_lt_iff₀ hK).mp hn
  have hscale : Tendsto (fun n : ℕ =>
      Real.log (Real.log (c * n : ℕ)) / Real.log (Real.log (n : ℝ))) atTop (𝓝 1) := by
    simpa only [Nat.cast_mul] using
      (D5.S3.Weil.PrimeValuationGap.tendsto_loglog_scale
        (Nat.cast_pos.mpr hc : (0 : ℝ) < (c : ℝ)))
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hgrowth.and (hscale.eventually_lt_const (lt_add_of_pos_right 1 hδ)))
  obtain ⟨n, hn, hgn⟩ :=
    D5.S3.Weil.GronwallLowerEnvelope.gronwall_lower_envelope δ hδ (max T 5041)
  have hnlarge : 5041 ≤ n := (le_max_right _ _).trans hn
  have hnT : T ≤ n := (le_max_left _ _).trans hn
  have hn0 : n ≠ 0 := by omega
  have hLn : 0 < Real.log (Real.log (n : ℝ)) := loglog_pos hnlarge
  have hratio_n : robinRatio n = Z n / (E * Real.log (Real.log (n : ℝ))) := by
    dsimp only [robinRatio, E]
    rw [div_div]
    congr 1
    ring
  change 1 - δ ≤ robinRatio n at hgn
  rw [hratio_n] at hgn
  have hZn : E * (1 - δ) * Real.log (Real.log (n : ℝ)) ≤ Z n := by
    have h := (le_div_iff₀ (mul_pos hE hLn)).mp hgn
    convert h using 1 <;> ring
  obtain ⟨m, hm0, hmval, hmsize, hmZ⟩ := finite_exact_valuation_surgery S A hS n hn0
  change m ≤ c * n at hmsize
  change R * Z n ≤ Z m at hmZ
  have hZm : K * Real.log (Real.log (n : ℝ)) ≤ Z m := by
    calc
      K * Real.log (Real.log (n : ℝ)) =
          R * (E * (1 - δ) * Real.log (Real.log (n : ℝ))) := by
        dsimp only [K]
        ring
      _ ≤ R * Z n := mul_le_mul_of_nonneg_left hZn hR.le
      _ ≤ Z m := hmZ
  -- Reuse the upstream divisor-sum bound, rather than assuming that surgery
  -- leaves a large integer. The growing abundancy itself forces largeness.
  have hZupper : Z m ≤ (m : ℝ) := by
    have hs : (ArithmeticFunction.sigma 1 m : ℝ) ≤ (m : ℝ) ^ 2 := by
      exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 m)
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0))).mpr
    simpa only [pow_two] using hs
  have hmB : B ≤ m := by
    have hlt : (B : ℝ) < (m : ℝ) :=
      (hT n hnT).1.trans_le (hZm.trans hZupper)
    have hnat : B < m := by exact_mod_cast hlt
    exact hnat.le
  have hmlarge : 5041 ≤ m := (le_max_right N 5041).trans hmB
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hLm : 0 < Real.log (Real.log (m : ℝ)) := loglog_pos hmlarge
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hLmono : Real.log (Real.log (m : ℝ)) ≤ Real.log (Real.log (c * n : ℕ)) :=
    Real.log_le_log hlogm
      (Real.log_le_log hmR (Nat.cast_le.mpr hmsize))
  have hLscale : Real.log (Real.log (c * n : ℕ)) ≤
      (1 + δ) * Real.log (Real.log (n : ℝ)) :=
    (div_le_iff₀ hLn).mp (hT n hnT).2.le
  have hLbound := hLmono.trans hLscale
  refine ⟨m, hmB, hmval, ?_⟩
  change R - ε ≤ robinRatio m
  calc
    R - ε ≤ R * (1 - δ) / (1 + δ) := happrox
    _ = (K * Real.log (Real.log (n : ℝ))) /
        (E * ((1 + δ) * Real.log (Real.log (n : ℝ)))) := by
      dsimp only [K]
      field_simp [hLn.ne', hE.ne', hδplus.ne'] <;> ring
    _ ≤ Z m / (E * ((1 + δ) * Real.log (Real.log (n : ℝ)))) :=
      div_le_div_of_nonneg_right hZm (mul_pos hE (mul_pos hδplus hLn)).le
    _ ≤ Z m / (E * Real.log (Real.log (m : ℝ))) :=
      div_le_div_of_nonneg_left (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_pos hE hLm) (mul_le_mul_of_nonneg_left hLbound hE.le)
    _ = robinRatio m := by
      dsimp only [robinRatio, E]
      rw [div_div]
      congr 1
      ring

#print axioms exact_finite_prime_valuation_robin_lower_envelope

end D5.S3.Weil.ExactPrimeValuationLowerEnvelope
