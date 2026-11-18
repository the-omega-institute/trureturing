/- GID: D5/S3/Arith/Robin/GronwallAbundant/Upper
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/GronwallAbundant/Upper
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Quantitative prime error and missing-set entropy improve the proper GA1 counting bound. -/

import D5.S3.Arith.Robin.GronwallAbundant.Asymptotic

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.GronwallAbundant
open Finset Real Filter
open scoped BigOperators Topology

/-- The actual counting function is bounded by the logarithmic cost of its injective code. -/
theorem ga1_log_count_le_cost {X B : ℝ} (hX : 2 ≤ X)
    (hKM : codeK X B ≤ codeM X)
    (hbudget : ∀ N : ℕ, IsProperGA1 N → Real.log N ≤ X →
      missingMass N (primeEnd N) ≤ B) :
    Real.log (1 + (Q1 (Real.exp X) : ℝ)) ≤ codeCost X B := by
  let M := codeM X
  let A := codeA X
  let L := codeL X
  let K := codeK X B
  let S : ℝ := ∑ j ∈ Finset.range (K + 1), (M.choose j : ℝ)
  have hM : (0 : ℝ) < M := by dsimp [M, codeM]; positivity
  have hA : (0 : ℝ) < A + 1 := by positivity
  have hK : 1 ≤ K := by dsimp [K, codeK]; omega
  have hS : 1 ≤ S := by
    dsimp [S]
    have hh := Finset.single_le_sum (s := Finset.range (K + 1))
      (f := fun j => (M.choose j : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (show 0 ∈ Finset.range (K + 1) by simp)
    simpa only [Nat.choose_zero_right, Nat.cast_one] using hh
  have hSP : 0 < S := by linarith
  have hR : 1 ≤ (M : ℝ) * ((A : ℝ) + 1) ^ L * S := by
    have hm1 : (1 : ℝ) ≤ M := by dsimp [M, codeM]; exact_mod_cast Nat.le_add_left 1 ⌊X⌋₊
    have ha1 : (1 : ℝ) ≤ (A : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) A]
    have hp : (1 : ℝ) ≤ ((A : ℝ) + 1) ^ L := one_le_pow₀ ha1
    have hmp : 1 ≤ (M : ℝ) * ((A : ℝ) + 1) ^ L := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (sub_nonneg.mpr hp)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmp) (sub_nonneg.mpr hS)]
  have hq : (Q1 (Real.exp X) : ℝ) ≤ (M : ℝ) * ((A : ℝ) + 1) ^ L * S := by
    have hh := ga1_count_code_bound hX hbudget
    have hhR := (Nat.cast_le (α := ℝ)).mpr hh
    push_cast at hhR
    simpa only [M, A, L, K, S] using hhR
  have hmain : Real.log (1 + (Q1 (Real.exp X) : ℝ)) ≤
      Real.log (2 * ((M : ℝ) * ((A : ℝ) + 1) ^ L * S)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogS : Real.log S ≤ (K : ℝ) * (1 + Real.log ((M : ℝ) / K)) := by
    have hh := binomial_partial_sum_entropy M K hK hKM
    have hlog := Real.log_le_log hSP hh
    simpa only [Real.log_exp] using hlog
  rw [Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by positivity) hSP.ne',
    Real.log_mul hM.ne' (pow_pos hA _).ne', Real.log_pow] at hmain
  dsimp [codeCost]
  change Real.log (1 + (Q1 (Real.exp X) : ℝ)) ≤
    Real.log 2 + Real.log (M : ℝ) + (L : ℝ) * Real.log ((A : ℝ) + 1) +
      (K : ℝ) * (1 + Real.log ((M : ℝ) / K))
  linarith

/-- The proper GA1 counting function has an exponential power-logarithm saving. -/
theorem result : ∃ a > 0, ∃ C > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀,
    Real.log (1 + (Q1 x : ℝ)) ≤
      C * (Real.log x / Real.log (Real.log x)) *
        Real.exp (-a * (Real.log (Real.log x)) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, C, hC, hbudget⟩ := ga1_missingMass_budget
  obtain ⟨a, ha, D, hD, hcost⟩ := code_cost_eventually c C hc hC
  have hfinal : ∀ᶠ X : ℝ in atTop,
      Real.log (1 + (Q1 (Real.exp X) : ℝ)) ≤
        D * (X / Real.log X) * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10)) := by
    filter_upwards [hbudget, hcost, eventually_ge_atTop (2 : ℝ)] with X hb hs hX
    apply (ga1_log_count_le_cost hX hs.1 ?_).trans hs.2
    intro N hN hNX
    apply hb N (primeEnd N) hN hNX
    · intro q hq
      exact Nat.mem_primesLE.mpr ⟨Finset.le_sup (f := id) hq,
        Nat.prime_of_mem_primeFactors hq⟩
    · exact ga1_endpoint_bound hN
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hfinal
  refine ⟨a, ha, D, hD, Real.exp X₀, ?_⟩
  intro x hx
  have hx0 : 0 < x := (Real.exp_pos X₀).trans_le hx
  have hlog : X₀ ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  simpa only [Real.exp_log hx0] using hX₀ (Real.log x) hlog

end D5.S3.Arith.Robin.GronwallAbundant
