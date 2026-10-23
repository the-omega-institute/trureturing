/- GID: D5/S3/Arith/Robin/OriginalMaximumPurePackets
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalMaximumPurePackets
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Full original maximality is equivalent to all legal pure packet comparisons. -/

import D5.S3.Arith.Robin.OriginalFirstClockTransport
import D5.S3.Arith.GoldenResourceObjectiveFactorization
import Mathlib.Data.Nat.Factorization.Basic

/-!
The finite Euler min/max identity is AVB10 in
`Library/ArithSums/nicolas2025comparison.md`. The pure-packet reduction follows
LR7--LR15 of `legal-replacement-main-upper-proof.md`: exact Euler modularity
and strict logarithmic curvature reduce every mixed comparison to its legal
gcd and lcm packets. All prime-power layers and every maximizing tie remain
in scope; no attainment or initial-height payment is asserted.
-/

noncomputable section
open Classical Finset

namespace D5.S3.Arith.Robin.OriginalMaximumPurePackets

open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResourceObjectiveFactorization

local notation "W" => (fun n : ℕ =>
  Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / (n : ℝ)))
local notation "T" => (fun n : ℕ =>
  Real.log (Real.log (Real.log (n : ℝ))))

/-- The mandatory floor alone puts the actual natural clock in `(1,∞)`. -/
private theorem legal_clock {p n : ℕ} (hp : 0 < p) (hn : 1 ≤ n)
    (hfloor : 5040 * p ∣ n) : 1 < Real.log (n : ℝ) := by
  have hn0 : 0 < n := by omega
  have hf3 : (3 : ℕ) ≤ 5040 * p := by nlinarith
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hf3.trans (Nat.le_of_dvd hn0 hfloor)
  exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hn0)).mpr
    (Real.exp_one_lt_three.trans_le hn3)

/-- Exact Euler modularity at the natural meet and join. The finite ambient
support contains the complete exponent stacks of all four integers. -/
private theorem euler_modular {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hG : 0 < Nat.gcd N M) (hH : 0 < Nat.lcm N M) :
    W (Nat.gcd N M) + W (Nat.lcm N M) = W N + W M := by
  let S := ((Nat.gcd N M).primeFactors ∪ (Nat.lcm N M).primeFactors) ∪
    (N.primeFactors ∪ M.primeFactors)
  have hGS : (Nat.gcd N M).primeFactors ⊆ S := by
    intro q hq
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl hq)))
  have hHS : (Nat.lcm N M).primeFactors ⊆ S := by
    intro q hq
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr hq)))
  have hNS : N.primeFactors ⊆ S := by
    intro q hq
    exact mem_union.mpr (Or.inr (mem_union.mpr (Or.inl hq)))
  have hMS : M.primeFactors ⊆ S := by
    intro q hq
    exact mem_union.mpr (Or.inr (mem_union.mpr (Or.inr hq)))
  have hGs := golden_resource_objective_sum_on 0 (by omega : 1 ≤ Nat.gcd N M) S hGS
  have hHs := golden_resource_objective_sum_on 0 (by omega : 1 ≤ Nat.lcm N M) S hHS
  have hNs := golden_resource_objective_sum_on 0 (by omega : 1 ≤ N) S hNS
  have hMs := golden_resource_objective_sum_on 0 (by omega : 1 ≤ M) S hMS
  rw [golden_resource_sigma_identity 0 (by omega : 1 ≤ Nat.gcd N M)] at hGs
  rw [golden_resource_sigma_identity 0 (by omega : 1 ≤ Nat.lcm N M)] at hHs
  rw [golden_resource_sigma_identity 0 (by omega : 1 ≤ N)] at hNs
  rw [golden_resource_sigma_identity 0 (by omega : 1 ≤ M)] at hMs
  simp only [zero_mul, sub_zero] at hGs hHs hNs hMs
  change Real.log ((ArithmeticFunction.sigma 1 (Nat.gcd N M) : ℝ) /
      (Nat.gcd N M : ℝ)) +
    Real.log ((ArithmeticFunction.sigma 1 (Nat.lcm N M) : ℝ) /
      (Nat.lcm N M : ℝ)) =
    Real.log ((ArithmeticFunction.sigma 1 N : ℝ) / (N : ℝ)) +
      Real.log ((ArithmeticFunction.sigma 1 M : ℝ) / (M : ℝ))
  rw [hGs, hHs, hNs, hMs, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  have hg : (Nat.gcd N M).factorization q =
      min (N.factorization q) (M.factorization q) := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f q)
      (Nat.factorization_gcd hN.ne' hM.ne')
    change (Nat.gcd N M).factorization q =
      min (N.factorization q) (M.factorization q) at h
    exact h
  have hl : (Nat.lcm N M).factorization q =
      max (N.factorization q) (M.factorization q) := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f q)
      (Nat.factorization_lcm hN.ne' hM.ne')
    change (Nat.lcm N M).factorization q =
      max (N.factorization q) (M.factorization q) at h
    exact h
  rw [hg, hl]
  rcases le_total (N.factorization q) (M.factorization q) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, add_comm]

/-- Exact LR10, before any maximality premise. -/
private theorem deficit_identity {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hG : 0 < Nat.gcd N M) (hH : 0 < Nat.lcm N M) :
    originalObjective N - originalObjective M =
      (originalObjective N - originalObjective (Nat.gcd N M)) +
      (originalObjective N - originalObjective (Nat.lcm N M)) +
      (T N + T M - T (Nat.gcd N M) - T (Nat.lcm N M)) := by
  have h := euler_modular hN hM hG hH
  unfold originalObjective
  linarith

/-- Strict concave log-log rectangle on its actual positive-log domain.
Here `a,b,c,d` will be the logs of `gcd,N,M,lcm`, respectively. -/
private theorem strict_loglog_rectangle {a b c d : ℝ}
    (ha : 1 < a) (hab : a < b) (hac : a < c) (hbalance : a + d = b + c) :
    Real.log (Real.log a) + Real.log (Real.log d) <
      Real.log (Real.log b) + Real.log (Real.log c) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hd1 : 1 < d := by linarith
  have hd0 : 0 < d := by linarith
  have hd : d = b + c - a := by linarith
  have hprod : a * d < b * c := by
    rw [hd]
    nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr hac)]
  have hlogs : Real.log a + Real.log d < Real.log b + Real.log c := by
    have h := Real.log_lt_log (mul_pos ha0 hd0) hprod
    rwa [Real.log_mul ha0.ne' hd0.ne', Real.log_mul hb0.ne' hc0.ne'] at h
  have hla : 0 < Real.log a := Real.log_pos ha
  have hld : 0 < Real.log d := Real.log_pos hd1
  have hlb : Real.log a < Real.log b := Real.log_lt_log ha0 hab
  have hlc : Real.log a < Real.log c := Real.log_lt_log ha0 hac
  have hprodlog : Real.log a * Real.log d < Real.log b * Real.log c := by
    have hw := mul_lt_mul_of_pos_left hlogs hla
    nlinarith [mul_nonneg (sub_nonneg.mpr hlb.le) (sub_nonneg.mpr hlc.le)]
  have h := Real.log_lt_log (mul_pos hla hld) hprodlog
  rwa [Real.log_mul hla.ne' hld.ne',
    Real.log_mul (hla.trans hlb).ne' (hla.trans hlc).ne'] at h

/-- An incomparable legal competitor is strictly worse once its two actual
pure packets are weakly worse. No full-domain maximum is a premise. -/
private theorem mixed_packet_strict {p N M : ℕ} (hp : 0 < p)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hfloorN : 5040 * p ∣ N)
    (hfloorM : 5040 * p ∣ M) (hNM : ¬N ∣ M) (hMN : ¬M ∣ N)
    (hdown : originalObjective (Nat.gcd N M) ≤ originalObjective N)
    (hup : originalObjective (Nat.lcm N M) ≤ originalObjective N) :
    originalObjective M < originalObjective N := by
  have hN0 : 0 < N := by omega
  have hM0 : 0 < M := by omega
  have hprod := Nat.gcd_mul_lcm N M
  have hG0 : 0 < Nat.gcd N M := by
    by_contra h
    have hz : Nat.gcd N M = 0 := by omega
    have hd := Nat.gcd_dvd_left N M
    rw [hz] at hd
    have : N = 0 := by simpa using hd
    omega
  have hH0 : 0 < Nat.lcm N M := by
    by_contra h
    have hz : Nat.lcm N M = 0 := by omega
    rw [hz, mul_zero] at hprod
    have := Nat.mul_pos hN0 hM0
    omega
  have hfloorG : 5040 * p ∣ Nat.gcd N M := Nat.dvd_gcd hfloorN hfloorM
  have hGclock := legal_clock hp (by omega : 1 ≤ Nat.gcd N M) hfloorG
  have hGN : Nat.gcd N M < N := by
    have hle := Nat.le_of_dvd hN0 (Nat.gcd_dvd_left N M)
    by_contra h
    have he : Nat.gcd N M = N := by omega
    have hd := Nat.gcd_dvd_right N M
    rw [he] at hd
    exact hNM hd
  have hGM : Nat.gcd N M < M := by
    have hle := Nat.le_of_dvd hM0 (Nat.gcd_dvd_right N M)
    by_contra h
    have he : Nat.gcd N M = M := by omega
    have hd := Nat.gcd_dvd_left N M
    rw [he] at hd
    exact hMN hd
  have hGNlog : Real.log (Nat.gcd N M : ℝ) < Real.log (N : ℝ) :=
    Real.log_lt_log (by exact_mod_cast hG0) (by exact_mod_cast hGN)
  have hGMlog : Real.log (Nat.gcd N M : ℝ) < Real.log (M : ℝ) :=
    Real.log_lt_log (by exact_mod_cast hG0) (by exact_mod_cast hGM)
  have hlogs : Real.log (Nat.gcd N M : ℝ) + Real.log (Nat.lcm N M : ℝ) =
      Real.log (N : ℝ) + Real.log (M : ℝ) := by
    rw [← Real.log_mul (by exact_mod_cast hG0.ne') (by exact_mod_cast hH0.ne'),
      ← Real.log_mul (by exact_mod_cast hN0.ne') (by exact_mod_cast hM0.ne')]
    apply congrArg Real.log
    exact_mod_cast Nat.gcd_mul_lcm N M
  have hrectangle := strict_loglog_rectangle hGclock hGNlog hGMlog hlogs
  have hidentity := deficit_identity hN0 hM0 hG0 hH0
  change T (Nat.gcd N M) + T (Nat.lcm N M) < T N + T M at hrectangle
  linarith

/-- For every positive forcing label and every positive integer above its
mandatory `5040*p` floor, full literal original maximality is equivalent to
all legal divisor and all legal multiple packet comparisons. Packets have
no size, prime-count, layer-count or ceiling restriction. -/
theorem original_maximizes_iff_pure_packets {p N : ℕ} (hp : 0 < p)
    (hN : 1 ≤ N) (hfloorN : 5040 * p ∣ N) :
    originalMaximizes p N ↔
      (∀ D : ℕ, 1 ≤ D → 5040 * p ∣ D → D ∣ N →
        originalObjective D ≤ originalObjective N) ∧
      (∀ U : ℕ, 1 ≤ U → 5040 * p ∣ U → N ∣ U →
        originalObjective U ≤ originalObjective N) := by
  constructor
  · intro hmax
    exact ⟨fun D hD hf _ => hmax.2.2 D hD hf,
      fun U hU hf _ => hmax.2.2 U hU hf⟩
  · rintro ⟨hdown, hup⟩
    refine ⟨hN, hfloorN, ?_⟩
    intro M hM hfloorM
    by_cases hNM : N ∣ M
    · exact hup M hM hfloorM hNM
    by_cases hMN : M ∣ N
    · exact hdown M hM hfloorM hMN
    have hG0 : 0 < Nat.gcd N M := by
      by_contra h
      have hz : Nat.gcd N M = 0 := by omega
      have hd := Nat.gcd_dvd_left N M
      rw [hz] at hd
      have : N = 0 := by simpa using hd
      omega
    have hH0 : 0 < Nat.lcm N M := by
      have hprod := Nat.gcd_mul_lcm N M
      by_contra h
      have hz : Nat.lcm N M = 0 := by omega
      rw [hz, mul_zero] at hprod
      have : 0 < N * M := Nat.mul_pos (by omega) (by omega)
      omega
    have hfloorG : 5040 * p ∣ Nat.gcd N M := Nat.dvd_gcd hfloorN hfloorM
    have hfloorH : 5040 * p ∣ Nat.lcm N M :=
      hfloorN.trans (Nat.dvd_lcm_left N M)
    have hG := hdown (Nat.gcd N M) (by omega) hfloorG (Nat.gcd_dvd_left N M)
    have hH := hup (Nat.lcm N M) (by omega) hfloorH (Nat.dvd_lcm_left N M)
    exact (mixed_packet_strict hp hN hM hfloorN hfloorM hNM hMN hG hH).le

end D5.S3.Arith.Robin.OriginalMaximumPurePackets

#print axioms D5.S3.Arith.Robin.OriginalMaximumPurePackets.original_maximizes_iff_pure_packets
