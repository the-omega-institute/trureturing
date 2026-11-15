/- GID: D5/S3/Arith/Robin/GronwallAbundant/Budget
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/GronwallAbundant/Budget
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Missing prime mass and uniform quantitative Chebyshev error budgets. -/

import D5.S3.Arith.Robin.GronwallAbundant.Local
import D5.S3.Arith.Robin.GronwallAbundant.Coding
import D5.S3.Weil.PrimeNumberTheorem.MediumPNT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.GronwallAbundant

open Finset Real Filter Asymptotics
open scoped BigOperators Topology

/-- The logarithmic mass beyond the first copy of each prime factor. -/
def repeatedMass (N : ℕ) : ℝ :=
  ∑ p ∈ N.primeFactors, ((N.factorization p - 1 : ℕ) : ℝ) * Real.log p

/-- Primes absent from the integer, within a specified prime prefix. -/
def missingPrimes (N P : ℕ) : Finset ℕ := Nat.primesLE P \ N.primeFactors

/-- The logarithmic mass of the absent primes. -/
def missingMass (N P : ℕ) : ℝ := ∑ p ∈ missingPrimes N P, Real.log p

/-- The first copies and the repeated copies recover the complete logarithm. -/
theorem first_layer_add_repeatedMass {N : ℕ} (hN : N ≠ 0) :
    (∑ p ∈ N.primeFactors, Real.log p) + repeatedMass N = Real.log N := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
    repeatedMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hv : 1 ≤ N.factorization p :=
    ((Nat.prime_of_mem_primeFactors hp).dvd_iff_one_le_factorization hN).mp
      (Nat.dvd_of_mem_primeFactors hp)
  rw [Nat.cast_sub hv]
  ring

/-- Exact missing-prime accounting, with no optimality or GA1 assumption. -/
theorem missing_mass_identity {N P : ℕ} (hN : N ≠ 0)
    (hprefix : N.primeFactors ⊆ Nat.primesLE P) :
    Real.log N = Chebyshev.theta P - missingMass N P + repeatedMass N := by
  have hs : missingMass N P + (∑ p ∈ N.primeFactors, Real.log p) =
      Chebyshev.theta P := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    exact Finset.sum_sdiff hprefix
  have hr := first_layer_add_repeatedMass hN
  linarith

/-- When the prime prefix lies below the logarithmic clock, its missing mass
is bounded by the Chebyshev error and the repeated mass. -/
theorem missing_mass_le_psi_error {N P : ℕ} (hN : N ≠ 0)
    (hprefix : N.primeFactors ⊆ Nat.primesLE P) (hP : (P : ℝ) ≤ Real.log N) :
    missingMass N P ≤ Chebyshev.psi P - P + repeatedMass N := by
  have hi := missing_mass_identity hN hprefix
  have ht := Chebyshev.theta_le_psi (P : ℝ)
  linarith

/-- A bound on the repeated-prime support and on each complete prime-power
logarithm gives a uniform repeated-mass budget. -/
theorem repeatedMass_le_support_budget {N : ℕ} {Y B : ℝ}
    (hY : 0 ≤ Y) (hB : 0 ≤ B)
    (hsupport : ∀ p ∈ N.primeFactors, 2 ≤ N.factorization p → (p : ℝ) ≤ Y)
    (hpower : ∀ p ∈ N.primeFactors,
      (N.factorization p : ℝ) * Real.log p ≤ B) :
    repeatedMass N ≤ (Y + 1) * B := by
  classical
  let S := N.primeFactors.filter (fun p => 2 ≤ N.factorization p)
  have heq : repeatedMass N =
      ∑ p ∈ S, ((N.factorization p - 1 : ℕ) : ℝ) * Real.log p := by
    symm
    exact Finset.sum_filter_of_ne (fun p hp hv => by
      by_contra hh
      have hz : N.factorization p - 1 = 0 := by omega
      simp [hz] at hv)
  have hterm : ∀ p ∈ S,
      ((N.factorization p - 1 : ℕ) : ℝ) * Real.log p ≤ B := by
    intro p hp
    have hpN := (Finset.mem_filter.mp hp).1
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hpN).one_lt.le)
    exact (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.sub_le (N.factorization p) 1) hlog).trans (hpower p hpN)
  have hsub : S ⊆ Finset.range (⌊Y⌋₊ + 1) := by
    intro p hp
    have hpp := Finset.mem_filter.mp hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hsupport p hpp.1 hpp.2)))
  have hcard : (S.card : ℝ) ≤ Y + 1 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_range] at hh
    have hhr : (S.card : ℝ) ≤ (⌊Y⌋₊ : ℝ) + 1 := by exact_mod_cast hh
    linarith [Nat.floor_le hY]
  rw [heq]
  calc
    _ ≤ (S.card : ℝ) * B := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hterm
    _ ≤ (Y + 1) * B := mul_le_mul_of_nonneg_right hcard hB

/-- The repeated-prime mass of a proper GA1 integer is controlled by its
logarithmic clock and the bounded prime-power coordinates. -/
theorem ga1_repeatedMass_bound {N : ℕ} (hN : IsProperGA1 N)
    (hT : 2 ≤ Real.log N) :
    repeatedMass N ≤ (Real.sqrt (2 * Real.log N) + 1) *
      Real.log (Real.log N * Real.log (Real.log N) / Real.log 2) := by
  let T : ℝ := Real.log N
  let B : ℝ := Real.log (T * Real.log T / Real.log 2)
  have hT0 : 0 < T := by dsimp [T]; linarith
  have hT2 : 2 ≤ T := hT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have harg : 1 ≤ T * Real.log T / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    have hh : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
    nlinarith
  apply repeatedMass_le_support_budget (Real.sqrt_nonneg _)
    (Real.log_nonneg harg)
  · intro p hp hv
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr
      (square_le_two_log hN hp hv)
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hplog : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hprime.two_le)
    have hpow : (p : ℝ) ^ N.factorization p ≤ primeDeletionSum N p := by
      apply Finset.single_le_sum (fun i _ => pow_nonneg hp0.le i)
      simp only [Finset.mem_range]
      omega
    have hbudget := ga1_prime_power_log_bound hN hp
    have hpowB : (p : ℝ) ^ N.factorization p ≤ T * Real.log T / Real.log 2 := by
      apply (le_div_iff₀ hlog2).mpr
      have hh := mul_le_mul hpow hplog hlog2.le
        (Finset.sum_nonneg (fun i _ => pow_nonneg hp0.le i))
      exact hh.trans hbudget
    have hlogged := Real.log_le_log (pow_pos hp0 _) hpowB
    simpa only [Real.log_pow] using hlogged

/-- A deliberately coarse power bound suffices to absorb the repeated mass
into the quantitative prime-number-theorem saving. -/
theorem ga1_repeatedMass_le_rpow {N : ℕ} (hN : IsProperGA1 N)
    (hT : 2 ≤ Real.log N) {X : ℝ} (hX : 2 ≤ X) (hTX : Real.log N ≤ X) :
    repeatedMass N ≤ 72 * X ^ (3 / 4 : ℝ) := by
  let T : ℝ := Real.log N
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hT0 : 0 < T := by dsimp [T]; linarith
  have hT2 : 2 ≤ T := hT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlogT0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT : Real.log T ≤ X := (Real.log_le_self hT0.le).trans hTX
  have hargpos : 0 < T * Real.log T / Real.log 2 := by positivity
  have hargle : T * Real.log T / Real.log 2 ≤ X ^ 3 := by
    apply (div_le_iff₀ hlog2).mpr
    have hh := mul_le_mul hTX hlogT hlogT0.le hX0.le
    have hcube : 2 * X ^ 2 ≤ X ^ 3 := by nlinarith [sq_nonneg X]
    nlinarith [mul_le_mul_of_nonneg_left hlog2lower (pow_nonneg hX0.le 3)]
  have hlogarg : Real.log (T * Real.log T / Real.log 2) ≤ 3 * Real.log X := by
    have hh := Real.log_le_log hargpos hargle
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hroot : Real.sqrt (2 * T) + 1 ≤ 3 * Real.sqrt X := by
    have htwo : Real.sqrt 2 ≤ (2 : ℝ) := by
      apply (Real.sqrt_le_iff).mpr
      norm_num
    have hrt : Real.sqrt (2 * T) ≤ 2 * Real.sqrt X := by
      calc
        _ ≤ Real.sqrt (2 * X) := Real.sqrt_le_sqrt (by linarith)
        _ = Real.sqrt 2 * Real.sqrt X := Real.sqrt_mul (by norm_num) X
        _ ≤ 2 * Real.sqrt X := mul_le_mul_of_nonneg_right htwo (Real.sqrt_nonneg X)
    have hone : (1 : ℝ) ≤ Real.sqrt X := by
      apply (Real.le_sqrt (by norm_num) hX0.le).mpr
      nlinarith
    linarith
  have hB0 : 0 ≤ Real.log (T * Real.log T / Real.log 2) := by
    have hh : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
    apply Real.log_nonneg
    apply (le_div_iff₀ hlog2).mpr
    nlinarith
  have hlogpow : Real.log X ≤ 8 * X ^ (1 / 8 : ℝ) := by
    have hh := Real.log_le_rpow_div hX0.le (by norm_num : (0 : ℝ) < 1 / 8)
    convert hh using 1 <;> ring
  calc
    repeatedMass N ≤ (Real.sqrt (2 * T) + 1) *
        Real.log (T * Real.log T / Real.log 2) := ga1_repeatedMass_bound hN hT
    _ ≤ (3 * Real.sqrt X) * (3 * Real.log X) :=
      mul_le_mul hroot hlogarg hB0 (by positivity)
    _ = 9 * Real.sqrt X * Real.log X := by ring
    _ ≤ 9 * Real.sqrt X * (8 * X ^ (1 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogpow (by positivity)
    _ = 72 * X ^ (5 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      have hh : X ^ (1 / 2 : ℝ) * X ^ (1 / 8 : ℝ) = X ^ (5 / 8 : ℝ) := by
        rw [← Real.rpow_add hX0]
        norm_num
      nlinarith only [hh]
    _ ≤ 72 * X ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by norm_num)

/-- Sublinear powers of the logarithm eventually fit within any positive
linear logarithmic budget. -/
theorem log_tenth_eventually_le (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      c * (Real.log X) ^ ((1 : ℝ) / 10) ≤ ε * Real.log X := by
  have hlim : Tendsto (fun X : ℝ => (Real.log X) ^ (-(9 / 10 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      Real.tendsto_log_atTop
  have hlimc : Tendsto (fun X : ℝ => c * (Real.log X) ^ (-(9 / 10 : ℝ)))
      atTop (𝓝 0) := by simpa only [mul_zero] using hlim.const_mul c
  have hsmall := hlimc.eventually_lt_const hε
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with X hsmall hX
  have hL : 0 < Real.log X := Real.log_pos hX
  have heq : (Real.log X) ^ ((1 : ℝ) / 10) =
      (Real.log X) ^ (-(9 / 10 : ℝ)) * Real.log X := by
    calc
      _ = (Real.log X) ^ (-(9 / 10 : ℝ) + 1) := by norm_num
      _ = (Real.log X) ^ (-(9 / 10 : ℝ)) * (Real.log X) ^ (1 : ℝ) :=
        Real.rpow_add hL _ _
      _ = _ := by rw [Real.rpow_one]
  rw [heq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hsmall.le hL.le

/-- Every fixed power below one is eventually absorbed into the exponential
power-logarithm saving. -/
theorem rpow_eventually_le_pnt_envelope (a r : ℝ) (hr : r < 1) :
    ∀ᶠ X : ℝ in atTop,
      X ^ r ≤ X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10)) := by
  filter_upwards [log_tenth_eventually_le a (sub_pos.mpr hr),
    eventually_gt_atTop (1 : ℝ)] with X hb hX
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  rw [Real.rpow_def_of_pos hX0]
  calc
    Real.exp (Real.log X * r) ≤
        Real.exp (Real.log X - a * (Real.log X) ^ ((1 : ℝ) / 10)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hb]
    _ = X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hX0]
      congr 1
      congr 1
      ring

/-- A single quantitative prime-number-theorem budget controls every smaller
nonnegative argument, including the initial finite interval. -/
theorem uniform_psi_error_budget :
    ∃ a > 0, ∃ C > 0, ∀ᶠ X : ℝ in atTop,
      ∀ y : ℝ, 0 ≤ y → y ≤ X →
        Chebyshev.psi y - y ≤
          C * (X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨D, hD, hbound⟩ := isBigO_iff'.mp hO
  obtain ⟨A, hA⟩ := eventually_atTop.mp hbound
  let a : ℝ := c * (1 / 2 : ℝ) ^ ((1 : ℝ) / 10)
  let L : ℝ := Real.log 4 + 4
  have ha : 0 < a := mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)
  have hL : 0 < L := by
    dsimp [L]
    have hh := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  refine ⟨a, ha, D + L, add_pos hD hL, ?_⟩
  have hroot : ∀ᶠ X : ℝ in atTop, A ≤ Real.sqrt X :=
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop A)
  filter_upwards [hroot, eventually_gt_atTop (1 : ℝ),
    rpow_eventually_le_pnt_envelope a (1 / 2) (by norm_num)] with X hroot hX hsave
  intro y hy0 hyX
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have henv : 0 ≤ X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10)) := by positivity
  by_cases hy : y ≤ Real.sqrt X
  · have hsmall : Chebyshev.psi y - y ≤
        L * (X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10))) := by
      calc
        _ ≤ Chebyshev.psi y := sub_le_self _ hy0
        _ ≤ L * y := Chebyshev.psi_le_const_mul_self hy0
        _ ≤ L * Real.sqrt X := mul_le_mul_of_nonneg_left hy hL.le
        _ ≤ L * (X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10))) := by
          apply mul_le_mul_of_nonneg_left _ hL.le
          simpa only [Real.sqrt_eq_rpow] using hsave
    exact hsmall.trans (mul_le_mul_of_nonneg_right (by linarith) henv)
  · have hyroot : Real.sqrt X ≤ y := (lt_of_not_ge hy).le
    have hypos : 0 < y := (Real.sqrt_pos.mpr hX0).trans_le hyroot
    have hAy : A ≤ y := hroot.trans hyroot
    have herror : Chebyshev.psi y - y ≤
        D * (y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))) := by
      have hh := hA y hAy
      have hn : ‖Chebyshev.psi y - y‖ ≤
          D * (y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))) := by
        simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs,
          abs_of_pos (mul_pos hypos (Real.exp_pos _))] using hh
      exact (le_abs_self _).trans hn
    have hlog : Real.log X / 2 ≤ Real.log y := by
      have hh := Real.log_le_log (Real.sqrt_pos.mpr hX0) hyroot
      simpa only [Real.log_sqrt hX0.le] using hh
    have hpow : (1 / 2 : ℝ) ^ ((1 : ℝ) / 10) *
        (Real.log X) ^ ((1 : ℝ) / 10) ≤
          (Real.log y) ^ ((1 : ℝ) / 10) := by
      have hh := Real.rpow_le_rpow
        (div_nonneg (Real.log_pos hX).le (by norm_num : (0 : ℝ) ≤ 2))
        hlog (by norm_num : (0 : ℝ) ≤ 1 / 10)
      calc
        _ = (Real.log X / 2) ^ ((1 : ℝ) / 10) := by
          symm
          calc
            _ = ((1 / 2 : ℝ) * Real.log X) ^ ((1 : ℝ) / 10) := by congr 1; ring
            _ = _ := Real.mul_rpow (by norm_num) (Real.log_pos hX).le
        _ ≤ _ := hh
    have hexp : Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10)) ≤
        Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10)) := by
      apply Real.exp_le_exp.mpr
      dsimp [a]
      nlinarith only [mul_le_mul_of_nonneg_left hpow hc.le]
    have hlarge : Chebyshev.psi y - y ≤
        D * (X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10))) :=
      herror.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul hyX hexp (Real.exp_pos _).le hX0.le) hD.le)
    exact hlarge.trans (mul_le_mul_of_nonneg_right (by linarith) henv)

/-- Every proper GA1 integer in the same logarithmic window obeys a
single exponential power-logarithm budget for its missing primes. -/
theorem ga1_missingMass_budget :
    ∃ a > 0, ∃ C > 0, ∀ᶠ X : ℝ in atTop,
      ∀ N P : ℕ, IsProperGA1 N → Real.log N ≤ X →
        N.primeFactors ⊆ Nat.primesLE P → (P : ℝ) ≤ Real.log N →
          missingMass N P ≤
            C * (X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10))) := by
  obtain ⟨a, ha, C, hC, hbudget⟩ := uniform_psi_error_budget
  refine ⟨a, ha, C + 72, by linarith, ?_⟩
  filter_upwards [hbudget, eventually_ge_atTop (2 : ℝ),
    rpow_eventually_le_pnt_envelope a (3 / 4) (by norm_num)] with X hb hX hsave
  intro N P hN hNX hprefix hP
  have hN0 : N ≠ 0 := by have := hN.1.2.1; omega
  have herr := hb (P : ℝ) (by positivity) (hP.trans hNX)
  have hrep := ga1_repeatedMass_le_rpow hN (proper_log_ge_two hN) hX hNX
  have hm := missing_mass_le_psi_error hN0 hprefix hP
  have hrep' : repeatedMass N ≤
      72 * (X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10))) :=
    hrep.trans (mul_le_mul_of_nonneg_left hsave (by norm_num))
  nlinarith only [hm, herr, hrep']

/-- The available integer coordinates for the support endpoint. -/
def codeM (X : ℝ) : ℕ := ⌊X⌋₊ + 1

/-- Every prime beyond this cutoff occurs at most once. -/
def codeL (X : ℝ) : ℕ := ⌊Real.sqrt (2 * X)⌋₊ + 1

/-- A coarse exponent bound sufficient for the small-prime code. -/
def codeA (X : ℝ) : ℕ := ⌈2 * X⌉₊

/-- An integer upper bound on the number of omitted large primes. -/
def codeK (X B : ℝ) : ℕ := ⌈2 * B / Real.log X⌉₊ + 1

/-- The rounded hole parameter dominates its real mass allowance. -/
theorem codeK_lower (X B : ℝ) : 2 * B / Real.log X ≤ (codeK X B : ℝ) := by
  have hh := Nat.le_ceil (2 * B / Real.log X)
  dsimp [codeK]
  push_cast
  linarith

/-- Rounding adds at most two to the real mass allowance. -/
theorem codeK_upper {X B : ℝ} (hX : 1 < X) (hB : 0 ≤ B) :
    (codeK X B : ℝ) ≤ 2 * B / Real.log X + 2 := by
  have hnonneg : 0 ≤ 2 * B / Real.log X :=
    div_nonneg (by positivity) (Real.log_pos hX).le
  have hh := Nat.ceil_lt_add_one hnonneg
  dsimp [codeK]
  push_cast
  linarith

/-- The eventual counting scale absorbs the constant added by logarithmic counting. -/
theorem pnt_count_scale_eventually_ge_one (c : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      1 ≤ X / Real.log X * Real.exp (-c * (Real.log X) ^ ((1 : ℝ) / 10)) := by
  have hlog := (isLittleO_log_rpow_atTop (r := (3 / 4 : ℝ)) (by norm_num)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    rpow_eventually_le_pnt_envelope c (3 / 4) (by norm_num), hlog] with X hX henv hlog
  have hL : 0 < Real.log X := Real.log_pos hX
  have hh : Real.log X ≤ X ^ (3 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hL,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ X) _), one_mul] using hlog
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hL).mpr
  simpa only [one_mul] using hh.trans henv

/-- The entire prime support lies below the integer's logarithmic clock. -/
theorem ga1_endpoint_bound {N : ℕ} (hN : IsProperGA1 N) :
    (primeEnd N : ℝ) ≤ Real.log N := by
  have hN1 : 1 < N := hN.1.2.1
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1.le)
  have hbound : primeEnd N ≤ ⌊Real.log N⌋₊ :=
    Finset.sup_le (fun q hq => Nat.le_floor (prime_le_log hN hq))
  exact (show (primeEnd N : ℝ) ≤ (⌊Real.log N⌋₊ : ℝ) by exact_mod_cast hbound).trans
    (Nat.floor_le hlog)

/-- Prime-power divisibility bounds all exponents by twice the logarithmic cutoff. -/
theorem ga1_exponent_bound {N : ℕ} (hN : IsProperGA1 N) {X : ℝ}
    (hNX : Real.log N ≤ X) (q : ℕ) : N.factorization q ≤ codeA X := by
  by_cases hz : N.factorization q = 0
  · rw [hz]
    exact Nat.zero_le _
  have hq : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hz
  have hp := Nat.prime_of_mem_primeFactors hq
  have hN0 : 0 < N := by have := hN.1.2.1; omega
  have hd : q ^ N.factorization q ≤ N := Nat.le_of_dvd hN0 (Nat.ordProj_dvd N q)
  have hp0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
  have hlog := Real.log_le_log (pow_pos hp0 _)
    (show (q : ℝ) ^ N.factorization q ≤ N by exact_mod_cast hd)
  rw [Real.log_pow] at hlog
  have hlogq : (1 / 2 : ℝ) ≤ Real.log q := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ q by exact_mod_cast hp.two_le)
    linarith [Real.log_two_gt_d9]
  have hreal : (N.factorization q : ℝ) ≤ 2 * X := by
    nlinarith [mul_le_mul_of_nonneg_left hlogq (Nat.cast_nonneg (N.factorization q))]
  exact_mod_cast hreal.trans (Nat.le_ceil (2 * X))

/-- Large primes have only the two exponent values used by the binary code. -/
theorem ga1_large_exponent_bound {N : ℕ} (hN : IsProperGA1 N) {X : ℝ}
    (hX : 2 ≤ X) (hNX : Real.log N ≤ X) (q : ℕ) (hqL : codeL X ≤ q) :
    N.factorization q ≤ 1 := by
  by_contra hv
  have hv2 : 2 ≤ N.factorization q := by omega
  have hq : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  have hpow := square_le_two_log hN hq hv2
  have hqR : Real.sqrt (2 * X) < q := by
    apply (Nat.lt_floor_add_one (Real.sqrt (2 * X))).trans_le
    exact_mod_cast hqL
  have hroot : Real.sqrt (2 * X) ^ 2 = 2 * X := Real.sq_sqrt (by linarith)
  nlinarith [Real.sqrt_nonneg (2 * X), (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]

/-- Every omitted large prime spends at least half the logarithmic cutoff. -/
theorem upperHoles_card_le_mass (N : ℕ) {X : ℝ} (hX : 2 ≤ X) :
    ((upperHoles N (codeL X)).card : ℝ) ≤
      2 * missingMass N (primeEnd N) / Real.log X := by
  let H := upperHoles N (codeL X)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hsub : H ⊆ missingPrimes N (primeEnd N) := by
    intro q hq
    obtain ⟨hqend, hprime, hqL, hnot⟩ := Finset.mem_filter.mp hq
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨?_, hprime⟩, ?_⟩
    · exact Nat.le_of_lt_succ (Finset.mem_range.mp hqend)
    · intro hd
      exact hnot (Nat.dvd_of_mem_primeFactors hd)
  have hweight : ∀ q ∈ H, Real.log X / 2 ≤ Real.log q := by
    intro q hq
    have hqL := (Finset.mem_filter.mp hq).2.2.1
    have hqroot : Real.sqrt X ≤ (q : ℝ) := by
      have hh : Real.sqrt (2 * X) < q :=
        (Nat.lt_floor_add_one (Real.sqrt (2 * X))).trans_le (by exact_mod_cast hqL)
      exact (Real.sqrt_le_sqrt (by linarith : X ≤ 2 * X)).trans hh.le
    have hh := Real.log_le_log (Real.sqrt_pos.mpr (by linarith : 0 < X)) hqroot
    simpa only [Real.log_sqrt (by linarith : 0 ≤ X)] using hh
  have hsum : (H.card : ℝ) * (Real.log X / 2) ≤ missingMass N (primeEnd N) := by
    calc
      _ ≤ ∑ q ∈ H, Real.log q := by
        simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hweight
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => by
        have hp := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hq).1
        exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
  apply (le_div_iff₀ hlogX).mpr
  nlinarith

/-- The mass budget becomes the cardinality parameter required by the finite code. -/
theorem ga1_holes_bound {N : ℕ} {X B : ℝ} (hX : 2 ≤ X)
    (hB : missingMass N (primeEnd N) ≤ B) :
    (upperHoles N (codeL X)).card ≤ codeK X B := by
  have hh := upperHoles_card_le_mass N hX
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hreal : ((upperHoles N (codeL X)).card : ℝ) ≤ 2 * B / Real.log X :=
    hh.trans (div_le_div_of_nonneg_right (by linarith) hlogX.le)
  have hceil : (upperHoles N (codeL X)).card ≤ ⌈2 * B / Real.log X⌉₊ := by
    exact_mod_cast hreal.trans (Nat.le_ceil _)
  exact hceil.trans (Nat.le_succ _)

/-- A common missing-mass budget bounds the actual proper GA1 counting function. -/
theorem ga1_count_code_bound {X B : ℝ} (hX : 2 ≤ X)
    (hbudget : ∀ N : ℕ, IsProperGA1 N → Real.log N ≤ X →
      missingMass N (primeEnd N) ≤ B) :
    Q1 (Real.exp X) ≤ codeM X * (codeA X + 1) ^ codeL X *
      (∑ j ∈ Finset.range (codeK X B + 1), (codeM X).choose j) := by
  classical
  let s := (Finset.range (⌊Real.exp X⌋₊ + 1)).filter IsProperGA1
  have hlog : ∀ N ∈ s, Real.log N ≤ X := by
    intro N hN
    obtain ⟨hrange, hproper⟩ := Finset.mem_filter.mp hN
    have hfloor : N ≤ ⌊Real.exp X⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hrange)
    have hreal : (N : ℝ) ≤ Real.exp X :=
      (show (N : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) by exact_mod_cast hfloor).trans
        (Nat.floor_le (Real.exp_pos X).le)
    have hh := Real.log_le_log
      (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by have := hproper.1.2.1; omega)) hreal
    simpa only [Real.log_exp] using hh
  apply prime_code_card_bound s (codeM X) (codeL X) (codeA X) (codeK X B)
  · intro N hN
    have hp := (Finset.mem_filter.mp hN).2
    have := hp.1.2.1
    omega
  · intro N hN
    exact Nat.lt_succ_of_le (Nat.le_floor
      ((ga1_endpoint_bound (Finset.mem_filter.mp hN).2).trans (hlog N hN)))
  · intro N hN q
    exact ga1_exponent_bound (Finset.mem_filter.mp hN).2 (hlog N hN) q
  · intro N hN q hq
    exact ga1_large_exponent_bound (Finset.mem_filter.mp hN).2 hX (hlog N hN) q hq
  · intro N hN
    exact ga1_holes_bound hX (hbudget N (Finset.mem_filter.mp hN).2 (hlog N hN))

end D5.S3.Arith.Robin.GronwallAbundant
