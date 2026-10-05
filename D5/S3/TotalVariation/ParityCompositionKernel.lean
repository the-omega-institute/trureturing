/- GID: D5/S3/TotalVariation/ParityCompositionKernel
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParityCompositionKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity masses of uniform weak compositions and biased Bernoulli vectors. -/

import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Bits
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.ParityCompositionKernel

open Finset Real Set
open scoped BigOperators

/-- The parity-vector mass induced by the uniform weak compositions of `M` into `d` parts.
The binomial coefficient is evaluated only after the parity and support tests succeed. -/
noncomputable def R (d M : ℕ) (ξ : Fin d → Bool) : ℝ :=
  let h := ∑ i, (ξ i).toNat
  if h % 2 = M % 2 ∧ h ≤ M then
    (((M - h) / 2 + d - 1).choose (d - 1) : ℝ) /
      ((M + d - 1).choose (d - 1) : ℝ)
  else 0

/-- Independent Bernoulli masses with parameter `M / (2M + d)`, conditioned on the
parity of the total number of occupied coordinates. -/
noncomputable def Q (d M : ℕ) (ξ : Fin d → Bool) : ℝ :=
  let h := ∑ i, (ξ i).toNat
  let ν : ℝ := M / (2 * M + d)
  let η : ℝ := d / (2 * M + d)
  let p : ℝ := (1 + (-1 : ℝ) ^ M * η ^ d) / 2
  if h % 2 = M % 2 then ν ^ h * (1 - ν) ^ (d - h) / p else 0

/-- The continuous logarithmic profile of the parity density ratio. -/
private noncomputable def logProfile (d M : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ range (d - 1), log ((M : ℝ) - x + 2 * (j + 1))) -
    x * log ((M : ℝ) / (M + d))

/-- At the unconditioned Bernoulli center, the continuum cancellation leaves only
the endpoint error of the complete reciprocal sum. -/
private theorem profile_endpoint (d M : ℕ) (hd : 2 ≤ d) (hM : 3 * d ≤ M) :
    let m : ℝ := d * M / (2 * M + d)
    let s : ℝ := -(∑ j ∈ range (d - 1),
      1 / ((M : ℝ) - m + 2 * (j + 1))) - log ((M : ℝ) / (M + d))
    HasDerivAt (logProfile d M) s m ∧ 0 ≤ s ∧ s ≤ 1 / ((M : ℝ) - d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hMd : (d : ℝ) < M := by exact_mod_cast (by omega : d < M)
  have hM0 : (0 : ℝ) < M := hd0.trans hMd
  have hden : (0 : ℝ) < 2 * M + d := by positivity
  let m : ℝ := d * M / (2 * M + d)
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hmd : m < d := by
    dsimp [m]
    rw [div_lt_iff₀ hden]
    nlinarith
  let a : ℝ := M - m
  have ha : 0 < a := by dsimp [a]; linarith
  have had : (M : ℝ) - d ≤ a := by dsimp [a]; linarith
  let f : ℝ → ℝ := fun y => 1 / (a + 2 * y)
  have hfpos (y : ℝ) (hy : 0 ≤ y) : 0 < a + 2 * y := by linarith
  have hfcont : ContinuousOn f (Icc 0 d) := by
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    intro y hy
    exact (hfpos y hy.1).ne'
  have hfanti : AntitoneOn f (Icc 0 d) := by
    intro x hx y hy hxy
    exact one_div_le_one_div_of_le (hfpos x hx.1) (by linarith)
  have hint : (∫ y in (0 : ℝ)..d, f y) = -log ((M : ℝ) / (M + d)) := by
    have hcalc : (∫ y in (0 : ℝ)..d, f y) =
        log (a + 2 * d) / 2 - log a / 2 := by
      have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := (d : ℝ))
        (f := fun y => log (a + 2 * y) / 2) (f' := f)
      simp only [mul_zero, add_zero] at ht
      apply ht
      · intro y hy
        rw [uIcc_of_le (le_of_lt hd0)] at hy
        have hD : HasDerivAt (fun z : ℝ => log (a + 2 * z) / 2)
            ((2 / (a + 2 * y)) / 2) y := by
          simpa only [Pi.add_apply, id_eq, zero_add, mul_one] using
            (((hasDerivAt_const y a).add ((hasDerivAt_id y).const_mul 2)).log
              (hfpos y hy.1).ne').div_const 2
        exact hD.congr_deriv (by dsimp [f]; ring)
      · exact hfcont.intervalIntegrable_of_Icc hd0.le
    have hr : (a + 2 * d) / a = (((M : ℝ) + d) / M) ^ 2 := by
      dsimp [a, m]
      field_simp [hden.ne', hM0.ne']
      ring
    rw [hcalc, ← sub_div, ← log_div (hfpos d hd0.le).ne' ha.ne', hr, log_pow]
    have hi : ((M : ℝ) + d) / M = ((M : ℝ) / (M + d))⁻¹ := by
      rw [inv_div]
    rw [hi, log_inv]
    ring
  have hdc : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hint0 : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) d :=
    hfcont.intervalIntegrable_of_Icc hd0.le
  have hsumlo : (∫ y in (1 : ℝ)..d, f y) ≤
      ∑ j ∈ range (d - 1), f (j + 1) := by
    have ht := AntitoneOn.integral_le_sum
      (x₀ := (1 : ℝ)) (a := d - 1)
      (hfanti.mono (by
        rw [hdc]
        simp only [add_sub_cancel]
        exact Icc_subset_Icc (by norm_num) le_rfl))
    simpa only [hdc, add_sub_cancel, add_comm] using ht
  have hsumhi : (∑ j ∈ range (d - 1), f (j + 1)) ≤
      ∫ y in (0 : ℝ)..d, f y := by
    have ht := AntitoneOn.sum_le_integral
      (x₀ := (0 : ℝ)) (a := d - 1)
      (hfanti.mono (by
        rw [hdc]
        simp only [zero_add]
        exact Icc_subset_Icc le_rfl (by linarith)))
    simp only [zero_add, Nat.cast_add, Nat.cast_one] at ht
    refine ht.trans ?_
    apply intervalIntegral.integral_mono_interval le_rfl
      (by linarith [hdc]) (by linarith [hdc]) _ hint0
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact (one_div_pos.mpr (hfpos x hx.1.le)).le
  have htail : (∫ y in (0 : ℝ)..1, f y) ≤ 1 / ((M : ℝ) - d) := by
    calc
      (∫ y in (0 : ℝ)..1, f y) ≤ ∫ _ in (0 : ℝ)..1, 1 / ((M : ℝ) - d) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          ((hfcont.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc
            (by norm_num))
          intervalIntegrable_const
        intro y hy
        exact one_div_le_one_div_of_le (sub_pos.mpr hMd) (by linarith [had, hy.1])
      _ = 1 / ((M : ℝ) - d) := by simp
  have hadd : (∫ y in (0 : ℝ)..1, f y) + (∫ y in (1 : ℝ)..d, f y) =
      ∫ y in (0 : ℝ)..d, f y := by
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact (hfcont.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc
        (by norm_num)
    · exact (hfcont.mono (Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable_of_Icc
        (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have hD (j : ℕ) : HasDerivAt
        (fun x : ℝ => log ((M : ℝ) - x + 2 * (j + 1)))
        (-1 / ((M : ℝ) - m + 2 * (j + 1))) m := by
      have harg : (M : ℝ) - m + 2 * (j + 1) ≠ 0 := by
        have ht : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
        dsimp [a] at ha
        linarith
      simpa only [Pi.sub_apply, id_eq, zero_sub] using
        (((hasDerivAt_const m (M : ℝ)).sub (hasDerivAt_id m)).add_const
          (2 * ((j : ℝ) + 1))).log harg
    change HasDerivAt (logProfile d M)
      (-(∑ j ∈ range (d - 1), 1 / ((M : ℝ) - m + 2 * (j + 1))) -
        log ((M : ℝ) / (M + d))) m
    unfold logProfile
    rw [← sum_neg_distrib]
    apply HasDerivAt.sub
    · apply HasDerivAt.fun_sum
      intro j hj
      simpa only [neg_div] using hD j
    · simpa only [id_eq, one_smul, smul_eq_mul, one_mul] using
        (hasDerivAt_id m).smul_const (log ((M : ℝ) / (M + d)))
  · dsimp [f, a] at hsumhi
    rw [hint] at hsumhi
    dsimp [m] at hsumhi ⊢
    linarith
  · dsimp [f, a] at hsumlo
    rw [hint] at hadd
    dsimp [m] at hsumlo ⊢
    linarith

/- The logarithm-series remainder controls every point of the full interval,
including both sides of the unconditioned center. -/
private theorem profile_estimate (d M : ℕ) (hd : 2 ≤ d) (hM : 3 * d ≤ M) :
    let m : ℝ := d * M / (2 * M + d)
    ∀ x ∈ Icc (0 : ℝ) d,
      |logProfile d M x - logProfile d M m| ≤
        |x - m| / ((M : ℝ) - d) +
          (d - 1 : ℝ) * (x - m) ^ 2 /
            (((M : ℝ) - d / 2) * ((M : ℝ) - d)) ∧
      logProfile d M x - logProfile d M m ≤ 1 / 2 := by
  dsimp only
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hMc : 3 * (d : ℝ) ≤ M := by exact_mod_cast hM
  have hMd : (d : ℝ) < M := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hden : (0 : ℝ) < 2 * M + d := by positivity
  let m : ℝ := d * M / (2 * M + d)
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hmhalf : m ≤ (d : ℝ) / 2 := by
    dsimp [m]
    rw [div_le_iff₀ hden]
    nlinarith
  have hmd : m < d := by linarith
  let T : ℝ := M - d
  let L : ℝ := M - d / 2
  have hT : 0 < T := by dsimp [T]; linarith
  have hL : 0 < L := by dsimp [L]; linarith
  let s : ℝ := -(∑ j ∈ range (d - 1),
    1 / ((M : ℝ) - m + 2 * (j + 1))) - log ((M : ℝ) / (M + d))
  have hs := profile_endpoint d M hd hM
  change HasDerivAt (logProfile d M) s m ∧ 0 ≤ s ∧ s ≤ 1 / T at hs
  intro x hx
  let Δ : ℝ := x - m
  let a : ℕ → ℝ := fun j => M - m + 2 * (j + 1)
  have hΔ : |Δ| ≤ (d : ℝ) - m := by
    apply abs_le.mpr
    dsimp [Δ]
    constructor <;> linarith [hx.1, hx.2]
  have ha (j : ℕ) : 0 < a j ∧ L ≤ a j ∧ T ≤ a j - |Δ| := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    dsimp [a, L, T]
    constructor
    · linarith
    constructor <;> linarith
  have hz (j : ℕ) : 0 < 1 - Δ / a j := by
    have h := ha j
    have hΔle := le_abs_self Δ
    apply sub_pos.mpr
    rw [div_lt_one (ha j).1]
    linarith
  have heq (j : ℕ) :
      log ((M : ℝ) - x + 2 * (j + 1)) - log (a j) =
        log (1 - Δ / a j) := by
    have hb : 0 < (M : ℝ) - x + 2 * (j + 1) := by
      have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith [hx.2]
    rw [← log_div hb.ne' (ha j).1.ne']
    congr 1
    calc
      ((M : ℝ) - x + 2 * (j + 1)) / a j = (a j - Δ) / a j := by
        congr 1
        dsimp [a, Δ]
        ring
      _ = 1 - Δ / a j := by rw [sub_div, div_self (ha j).1.ne']
  have hrem (j : ℕ) :
      |log (1 - Δ / a j) + Δ / a j| ≤ Δ ^ 2 / (L * T) := by
    have hj := ha j
    have hu : |Δ / a j| < 1 := by
      rw [abs_div, abs_of_pos hj.1, div_lt_one hj.1]
      linarith
    have hh := Real.abs_log_sub_add_sum_range_le hu 1
    norm_num only [sum_range_one, pow_one, Nat.cast_one, div_one] at hh
    rw [add_comm] at hh
    have he : |Δ / a j| ^ 2 / (1 - |Δ / a j|) =
        Δ ^ 2 / (a j * (a j - |Δ|)) := by
      rw [abs_div, abs_of_pos hj.1, div_pow, sq_abs]
      field_simp [hj.1.ne', (lt_of_lt_of_le hT hj.2.2).ne']
    rw [he] at hh
    refine hh.trans (div_le_div_of_nonneg_left (sq_nonneg Δ)
      (mul_pos hL hT) ?_)
    exact mul_le_mul hj.2.1 hj.2.2 hT.le hj.1.le
  have htangent (j : ℕ) : log (1 - Δ / a j) ≤ -Δ / a j := by
    have hh := log_le_sub_one_of_pos (hz j)
    convert hh using 1
    ring
  have hdiff : logProfile d M x - logProfile d M m =
      (∑ j ∈ range (d - 1), log (1 - Δ / a j)) -
        Δ * log ((M : ℝ) / (M + d)) := by
    dsimp [logProfile, Δ, a]
    have hh : (∑ j ∈ range (d - 1),
        (log ((M : ℝ) - x + 2 * (j + 1)) -
          log ((M : ℝ) - m + 2 * (j + 1)))) =
        ∑ j ∈ range (d - 1), log (1 - (x - m) /
          ((M : ℝ) - m + 2 * (j + 1))) :=
      sum_congr rfl (fun j _ => heq j)
    rw [sum_sub_distrib] at hh
    nlinarith only [hh]
  have hlin : (∑ j ∈ range (d - 1), Δ / a j) +
      Δ * log ((M : ℝ) / (M + d)) = -s * Δ := by
    dsimp [s, a]
    simp only [div_eq_mul_inv, ← mul_sum]
    ring
  have herror : |logProfile d M x - logProfile d M m - s * Δ| ≤
      (d - 1 : ℝ) * Δ ^ 2 / (L * T) := by
    have hh : logProfile d M x - logProfile d M m - s * Δ =
        ∑ j ∈ range (d - 1), (log (1 - Δ / a j) + Δ / a j) := by
      rw [sum_add_distrib, hdiff]
      linarith
    rw [hh]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc
      (∑ j ∈ range (d - 1), |log (1 - Δ / a j) + Δ / a j|) ≤
          ∑ _j ∈ range (d - 1), Δ ^ 2 / (L * T) := sum_le_sum (fun j _ => hrem j)
      _ = (d - 1 : ℝ) * Δ ^ 2 / (L * T) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
        ring
  have hupper : logProfile d M x - logProfile d M m ≤ s * Δ := by
    rw [hdiff]
    have hh := sum_le_sum (s := range (d - 1)) (fun j _ => htangent j)
    simp only [neg_div, sum_neg_distrib] at hh
    linarith
  constructor
  · change |logProfile d M x - logProfile d M m| ≤
      |Δ| / T + (d - 1 : ℝ) * Δ ^ 2 / (L * T)
    calc
      _ ≤ |logProfile d M x - logProfile d M m - s * Δ| + |s * Δ| := by
        simpa only [sub_add_cancel] using abs_add_le
          (logProfile d M x - logProfile d M m - s * Δ) (s * Δ)
      _ ≤ (d - 1 : ℝ) * Δ ^ 2 / (L * T) + (1 / T) * |Δ| := by
        apply add_le_add herror
        rw [abs_mul, abs_of_nonneg hs.2.1]
        exact mul_le_mul_of_nonneg_right hs.2.2 (abs_nonneg Δ)
      _ = _ := by ring
  · have hΔd : Δ ≤ d := by dsimp [Δ]; linarith [hx.2]
    have hstep := mul_le_mul_of_nonneg_left hΔd hs.2.1
    have hstep2 := mul_le_mul_of_nonneg_right hs.2.2 hd0.le
    have hcap : (1 / T) * d ≤ (1 : ℝ) / 2 := by
      rw [one_div_mul_eq_div, div_le_iff₀ hT]
      dsimp [T]
      linarith
    exact hupper.trans (hstep.trans (hstep2.trans hcap))

/-- Summing the guarded parity counts partitions the complete weak-composition fiber. -/
private theorem actual_normalization (d M : ℕ) (hd : 1 ≤ d) :
    (∑ ξ : Fin d → Bool, R d M ξ) = 1 := by
  classical
  let A : Finset (Fin d →₀ ℕ) := univ.finsuppAntidiag M
  let parity : (Fin d →₀ ℕ) → (Fin d → Bool) := fun r i => decide (r i % 2 = 1)
  let h : (Fin d → Bool) → ℕ := fun ξ => ∑ i, (ξ i).toNat
  have hbit (r : Fin d →₀ ℕ) (i : Fin d) : (parity r i).toNat = r i % 2 := by
    simpa only [Nat.bodd, Nat.testBit_zero, parity] using
      (Nat.mod_two_of_bodd (r i)).symm
  have hsplit (r : Fin d →₀ ℕ) (hr : r ∈ A) :
      M = 2 * (∑ i, r i / 2) + h (parity r) := by
    have hs : ∑ i, r i = M := by simpa [A] using hr
    rw [← hs]
    dsimp [h]
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [hbit]
    simpa only [Nat.add_comm] using (Nat.mod_add_div (r i) 2).symm
  have hcount (ξ : Fin d → Bool) :
      (A.filter (fun r => parity r = ξ)).card =
        if h ξ % 2 = M % 2 ∧ h ξ ≤ M then
          ((M - h ξ) / 2 + d - 1).choose (d - 1) else 0 := by
    by_cases hg : h ξ % 2 = M % 2 ∧ h ξ ≤ M
    · rw [if_pos hg]
      let s : ℕ := (M - h ξ) / 2
      have hs : 2 * s + h ξ = M := by dsimp [s]; omega
      let B : Finset (Fin d →₀ ℕ) := univ.finsuppAntidiag s
      let encode : (Fin d →₀ ℕ) → (Fin d →₀ ℕ) := fun t =>
        Finsupp.equivFunOnFinite.symm (fun i => 2 * t i + (ξ i).toNat)
      have hcard : B.card = (A.filter (fun r => parity r = ξ)).card := by
        apply card_bij (fun t _ => encode t)
        · intro t ht
          have htS : ∑ i, t i = s := by simpa [B] using ht
          apply mem_filter.mpr
          constructor
          · simp only [A, mem_finsuppAntidiag, Finset.subset_univ, and_true]
            change (∑ i, (2 * t i + (ξ i).toNat)) = M
            rw [sum_add_distrib, ← mul_sum, htS]
            exact hs
          · funext i
            dsimp [parity, encode]
            have hb (b : Bool) : decide ((2 * t i + b.toNat) % 2 = 1) = b := by
              simpa only [Nat.bodd, Nat.testBit_zero, Nat.bit_val] using
                Nat.bodd_bit b (t i)
            exact hb (ξ i)
        · intro t ht u hu he
          ext i
          have hi := congrArg (fun r : Fin d →₀ ℕ => r i) he
          change 2 * t i + (ξ i).toNat = 2 * u i + (ξ i).toNat at hi
          omega
        · intro r hr
          obtain ⟨hrA, hrP⟩ := mem_filter.mp hr
          let t : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => r i / 2)
          have hrS := hsplit r hrA
          rw [hrP] at hrS
          have htS : (∑ i, t i) = s := by
            change (∑ i, r i / 2) = s
            omega
          refine ⟨t, ?_, ?_⟩
          · simpa [B] using htS
          · ext i
            change 2 * (r i / 2) + (ξ i).toNat = r i
            rw [← hrP, hbit]
            omega
      rw [← hcard, card_finsuppAntidiag_nat_eq_choose]
      simp only [card_univ, Fintype.card_fin]
      change (d + s - 1).choose s = (s + d - 1).choose (d - 1)
      rw [show d + s - 1 = s + d - 1 by omega]
      exact Nat.choose_symm_of_eq_add (by omega)
    · rw [if_neg hg]
      apply card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hrA, hrP⟩ := mem_filter.mp hr
      have hrS := hsplit r hrA
      rw [hrP] at hrS
      apply hg
      omega
  have htotal : A.card = (M + d - 1).choose (d - 1) := by
    rw [card_finsuppAntidiag_nat_eq_choose]
    simp only [card_univ, Fintype.card_fin]
    have he : d + M - 1 = M + d - 1 := by omega
    rw [he]
    exact Nat.choose_symm_of_eq_add (by omega)
  have hsum : (∑ ξ : Fin d → Bool, (A.filter (fun r => parity r = ξ)).card) = A.card := by
    exact (card_eq_sum_card_fiberwise (by intro r hr; exact mem_univ (parity r))).symm
  have hden : ((M + d - 1).choose (d - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : d - 1 ≤ M + d - 1)).ne'
  calc
    (∑ ξ : Fin d → Bool, R d M ξ) =
        (∑ ξ : Fin d → Bool, ((A.filter (fun r => parity r = ξ)).card : ℝ) /
          ((M + d - 1).choose (d - 1) : ℝ)) := by
      apply sum_congr rfl
      intro ξ _
      rw [hcount]
      dsimp [R, h]
      split_ifs <;> simp
    _ = 1 := by
      rw [← sum_div, ← Nat.cast_sum, hsum, htotal, div_self hden]

/-- Normalization and centered conditional moments of the same biased parity law. -/
private theorem reference_moments (d M : ℕ) (hd : 2 ≤ d) (hM : 3 * d ≤ M) :
    let ν : ℝ := M / (2 * M + d)
    let h : (Fin d → Bool) → ℕ := fun ξ => ∑ i, (ξ i).toNat
    (∑ ξ, Q d M ξ) = 1 ∧
    (1 / 3 : ℝ) ≤ (1 + (-1 : ℝ) ^ M * ((d : ℝ) / (2 * M + d)) ^ d) / 2 ∧
    (∑ ξ, Q d M ξ * ((h ξ : ℝ) - d * ν) ^ 2) ≤ 3 * (d : ℝ) / 4 ∧
    (∑ ξ, Q d M ξ * |(h ξ : ℝ) - d * ν|) ≤ sqrt (3 * (d : ℝ)) / 2 := by
  dsimp only
  classical
  let h : (Fin d → Bool) → ℕ := fun ξ => ∑ i, (ξ i).toNat
  let ν : ℝ := M / (2 * M + d)
  let η : ℝ := d / (2 * M + d)
  let p : ℝ := (1 + (-1 : ℝ) ^ M * η ^ d) / 2
  let w : (Fin d → Bool) → ℝ := fun ξ => ν ^ h ξ * (1 - ν) ^ (d - h ξ)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hMd : (d : ℝ) ≤ M := by exact_mod_cast (by omega : d ≤ M)
  have hden : (0 : ℝ) < 2 * M + d := by positivity
  have heta0 : 0 ≤ η := by dsimp [η]; positivity
  have heta1 : η ≤ 1 / 7 := by
    dsimp [η]
    rw [div_le_iff₀ hden]
    have hh : (3 : ℝ) * d ≤ M := by exact_mod_cast hM
    linarith
  have hpow : η ^ d ≤ 1 / 7 := by
    calc
      η ^ d ≤ η ^ 1 := pow_le_pow_of_le_one heta0 (by linarith) (by omega)
      _ = η := pow_one _
      _ ≤ 1 / 7 := heta1
  have hsign : |(-1 : ℝ) ^ M| = 1 := by simp
  have hp : 1 / 3 ≤ p := by
    have habs : |(-1 : ℝ) ^ M * η ^ d| ≤ 1 / 7 := by
      rw [abs_mul, hsign, one_mul, abs_of_nonneg (pow_nonneg heta0 _)]
      exact hpow
    have hlo := (abs_le.mp habs).1
    dsimp [p]
    linarith
  have hp0 : p ≠ 0 := by linarith
  have hgen (a b : ℝ) :
      (∑ ξ : Fin d → Bool, a ^ h ξ * b ^ (d - h ξ)) = (a + b) ^ d := by
    have hcomp (ξ : Fin d → Bool) : (∑ i : Fin d, ((1 : ℕ) - (ξ i).toNat)) = d - h ξ := by
      rw [sum_tsub_distrib]
      · simp [h]
      · intro i _; cases ξ i <;> simp
    have hprod (ξ : Fin d → Bool) :
        (∏ i, if ξ i then a else b) = a ^ h ξ * b ^ (d - h ξ) := by
      calc
        (∏ i, if ξ i then a else b) =
            ∏ i, a ^ (ξ i).toNat * b ^ (1 - (ξ i).toNat) := by
          apply prod_congr rfl
          intro i _; cases ξ i <;> simp
        _ = (∏ i, a ^ (ξ i).toNat) * ∏ i, b ^ (1 - (ξ i).toNat) := prod_mul_distrib
        _ = a ^ h ξ * b ^ (d - h ξ) := by
          rw [prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, hcomp]
    calc
      _ = ∑ ξ : Fin d → Bool, ∏ i, if ξ i then a else b := by
        apply sum_congr rfl; intro ξ _; exact (hprod ξ).symm
      _ = ∏ _ : Fin d, ∑ j : Bool, if j then a else b := by
        symm
        simpa only [Fintype.piFinset_univ] using
          (prod_univ_sum (fun _ : Fin d => (univ : Finset Bool))
            (fun (_ : Fin d) (j : Bool) => if j then a else b))
      _ = (a + b) ^ d := by simp
  have hnorm : (∑ ξ, w ξ) = 1 := by
    simpa [w] using hgen ν (1 - ν)
  have hpgf (z : ℝ) : (∑ ξ, w ξ * z ^ h ξ) = (ν * z + (1 - ν)) ^ d := by
    have hh := hgen (ν * z) (1 - ν)
    simp_rw [mul_pow] at hh
    convert hh using 1
    apply sum_congr rfl
    intro ξ _
    dsimp [w]
    ring
  have hfirst (z : ℝ) :
      (∑ ξ, w ξ * (h ξ : ℝ) * z ^ (h ξ - 1)) =
        d * (ν * z + (1 - ν)) ^ (d - 1) * ν := by
    have hl : HasDerivAt (fun t : ℝ => ∑ ξ, w ξ * t ^ h ξ)
        (∑ ξ, w ξ * (h ξ : ℝ) * z ^ (h ξ - 1)) z := by
      simpa only [mul_assoc] using HasDerivAt.fun_sum (u := univ)
        (fun ξ _ => (hasDerivAt_pow (h ξ) z).const_mul (w ξ))
    have heq : (fun t : ℝ => ∑ ξ, w ξ * t ^ h ξ) =
        (fun t => (ν * t + (1 - ν)) ^ d) := funext hpgf
    rw [heq] at hl
    have hr := (((hasDerivAt_id z).const_mul ν).add_const (1 - ν)).pow d
    simpa only [mul_one, id_eq] using hl.unique hr
  have hsecond (z : ℝ) :
      (∑ ξ, w ξ * (h ξ : ℝ) * (h ξ - 1 : ℕ) * z ^ (h ξ - 2)) =
        (d : ℝ) * (d - 1 : ℕ) * (ν * z + (1 - ν)) ^ (d - 2) * ν ^ 2 := by
    have hl : HasDerivAt (fun t : ℝ => ∑ ξ, w ξ * (h ξ : ℝ) * t ^ (h ξ - 1))
        (∑ ξ, w ξ * (h ξ : ℝ) * (h ξ - 1 : ℕ) * z ^ (h ξ - 2)) z := by
      simpa only [mul_assoc, Nat.sub_sub, show (1 : ℕ) + 1 = 2 from rfl] using
        HasDerivAt.fun_sum (u := univ)
          (fun ξ _ => (hasDerivAt_pow (h ξ - 1) z).const_mul (w ξ * (h ξ : ℝ)))
    have heq : (fun t : ℝ => ∑ ξ, w ξ * (h ξ : ℝ) * t ^ (h ξ - 1)) =
        (fun t => (d : ℝ) * (ν * t + (1 - ν)) ^ (d - 1) * ν) := funext hfirst
    rw [heq] at hl
    have hr := (((((hasDerivAt_id z).const_mul ν).add_const (1 - ν)).pow
      (d - 1)).const_mul (d : ℝ)).mul_const ν
    have hh := hl.unique hr
    rw [Nat.sub_sub] at hh
    simp only [id_eq, mul_one, show (1 : ℕ) + 1 = 2 from rfl] at hh
    convert hh using 1; ring
  have hmean : (∑ ξ, w ξ * (h ξ : ℝ)) = d * ν := by
    simpa using hfirst 1
  have hfac : (∑ ξ, w ξ * (h ξ : ℝ) * (h ξ - 1 : ℕ)) =
      (d : ℝ) * (d - 1) * ν ^ 2 := by
    simpa [Nat.cast_sub (by omega : 1 ≤ d)] using hsecond 1
  have hmoment : (∑ ξ, w ξ * ((h ξ : ℝ) - d * ν) ^ 2) =
      (d : ℝ) * ν * (1 - ν) := by
    have hf (ξ : Fin d → Bool) :
        w ξ * ((h ξ : ℝ) - d * ν) ^ 2 =
          w ξ * (h ξ : ℝ) * (h ξ - 1 : ℕ) +
          (1 - 2 * d * ν) * (w ξ * (h ξ : ℝ)) + (d * ν) ^ 2 * w ξ := by
      by_cases hh : h ξ = 0
      · simp [hh]; ring
      · rw [Nat.cast_sub (by omega : 1 ≤ h ξ)]
        push_cast
        ring
    simp_rw [hf]
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hfac, hmean, hnorm]
    ring
  have hchar : (∑ ξ, (-1 : ℝ) ^ h ξ * w ξ) = η ^ d := by
    have heta : 1 - 2 * ν = η := by
      dsimp [ν, η]; field_simp; ring
    have hh := hgen (-ν) (1 - ν)
    simp_rw [neg_pow ν, mul_assoc] at hh
    change (∑ ξ, (-1 : ℝ) ^ h ξ * (ν ^ h ξ * (1 - ν) ^ (d - h ξ))) = η ^ d
    rw [hh]
    congr 1
    linarith [heta]
  have hind (ξ : Fin d → Bool) :
      (if h ξ % 2 = M % 2 then w ξ else 0) =
        (w ξ + (-1 : ℝ) ^ M * ((-1 : ℝ) ^ h ξ * w ξ)) / 2 := by
    rw [neg_one_pow_eq_pow_mod_two (R := ℝ) M,
      neg_one_pow_eq_pow_mod_two (R := ℝ) (h ξ)]
    have hm : M % 2 = 0 ∨ M % 2 = 1 := by omega
    have hh : h ξ % 2 = 0 ∨ h ξ % 2 = 1 := by omega
    rcases hm with hm | hm <;> rcases hh with hh | hh <;>
      simp [hm, hh]
  have hevent : (∑ ξ, if h ξ % 2 = M % 2 then w ξ else 0) = p := by
    simp_rw [hind]
    rw [← sum_div, sum_add_distrib, ← mul_sum, hnorm, hchar]
  have hQnorm : (∑ ξ, Q d M ξ) = 1 := by
    calc
      (∑ ξ, Q d M ξ) =
          (∑ ξ, if h ξ % 2 = M % 2 then w ξ else 0) / p := by
        rw [sum_div]
        apply sum_congr rfl
        intro ξ _
        change (if h ξ % 2 = M % 2 then w ξ / p else 0) = _
        split <;> simp_all
      _ = 1 := by rw [hevent, div_self hp0]
  have hν0 : 0 ≤ ν := by dsimp [ν]; positivity
  have hν1 : ν ≤ 1 := by
    dsimp [ν]
    rw [div_le_iff₀ hden]
    linarith
  have hw0 (ξ : Fin d → Bool) : 0 ≤ w ξ := by
    dsimp [w]
    exact mul_nonneg (pow_nonneg hν0 _) (pow_nonneg (sub_nonneg.mpr hν1) _)
  have hQ (ξ : Fin d → Bool) :
      Q d M ξ = if h ξ % 2 = M % 2 then w ξ / p else 0 := rfl
  have hQ0 (ξ : Fin d → Bool) : 0 ≤ Q d M ξ := by
    rw [hQ]
    split
    · exact div_nonneg (hw0 ξ) (by linarith)
    · exact le_rfl
  have hcm : (∑ ξ, Q d M ξ * ((h ξ : ℝ) - d * ν) ^ 2) ≤
      (∑ ξ, w ξ * ((h ξ : ℝ) - d * ν) ^ 2) / p := by
    rw [sum_div]
    apply sum_le_sum
    intro ξ _
    rw [hQ]
    split
    · simp only [div_mul_eq_mul_div]
      exact le_rfl
    · simp only [zero_mul]
      exact div_nonneg (mul_nonneg (hw0 ξ) (sq_nonneg _)) (by linarith)
  have hV0 : 0 ≤ (d : ℝ) * ν * (1 - ν) := by positivity
  have hcm_bound : (∑ ξ, Q d M ξ * ((h ξ : ℝ) - d * ν) ^ 2) ≤
      3 * (d : ℝ) / 4 := by
    calc
      _ ≤ ((d : ℝ) * ν * (1 - ν)) / p := by simpa only [hmoment] using hcm
      _ ≤ 3 * ((d : ℝ) * ν * (1 - ν)) := by
        rw [div_le_iff₀ (by linarith : 0 < p)]
        nlinarith [mul_nonneg hV0 (sub_nonneg.mpr hp)]
      _ ≤ 3 * (d : ℝ) / 4 := by
        have hvar : ν * (1 - ν) ≤ 1 / 4 := by nlinarith [sq_nonneg (ν - 1 / 2)]
        nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr hvar)]
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul
    (univ : Finset (Fin d → Bool))
    (f := fun ξ => Q d M ξ)
    (g := fun ξ => Q d M ξ * ((h ξ : ℝ) - d * ν) ^ 2)
    (r := fun ξ => Q d M ξ * |(h ξ : ℝ) - d * ν|)
    (fun ξ _ => hQ0 ξ)
    (fun ξ _ => mul_nonneg (hQ0 ξ) (sq_nonneg _))
    (by intro ξ _; rw [mul_pow, sq_abs]; ring_nf; exact le_rfl)
  rw [hQnorm, one_mul] at hcs
  have habs_bound : (∑ ξ, Q d M ξ * |(h ξ : ℝ) - d * ν|) ≤
      sqrt (3 * (d : ℝ)) / 2 := by
    have hs := sq_sqrt (by positivity : 0 ≤ 3 * (d : ℝ))
    have hs0 := sqrt_nonneg (3 * (d : ℝ))
    nlinarith
  exact ⟨hQnorm, hp, hcm_bound, habs_bound⟩

end D5.S3.TotalVariation.ParityCompositionKernel
