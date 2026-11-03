/- GID: D5/S3/Constants/Irrationality/LogNaturalIrrationality
   generality: I
   mirror-B: D5/B/S3/Constants/Irrationality/LogNaturalIrrationality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The natural logarithm of every natural number at least two is irrational. -/

import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Irrationality of logarithms of natural numbers

The analytic input is Mathlib's public
`LindemannWeierstrass.exp_polynomial_approx`, specialized to `X - C a`.
Clearing a rational denominator makes its small error an integer. A sufficiently
large prime then forces a divisibility contradiction. Rationality of `log n`
would make the exponential of a positive natural number an integer.

This uses the analytical approximation, not a transcendence or linear
independence conclusion of the Lindemann--Weierstrass theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Constants.Irrationality.LogNaturalIrrationality

open Polynomial Filter
open scoped Topology

/-- The exponential of a positive natural number is irrational. The prime
approximation error, after clearing the denominator, is an integer of norm less
than one. Its vanishing contradicts the supplier's nondivisibility clause. -/
private theorem exp_pos_nat_irrational (a : ℕ) (ha : 0 < a) :
    Irrational (Real.exp (a : ℝ)) := by
  rintro ⟨q, hq⟩
  have hd : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hmul : Real.exp (a : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
    apply (eq_div_iff hd).mp
    simpa only [Rat.cast_def] using hq.symm
  have hnum_pos : 0 < q.num := by
    have hpos : (0 : ℝ) < (q.num : ℝ) := by
      rw [← hmul]
      exact mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr q.pos)
    exact_mod_cast hpos
  have hmulC : Complex.exp (a : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by
    have h := congrArg Complex.ofReal hmul
    simpa only [Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.ofReal_natCast, Complex.ofReal_intCast] using h

  let f : ℤ[X] := X - C (a : ℤ)
  have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hf : f.eval 0 ≠ 0 := by
    simpa [f] using neg_ne_zero.mpr haZ
  have hf_ne : f ≠ 0 := by
    intro h
    apply hf
    simp [h]
  have hroot : (a : ℂ) ∈ f.aroots ℂ := by
    apply Polynomial.mem_aroots.mpr
    exact ⟨hf_ne, by simp [f]⟩
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf

  -- This limit theorem allows arbitrary real c, including negative c.
  have hlim : Tendsto
      (fun p : ℕ => (q.den : ℝ) * c ^ p / ((p - 1).factorial : ℝ))
      atTop (𝓝 0) :=
    FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop (q.den : ℝ) c 1
  have hsmall : ∀ᶠ p : ℕ in atTop,
      (q.den : ℝ) * c ^ p / ((p - 1).factorial : ℝ) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  obtain ⟨p, hp, hprime⟩ :=
    Nat.exists_infinite_primes (max N (max a q.num.natAbs) + 1)
  have hpN : N ≤ p := by omega
  have hpa : a < p := by omega
  have hpu : q.num.natAbs < p := by omega
  have hpf : (f.eval 0).natAbs < p := by simpa [f] using hpa
  obtain ⟨z, hz, g, _hdegree, happrox⟩ := hc p hpf hprime
  have hb := happrox hroot
  let gval : ℤ := g.eval (a : ℤ)
  have heval : aeval (a : ℂ) g = (gval : ℂ) := by
    simpa [gval] using
      (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (a : ℤ) g)

  let k : ℤ := z * q.num - (p : ℤ) * gval * (q.den : ℤ)
  have hidentity : (k : ℂ) = (q.den : ℂ) *
      (z • Complex.exp (a : ℂ) - p • aeval (a : ℂ) g) := by
    simp only [k, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      zsmul_eq_mul, nsmul_eq_mul, heval]
    rw [← hmulC]
    ring
  have hbound : ‖(k : ℂ)‖ < 1 := by
    calc
      ‖(k : ℂ)‖ = (q.den : ℝ) *
          ‖z • Complex.exp (a : ℂ) - p • aeval (a : ℂ) g‖ := by
        rw [hidentity, norm_mul, Complex.norm_natCast]
      _ ≤ (q.den : ℝ) * (c ^ p / ((p - 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = (q.den : ℝ) * c ^ p / ((p - 1).factorial : ℝ) := by ring
      _ < 1 := hN p hpN
  have hkzero : k = 0 := by
    have habsR : |(k : ℝ)| < 1 := by
      simpa only [Complex.norm_intCast] using hbound
    have habsZ : |k| < 1 := by exact_mod_cast habsR
    exact Int.abs_lt_one_iff.mp habsZ
  have hdiv : (p : ℤ) ∣ z * q.num := by
    have heq : z * q.num = (p : ℤ) * (gval * (q.den : ℤ)) := by
      have h := sub_eq_zero.mp hkzero
      simpa only [mul_assoc] using h
    rw [heq]
    exact dvd_mul_right _ _
  have hdivNat : p ∣ z.natAbs * q.num.natAbs := by
    simpa only [Int.natAbs_mul] using Int.natCast_dvd.mp hdiv
  rcases hprime.dvd_mul.mp hdivNat with hz' | hu'
  · exact hz (Int.natCast_dvd.mpr hz')
  · have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hnum_pos.ne') hu'
    omega

/-- The natural logarithm of every natural number at least two is irrational. -/
theorem irrational_log_natCast (n : ℕ) (hn : 2 ≤ n) :
    Irrational (Real.log (n : ℝ)) := by
  rintro ⟨q, hq⟩
  have hn_one : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn_one
  have hq_pos : (0 : ℚ) < q := by
    have hpos : (0 : ℝ) < (q : ℝ) := by
      rw [hq]
      exact Real.log_pos hn_one
    exact_mod_cast hpos
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
  let a : ℕ := q.num.natAbs
  have ha : 0 < a := Int.natAbs_pos.mpr hnum_pos.ne'
  have hnumCast : (a : ℝ) = (q.num : ℝ) := by
    have hZ : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnum_pos.le
    change (q.num.natAbs : ℝ) = (q.num : ℝ)
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hZ
  have hd : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hmul : Real.log (n : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
    apply (eq_div_iff hd).mp
    simpa only [Rat.cast_def] using hq.symm
  have ha_eq : (a : ℝ) = (q.den : ℝ) * Real.log (n : ℝ) := by
    rw [hnumCast, ← hmul]
    ring
  have hexp : Real.exp (a : ℝ) = ((n ^ q.den : ℕ) : ℝ) := by
    rw [ha_eq, Real.exp_nat_mul, Real.exp_log hn_pos, Nat.cast_pow]
  apply exp_pos_nat_irrational a ha
  refine ⟨((n ^ q.den : ℕ) : ℚ), ?_⟩
  simpa only [Rat.cast_natCast] using hexp.symm

end D5.S3.Constants.Irrationality.LogNaturalIrrationality
