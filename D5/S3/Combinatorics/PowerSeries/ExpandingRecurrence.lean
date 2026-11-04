/- GID: D5/S3/Combinatorics/PowerSeries/ExpandingRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/ExpandingRecurrence
   mirror-E: none(waiver:formal-expanding-series-recurrence)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Expand]
   utility: none
   digest: A positive-degree expanding formal recurrence has only the zero homogeneous solution. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.Linarith

/-! Coefficient induction proves uniqueness without analytic convergence or characteristic bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PowerSeries.ExpandingRecurrence

/-- Every coefficient of a homogeneous expanding recurrence vanishes over any commutative ring. -/
theorem eq_zero_of_mul_eq_X_expand {R : Type*} [CommRing R]
    (B D K : PowerSeries R) (d : ℕ) (hd : d ≠ 0)
    (hB : PowerSeries.constantCoeff B = 1)
    (hrec : B * D = PowerSeries.X * K * PowerSeries.expand d hd D) : D = 0 := by
  classical
  have hcoeff (n : ℕ) : PowerSeries.coeff n D = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hleft : PowerSeries.coeff n (B * D) = PowerSeries.coeff n D := by
        rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
        · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hB, one_mul]
        · intro p hp hne
          have he := Finset.mem_antidiagonal.mp hp
          have hlt : p.2 < n := by
            have hx : p.1 ≠ 0 := by
              intro hz
              apply hne
              exact Prod.ext hz (by omega)
            omega
          rw [ih p.2 hlt, mul_zero]
        · intro hn
          exact False.elim (hn (by simp))
      have hright : PowerSeries.coeff n
          (PowerSeries.X * K * PowerSeries.expand d hd D) = 0 := by
        rw [mul_assoc]
        cases n with
        | zero => simp
        | succ n =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul]
          apply Finset.sum_eq_zero
          intro p hp
          have he := Finset.mem_antidiagonal.mp hp
          have hterm : PowerSeries.coeff p.2 (PowerSeries.expand d hd D) = 0 := by
            by_cases hdiv : d ∣ p.2
            · obtain ⟨j, hj⟩ := hdiv
              rw [hj, PowerSeries.coeff_expand_mul]
              apply ih
              have hdpos : 1 ≤ d := by omega
              have hbound : j ≤ d * j := by nlinarith
              omega
            · exact PowerSeries.coeff_expand_of_not_dvd d hd D hdiv
          rw [hterm, mul_zero]
      have he := congrArg (PowerSeries.coeff n) hrec
      rwa [hleft, hright] at he
  ext n
  simpa only [map_zero] using hcoeff n

end D5.S3.Combinatorics.PowerSeries.ExpandingRecurrence
