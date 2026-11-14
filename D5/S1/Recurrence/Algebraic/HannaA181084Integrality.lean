/- GID: D5/S1/Recurrence/Algebraic/HannaA181084Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA181084Integrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer coefficients of Hanna's OEIS A181084 formal exponential. -/

import D5.S1.Recurrence.Algebraic.HannaA181070Integrality

namespace D5.S1.Recurrence.Algebraic.HannaA181084Integrality

open Finset PowerSeries
open D5.S1.Recurrence.Algebraic.HannaA181070Integrality

/-- The degreewise finite form of the literal logarithm in OEIS A181084. -/
noncomputable def logarithm : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (n + 1),
        if 0 < n ∧ n + k = m then
          ((n.choose k : ℕ) : ℚ) ^ (n + k + 1) / (n : ℚ)
        else 0

/-- The formal exponential over the rationals. -/
noncomputable def A : PowerSeries ℚ :=
  PowerSeries.subst logarithm (PowerSeries.exp ℚ)

/-- Ordinary coefficient integrality in every natural degree, including zero. -/
def claim : Prop :=
  ∀ m : ℕ, ∃ z : ℤ, PowerSeries.coeff m A = (z : ℚ)

private def F84 (n k : ℕ) : ℕ := (n.choose k) ^ (n + k + 1)

theorem result : claim := by
  have hl : logarithm = L F84 := by
    ext m
    simpa only [logarithm, coeff_mk, F84, Nat.cast_pow] using
      literalBounded F84
        (fun n k h => by simp [F84, Nat.choose_eq_zero_of_lt h]) m
  unfold claim A
  rw [hl]
  apply integralGeneric F84
  · exact divPower (fun n k => n.choose k) (fun n k => n + k)
      (fun n k _ => binomDiv n k)
  · intro p hp n k _
    have hdiv : n ∣ (n + k) * n.choose k := by
      rw [add_mul]
      exact dvd_add (dvd_mul_right n (n.choose k)) (binomDiv n k)
    have hc := (binomCong p n k hp).pow (p * (n + k) + 1)
    have he := variableExponent p n (n + k) (n.choose k) hp hdiv
    have h := Nat.modEq_iff_dvd.mp (hc.trans he).symm
    simpa only [F84, mul_add, Nat.cast_pow] using h

end D5.S1.Recurrence.Algebraic.HannaA181084Integrality
