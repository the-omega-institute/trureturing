/- GID: D5/S1/Recurrence/Algebraic/HannaA158119Parity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA158119Parity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The original factorial-product series and its normalized reversion quotient. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
import D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Ring.Int.Parity

open PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Algebraic.HannaA158119Parity

noncomputable def summand (n : ℕ) : PowerSeries ℤ :=
  C (n.factorial : ℤ) * X ^ n *
    ∏ k ∈ Finset.range n, invOfUnit (1 + C (2 * (k + 1) : ℤ) * X) 1

/-- Each coefficient of the original infinite OGF is a finite sum. -/
noncomputable def F : PowerSeries ℤ :=
  mk fun d => ∑ n ∈ Finset.range (d + 1), coeff d (summand n)

private theorem F_zero : constantCoeff F = 1 := by
  simp [F, ← coeff_zero_eq_constantCoeff, summand]

private theorem linear_unit : IsUnit (coeff 1 (X * F)) := by
  simpa [coeff_zero_eq_constantCoeff, F_zero] using (isUnit_one : IsUnit (1 : ℤ))

noncomputable def Q : PowerSeries ℤ := (X * F).substInvOfIsUnit linear_unit

/-- The inverse equation gives this normalized quotient without dividing by a nonunit. -/
noncomputable def B : PowerSeries ℤ := F.subst Q

noncomputable def a (m : ℕ) : ℕ := (coeff (2 * m) B).natAbs

def claim : Prop := ∀ m : ℕ, Odd (a m) ↔ m = 0 ∨ ∃ j : ℕ, m = 2 ^ j

private theorem Q_zero : constantCoeff Q = 0 := by simp [Q]

private theorem inverse_equation : (X * F).subst Q = X :=
  subst_substInvOfIsUnit_right _ (by simp) linear_unit

theorem quotient_equation : B * Q = X := by
  have h := inverse_equation
  rw [subst_mul (.of_constantCoeff_zero Q_zero), subst_X (.of_constantCoeff_zero Q_zero)] at h
  simpa [B, mul_comm] using h

private theorem summand_mod_two (n : ℕ) :
    (summand n).map (Int.castRingHom (ZMod 2)) =
      if n = 0 then 1 else if n = 1 then X else 0 := by
  classical
  let hom := Int.castRingHom (ZMod 2)
  have hi (k : ℕ) :
      (invOfUnit (1 + C (2 * (k + 1) : ℤ) * X) 1).map hom = 1 := by
    rw [D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime.map_inverse hom _ (by simp)]
    simp [hom]
  rcases n with _ | n
  · simp [summand]
  rcases n with _ | n
  · simpa [summand, hom] using hi 0
  · have hd : 2 ∣ (n + 2).factorial := Nat.dvd_factorial (by omega) (by omega)
    have hz : ((n + 2).factorial : ZMod 2) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    simp [summand, hz, hom]

private theorem F_mod_two : F.map (Int.castRingHom (ZMod 2)) = 1 + X := by
  classical
  ext d
  simp only [coeff_map, F, coeff_mk, map_sum]
  simp_rw [← coeff_map, summand_mod_two]
  rcases d with _ | d
  · simp
  · simp [Finset.sum_ite_eq', Finset.mem_range]

end D5.S1.Recurrence.Algebraic.HannaA158119Parity
