/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointSpectral
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointSpectral
   mirror-E: none(waiver:strict-depth-transfer-spectral-remainder)
   anchors: [mathlib/module/Mathlib.RingTheory.Henselian]
   utility: none
   digest: The unit transfer branch is exact below the block-dependent determinant depth. -/

import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-! Strict coefficient control for powers of a two-by-two series transfer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointSpectral

open PowerSeries
open scoped Matrix

/-- A trace-one, monomial-determinant transfer has one fixed unit spectral
branch controlling every entry at each actual depth below D*K. -/
theorem transfer_spectral_remainder
    (U : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ)) (D : ℕ) (hD : 0 < D)
    (htr : constantCoeff (Matrix.trace U) = 1)
    (hdet : U.det = X ^ D) :
    ∃ a : PowerSeries ℚ, constantCoeff a = 1 ∧
      ∃ E : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ),
        ∀ K h : ℕ, h < D * K → ∀ i j : Fin 2,
          coeff h ((U ^ K) i j) = coeff h (a ^ K * E i j) := by
  classical
  let I : Ideal (PowerSeries ℚ) := Ideal.span {PowerSeries.X}
  let f : Polynomial (PowerSeries ℚ) :=
    Polynomial.X ^ 2 - Polynomial.C (Matrix.trace U) * Polynomial.X +
      Polynomial.C (X ^ D)
  have fm : f.Monic := by
    dsimp [f]
    apply Polynomial.Monic.add_of_left
    · apply Polynomial.Monic.sub_of_left
      · exact Polynomial.monic_X_pow 2
      · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)
    · rw [Polynomial.degree_sub_eq_left_of_degree_lt
        (lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num))]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  have fi : f.eval 1 ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp [f, htr, ne_of_gt hD]
  have fd : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    apply IsUnit.map
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hc : constantCoeff (f.derivative.eval 1) = 1 := by
      norm_num [f, Polynomial.derivative_pow, htr, map_ofNat]
    rw [hc]
    exact isUnit_one
  obtain ⟨a, ha, haI⟩ := HenselianRing.is_henselian f fm 1 fi fd
  have ha0 : constantCoeff a = 1 := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, map_one] at haI
    exact sub_eq_zero.mp haI
  have root : a ^ 2 - Matrix.trace U * a + X ^ D = 0 := by
    simpa [f, Polynomial.IsRoot] using ha
  let V := PowerSeries.invOfUnit a (1 : ℚˣ)
  have hV : a * V = 1 := PowerSeries.mul_invOfUnit a 1 (by simpa using ha0)
  let b : PowerSeries ℚ := X ^ D * V
  have hab : a * b = X ^ D := by
    calc
      a * b = X ^ D * (a * V) := by dsimp [b]; ring
      _ = X ^ D := by rw [hV, mul_one]
  have trace_eq : Matrix.trace U = a + b := by
    dsimp only [b]
    linear_combination -V * root + (a - Matrix.trace U) * hV
  have hb0 : constantCoeff b = 0 := by simp [b, ne_of_gt hD]
  let W := PowerSeries.invOfUnit (a - b) (1 : ℚˣ)
  have hW : (a - b) * W = 1 :=
    PowerSeries.mul_invOfUnit (a - b) 1 (by simp [ha0, hb0])
  let E : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ) :=
    fun i j => (U i j - b * (1 : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ)) i j) * W
  let F : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ) := 1 - E
  have power : ∀ K : ℕ, ∀ i j : Fin 2,
      (U ^ K) i j = a ^ K * E i j + b ^ K * F i j := by
    intro K
    induction K using Nat.twoStepInduction with
    | zero =>
      intro i j
      simp only [pow_zero, one_mul, F, Matrix.sub_apply]
      ring
    | one =>
      intro i j
      simp only [pow_one]
      change U i j = a * E i j + b * ((1 : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ)) i j - E i j)
      dsimp only [E]
      linear_combination -(U i j - b * (1 : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ)) i j) * hW
    | more K ih0 ih1 =>
      intro i j
      rw [D5.S0.Observation.MatrixTracePowerSum.pow_add_two,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
        smul_eq_mul, ih1, ih0, trace_eq, hdet, ← hab]
      simp only [pow_succ]
      ring
  refine ⟨a, ha0, E, ?_⟩
  intro K h hh i j
  have small : coeff h (b ^ K * F i j) = 0 := by
    have factor : b ^ K * F i j = X ^ (D * K) * (V ^ K * F i j) := by
      dsimp only [b]
      rw [mul_pow, ← pow_mul]
      ring
    rw [factor, coeff_X_pow_mul', if_neg (by omega)]
  rw [power, map_add, small, add_zero]

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointSpectral
