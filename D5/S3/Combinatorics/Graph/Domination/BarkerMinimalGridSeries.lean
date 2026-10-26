/- GID: D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries
   mirror-E: none(waiver:internal-stage-a)
   anchors: []
   utility: none
   digest: The full literal Barker numerator follows from the exact quotient annihilator and initial convolutions. -/

import D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridPartition
import Mathlib.RingTheory.PowerSeries.Inverse
import Batteries.Tactic.OpenPrivate

/-! The reproduced formula is attributed to Colin Barker, OEIS A286848,
https://oeis.org/A286848, under CC-BY-SA-4.0,
https://creativecommons.org/licenses/by-sa/4.0/.
The quotient series is kept distinct from the actual-subset series until their
all-length counting correspondence is proved. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridSeries

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridQuotient
open private orbit_values from D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridQuotient

/-- The complete numerator in increasing degree order, including its leading x. -/
def numerator : Fin 49 → ℤ := ![0, 2, 3, -2, -1, 4, 10, -14, -32, -29, -2, -21, -140, -140, 126, 80, 127, 143, 695, 401, 462, 582, -8, -490, -660, -721, -960, -714, -925, 25, 206, 255, 494, 155, 443, -118, 80, -71, -172, 78, -105, 79, 7, -28, 33, -7, -4, 3, -1]

/-- Evaluation by the exact initial row of the full-state quotient. -/
def evaluate : Vector →ₗ[ℤ] ℤ where
  toFun v := ∑ i : Fin 59, BarkerMinimalGridPartition.alpha i * v i
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The scalar quotient orbit with the separately prescribed positive-width
initial value and a zero series constant. This is not a definition of actualCount. -/
def quotientCoefficient (n : ℕ) : ℤ :=
  if n = 0 then 0 else if n = 1 then 2 else evaluate (orbit (n - 2))

/-- Exact finite orbit values used only for the initial coefficient range. -/
def initialCoefficient (n : Fin 50) : ℤ :=
  if n.val = 0 then 0 else if n.val = 1 then 2 else
    evaluate (values ⟨n.val - 2, by omega⟩)

private theorem coefficient_initial (n : Fin 50) :
    quotientCoefficient n.val = initialCoefficient n := by
  unfold quotientCoefficient initialCoefficient
  split_ifs with h₀ h₁
  · rfl
  · rfl
  · congr 1
    exact orbit_values ⟨n.val - 2, by omega⟩

/-- Every initial convolution, in degrees zero through 49, equals the complete
numerator; the extra degree 49 is checked to be zero. -/
theorem initial_convolutions : ∀ m : Fin 50,
    (∑ j : Fin 49, if j.val ≤ m.val then
      denominator j * initialCoefficient ⟨m.val - j.val, by omega⟩ else 0) =
      if h : m.val < 49 then numerator ⟨m.val, h⟩ else 0 := by
  decide

/-- The denominator recurrence holds at every coefficient from degree 50 onward. -/
theorem all_later_convolutions (m : ℕ) (hm : 50 ≤ m) :
    (∑ j : Fin 49, denominator j * quotientCoefficient (m - j.val)) = 0 := by
  have h := congrArg evaluate (shifted_annihilator (m - 50))
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  have h₀ : m - j.val ≠ 0 := by omega
  have h₁ : m - j.val ≠ 1 := by omega
  have he : m - j.val - 2 = m - 50 + 48 - j.val := by omega
  simp only [quotientCoefficient, if_neg h₀, if_neg h₁, he]

/-- The quotient-orbit series over the rationals. -/
def quotientSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (quotientCoefficient n : ℚ)

/-- The full literal numerator as a formal polynomial series. -/
def P : PowerSeries ℚ := PowerSeries.mk fun n =>
  if h : n < 49 then (numerator ⟨n, h⟩ : ℚ) else 0

/-- The full literal denominator as a finite sum of monomials. -/
def Q : PowerSeries ℚ :=
  ∑ j : Fin 49, PowerSeries.C (denominator j : ℚ) * PowerSeries.X ^ j.val

private theorem coefficient_product (m : ℕ) :
    PowerSeries.coeff m (quotientSeries * Q) =
      ∑ j : Fin 49, if j.val ≤ m then
        (denominator j : ℚ) * (quotientCoefficient (m - j.val) : ℚ) else 0 := by
  simp only [Q, Finset.mul_sum, map_sum, ← mul_assoc,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C,
    quotientSeries, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp_all [mul_comm]

/-- The exact quotient series has the complete numerator, including all initial
coefficients and the leading x, after multiplication by the literal denominator. -/
theorem quotientSeries_mul_Q : quotientSeries * Q = P := by
  apply PowerSeries.ext
  intro m
  rw [coefficient_product, P, PowerSeries.coeff_mk]
  by_cases hm : m < 50
  · have hi := initial_convolutions ⟨m, hm⟩
    have hc : ∀ j : Fin 49, j.val ≤ m →
        quotientCoefficient (m - j.val) = initialCoefficient ⟨m - j.val, by omega⟩ :=
      fun j _ => coefficient_initial ⟨m - j.val, by omega⟩
    simp_rw [show ∀ j : Fin 49, (if j.val ≤ m then
      (denominator j : ℚ) * (quotientCoefficient (m - j.val) : ℚ) else 0) =
      ((if j.val ≤ m then denominator j * initialCoefficient ⟨m - j.val, by omega⟩
        else 0 : ℤ) : ℚ) from fun j => by
          by_cases hj : j.val ≤ m
          · simp only [if_pos hj, hc j hj, Int.cast_mul]
          · simp only [if_neg hj, Int.cast_zero]]
    exact_mod_cast hi
  · have hh : 50 ≤ m := by omega
    have hi := all_later_convolutions m hh
    have h49 : ¬ m < 49 := by omega
    rw [dif_neg h49]
    have hj : ∀ j : Fin 49, j.val ≤ m := fun j => by omega
    simp only [if_pos (hj _)]
    exact_mod_cast hi

/-- The constant term is one, so the literal denominator is a unit. -/
theorem Q_constant : PowerSeries.constantCoeff Q = 1 := by
  simp only [Q, map_sum, map_mul, map_pow, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X]
  decide

/-- Inverse form of the full quotient-orbit identity. The actual-subset bridge
is an independent obligation, not an assumption of this theorem. -/
theorem quotientSeries_identity : quotientSeries = P * Q⁻¹ :=
  (PowerSeries.eq_mul_inv_iff_mul_eq (by rw [Q_constant]; norm_num)).mpr quotientSeries_mul_Q

end D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridSeries
