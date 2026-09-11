/- GID: D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Quadratic power diagonals connect Hanna A397244 to Fibbinary parity. -/

import D5.S1.Recurrence.Residue.AbsoluteReciprocalSquareFibbinaryParity
import D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd

/-!
Library-search audit: the frozen AbsoluteReciprocalSquareFibbinaryParity
and StripThreeTernaryCatalanParity supply parity and the ternary equation,
but concern different integer sequences. DiagonalPowerRatioAllOdd supplies
the first-difference multiplier for powers. Pinned Mathlib supplies
coeff_subst_X_pow, map_frobenius_expand, ZMod.frobenius_zmod and unit inversion.
Searches for Lagrange inversion and a quadratic power-diagonal bridge found
no matching theorem. External search is excluded by this task's offline scope.

Proposed escape: Frobenius descent annihilates [X^n] F^(2n) for all n > 0
over ZMod 2. The cubic candidate then has zero odd-power diagonal above
degree one, so strict-prefix uniqueness identifies the two reductions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.QuadraticPowerDiagonalFibbinaryParity

open PowerSeries
open D5.S1.Recurrence.Parity.FibbinarySquareSubstitutionParity (Fibbinary)

noncomputable def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
    let P : PowerSeries ℤ := mk fun j => if _h : j < n + 2 then a j else 0
    (2 * (n + 2) - 1 : ℤ) * coeff (n + 2) (P ^ (2 * (n + 2) + 1)) -
      (2 * (n + 2) : ℤ) * coeff (n + 2) (P ^ (2 * (n + 2)))
termination_by n => n

noncomputable def generatingSeries : PowerSeries ℤ := mk a

noncomputable def strictPrefix (n : ℕ) : PowerSeries ℤ :=
  mk fun j => if j < n then a j else 0

theorem a_two : a 2 = 6 := by
  have hp : (mk fun j => if j < 2 then a j else 0 : PowerSeries ℤ) = 1 + X := by
    ext j
    rcases j with _ | _ | j
    · simp [a]
    · simp [a, coeff_one]
    · simp [coeff_one, coeff_X]
  rw [a]
  change (3 : ℤ) * coeff 2 ((mk fun j => if j < 2 then a j else 0) ^ 5) -
    4 * coeff 2 ((mk fun j => if j < 2 then a j else 0) ^ 4) = 6
  rw [hp]
  have hc (k : ℕ) : coeff 2 ((1 + X : PowerSeries ℤ) ^ k) = (Nat.choose k 2 : ℤ) := by
    rw [← Polynomial.coe_one, ← Polynomial.coe_X, ← Polynomial.coe_add,
      ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  rw [hc, hc]
  norm_num [Nat.choose]

open private diagonal_multiplier from D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd
open private mod_two_equation from D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity
open private coeff_square square_subst from D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity

private theorem recurrence (n : ℕ) (hn : 1 < n) :
    a n = (2 * (n : ℤ) - 1) * coeff n (strictPrefix n ^ (2 * n + 1)) -
      (2 * (n : ℤ)) * coeff n (strictPrefix n ^ (2 * n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [a]
  rfl

private theorem zero_coeff : coeff 0 generatingSeries = 1 := by
  simp [generatingSeries, a]

private theorem one_coeff : coeff 1 generatingSeries = 1 := by
  simp [generatingSeries, a]

theorem generating_equation : coeff 0 generatingSeries = 1 ∧
    coeff 1 generatingSeries = 1 ∧ ∀ n : ℕ, 1 < n →
      (2 * (n : ℤ)) * coeff n (generatingSeries ^ (2 * n)) =
        (2 * (n : ℤ) - 1) * coeff n (generatingSeries ^ (2 * n + 1)) := by
  refine ⟨zero_coeff, one_coeff, ?_⟩
  intro n hn
  have ha : constantCoeff generatingSeries = 1 := by
    simpa only [coeff_zero_eq_constantCoeff] using zero_coeff
  have hp : constantCoeff (strictPrefix n) = 1 := by simp [strictPrefix, a]; omega
  have hag : ∀ j < n, coeff j generatingSeries = coeff j (strictPrefix n) := by
    intro j hj
    simp [generatingSeries, strictPrefix, hj]
  have h2 := diagonal_multiplier ha hp hag (2 * n)
  have h3 := diagonal_multiplier ha hp hag (2 * n + 1)
  have hr := recurrence n hn
  simp only [generatingSeries, strictPrefix, coeff_mk, lt_self_iff_false, if_false,
    sub_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h2 h3
  dsimp only [generatingSeries, strictPrefix] at hr ⊢
  linear_combination (2 * (n : ℤ)) * h2 - (2 * (n : ℤ) - 1) * h3 + hr

private theorem equation_unique {R : Type*} [CommRing R] (A B : PowerSeries R)
    (hA0 : coeff 0 A = 1) (hB0 : coeff 0 B = 1)
    (hA1 : coeff 1 A = 1) (hB1 : coeff 1 B = 1)
    (hA : ∀ n : ℕ, 1 < n → (2 * (n : R)) * coeff n (A ^ (2 * n)) =
      (2 * (n : R) - 1) * coeff n (A ^ (2 * n + 1)))
    (hB : ∀ n : ℕ, 1 < n → (2 * (n : R)) * coeff n (B ^ (2 * n)) =
      (2 * (n : R) - 1) * coeff n (B ^ (2 * n + 1))) : A = B := by
  have hA0' : constantCoeff A = 1 := by simpa only [coeff_zero_eq_constantCoeff] using hA0
  have hB0' : constantCoeff B = 1 := by simpa only [coeff_zero_eq_constantCoeff] using hB0
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; exact hA0.trans hB0.symm
    by_cases hn1 : n = 1
    · subst n; exact hA1.trans hB1.symm
    have h2 := diagonal_multiplier hA0' hB0' ih (2 * n)
    have h3 := diagonal_multiplier hA0' hB0' ih (2 * n + 1)
    have ha := hA n (by omega)
    have hb := hB n (by omega)
    push_cast at h2 h3
    linear_combination ha - hb - (2 * (n : R)) * h2 + (2 * (n : R) - 1) * h3

theorem generating_unique (B : PowerSeries ℤ) (h0 : coeff 0 B = 1)
    (h1 : coeff 1 B = 1)
    (he : ∀ n : ℕ, 1 < n → (2 * (n : ℤ)) * coeff n (B ^ (2 * n)) =
      (2 * (n : ℤ) - 1) * coeff n (B ^ (2 * n + 1))) : B = generatingSeries :=
  equation_unique B generatingSeries h0 zero_coeff h1 one_coeff he generating_equation.2.2

/-- Frobenius descent annihilates this diagonal for every series, in every positive degree. -/
private theorem even_power_diagonal (F : PowerSeries (ZMod 2)) (n : ℕ) (hn : 0 < n) :
    coeff n (F ^ (2 * n)) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [show F ^ (2 * n) = (F ^ n) ^ 2 by rw [← pow_mul]; congr 1; omega,
      coeff_square]
    split_ifs with he
    · have hh : n = 2 * (n / 2) := by omega
      rw [hh]
      simpa using ih (n / 2) (by omega) (by omega)
    · rfl

private noncomputable def candidate : PowerSeries (ZMod 2) :=
  AbsoluteReciprocalSquareFibbinaryParity.generatingSeries.map (Int.castRingHom (ZMod 2))

private theorem candidate_cubic : candidate ^ 3 = candidate ^ 2 + X := by
  let T := Parity.StripThreeTernaryCatalanParity.generatingSeries.map
    (Int.castRingHom (ZMod 2))
  have ht : T = 1 + X * T ^ 3 := mod_two_equation
  have hb : candidate = 1 + X * T ^ 2 := by
    rw [candidate, AbsoluteReciprocalSquareFibbinaryParity.mod_two_identity,
      expand_apply]
    rw [← square_subst]
  have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (C (R := ZMod 2))
      (CharTwo.two_eq_zero (R := ZMod 2))
  have hu : candidate * T = 1 := by
    rw [hb]
    linear_combination ht + X * T ^ 3 * hz
  calc
    candidate ^ 3 = candidate ^ 2 * (1 + X * T ^ 2) := by rw [← hb]; ring
    _ = candidate ^ 2 + X * (candidate * T) ^ 2 := by ring
    _ = candidate ^ 2 + X := by rw [hu]; ring

private theorem cubic_diagonal (B : PowerSeries (ZMod 2))
    (hB : B ^ 3 = B ^ 2 + X) (n : ℕ) (hn : 1 < n) :
    coeff n (B ^ (2 * n + 1)) = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    have hp : B ^ (2 * (m + 1) + 1) = B ^ (2 * (m + 1)) + X * B ^ (2 * m) := by
      calc
        _ = B ^ 3 * B ^ (2 * m) := by rw [← pow_add]; congr 1; omega
        _ = (B ^ 2 + X) * B ^ (2 * m) := by rw [hB]
        _ = _ := by rw [add_mul, ← pow_add]; congr 2; omega
    rw [hp, map_add, coeff_succ_X_mul, even_power_diagonal B (m + 1) (by omega),
      even_power_diagonal B m (by omega), add_zero]

private theorem reduction_eq_candidate :
    generatingSeries.map (Int.castRingHom (ZMod 2)) = candidate := by
  let hom := Int.castRingHom (ZMod 2)
  apply equation_unique
  · simp [coeff_map, zero_coeff]
  · simp [candidate, coeff_map, coeff_zero_eq_constantCoeff,
      AbsoluteReciprocalSquareFibbinaryParity.generating_equation.1]
  · simp [coeff_map, one_coeff]
  · rw [candidate, AbsoluteReciprocalSquareFibbinaryParity.mod_two_identity]
    simp only [map_add, coeff_one, one_ne_zero, if_false, zero_add,
      coeff_succ_X_mul, coeff_zero_eq_constantCoeff,
      constantCoeff_expand]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      Parity.StripThreeTernaryCatalanParity.generating_equation.1, map_one]
  · intro n hn
    have h := congrArg hom (generating_equation.2.2 n hn)
    simpa only [hom, map_mul, map_sub, map_one, map_ofNat, Int.coe_castRingHom,
      Int.cast_natCast, ← map_pow, coeff_map] using h
  · intro n hn
    rw [cubic_diagonal candidate candidate_cubic n hn,
      even_power_diagonal candidate n (by omega)]
    ring

/-- The reduction of the strict-prefix sequence satisfies the cubic equation. -/
theorem mod_two_cubic :
    (generatingSeries.map (Int.castRingHom (ZMod 2))) ^ 3 =
      (generatingSeries.map (Int.castRingHom (ZMod 2))) ^ 2 + X := by
  rw [reduction_eq_candidate]
  exact candidate_cubic

/-- Equality of reductions, not equality of the two integer sequences. -/
theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) =
    1 + X * expand 2 (by decide)
      (Parity.StripThreeTernaryCatalanParity.generatingSeries.map
        (Int.castRingHom (ZMod 2))) :=
  reduction_eq_candidate.trans AbsoluteReciprocalSquareFibbinaryParity.mod_two_identity

theorem hanna_conjecture_a397244 (n : ℕ) (hn : 0 < n) :
    Odd (a n) ↔ ∃ f : ℕ, Fibbinary f ∧ n = 2 * f + 1 := by
  have hc := congrArg (coeff n) reduction_eq_candidate
  simp only [candidate, coeff_map, generatingSeries, coeff_mk,
    AbsoluteReciprocalSquareFibbinaryParity.generatingSeries, Int.coe_castRingHom] at hc
  rw [← ZMod.intCast_eq_one_iff_odd, hc, ZMod.intCast_eq_one_iff_odd]
  exact AbsoluteReciprocalSquareFibbinaryParity.hanna_conjecture n hn

#print axioms a_two
#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_cubic
#print axioms mod_two_identity
#print axioms hanna_conjecture_a397244

end D5.S1.Recurrence.Residue.QuadraticPowerDiagonalFibbinaryParity
