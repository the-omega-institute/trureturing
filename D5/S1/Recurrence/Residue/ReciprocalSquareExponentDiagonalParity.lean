/- GID: D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A binary Catalan reciprocal satisfies square-exponent diagonal equations. -/

import D5.S1.Recurrence.Residue.QuadraticPowerDiagonalFibbinaryParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.ReciprocalSquareExponentDiagonalParity

open PowerSeries
open D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
  (catalanSeries catalan_equation binary_catalan)
open private coeff_square square_subst from D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity
open private even_power_diagonal from
  D5.S1.Recurrence.Residue.QuadraticPowerDiagonalFibbinaryParity

private noncomputable def u : PowerSeries (ZMod 2) :=
  catalanSeries.map (Int.castRingHom (ZMod 2))

noncomputable def v : PowerSeries (ZMod 2) :=
  1 + catalanSeries.map (Int.castRingHom (ZMod 2))

private noncomputable def C : PowerSeries (ZMod 2) := PowerSeries.invOfUnit v 1

private theorem two_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  simpa only [map_ofNat, map_zero] using congrArg (PowerSeries.C (R := ZMod 2))
    (CharTwo.two_eq_zero (R := ZMod 2))

private theorem u_equation : u = X + u ^ 2 := by
  simpa [u] using congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
    catalan_equation.2.2

private theorem v_constant : constantCoeff v = 1 := by
  rw [v, map_add, map_one, ← coeff_zero_eq_constantCoeff, coeff_map,
    coeff_zero_eq_constantCoeff, catalan_equation.1, map_zero, add_zero]

private theorem u_mul_v : u * v = X := by
  change u * (1 + u) = X
  linear_combination u_equation + u ^ 2 * two_zero

private theorem artin_schreier : v ^ 2 = v + X ∧ constantCoeff v = 1 ∧ v * C = 1 := by
  refine ⟨?_, v_constant, PowerSeries.mul_invOfUnit v 1 v_constant⟩
  change (1 + u) ^ 2 = (1 + u) + X
  linear_combination u_equation + u ^ 2 * two_zero

private theorem v_even_part : v = v ^ 2 + X := by
  linear_combination -artin_schreier.1 - X * two_zero

private theorem X_mul_C : X * C = u := by
  rw [← u_mul_v, mul_assoc, artin_schreier.2.2, mul_one]

private theorem frobenius_diagonal (F : PowerSeries (ZMod 2)) (t : ℕ)
    (n : ℕ) (hn : 0 < n) : coeff n (F ^ (2 * n * t)) = 0 := by
  have he : F ^ (2 * n * t) = (F ^ t) ^ (2 * n) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [he]
  exact even_power_diagonal (F ^ t) n hn

private theorem coeff_two_mul (Q : PowerSeries (ZMod 2)) (m : ℕ) (hm : 0 < m) :
    coeff (2 * m) (v * Q ^ 2) = coeff m (v * Q) := by
  have he : v * Q ^ 2 = (v * Q) ^ 2 + X * Q ^ 2 := by
    calc
      v * Q ^ 2 = (v ^ 2 + X) * Q ^ 2 := congrArg (fun s => s * Q ^ 2) v_even_part
      _ = _ := by ring
  rw [he, map_add, coeff_square]
  have hs : 2 * m = (2 * m - 1) + 1 := by omega
  have hz : coeff (2 * m) (X * Q ^ 2) = 0 := by
    rw [hs, coeff_succ_X_mul, coeff_square, if_neg (by omega)]
  simp [hz]

/-- The residual diagonal vanishes by square extraction in both parity classes. -/
private theorem residual_diagonal (n : ℕ) (hn : 1 < n) :
    coeff (n - 1) (v ^ (n ^ 2 - 2)) = 0 := by
  by_cases he : n % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hm : 0 < m := by omega
    have hm2 : 1 ≤ m ^ 2 := by nlinarith
    have hp : (2 * m) ^ 2 - 2 = (2 * m ^ 2 - 1) * 2 := by
      have : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
      omega
    rw [hp, pow_mul, coeff_square, if_neg (by omega)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hm : 0 < m := by omega
    have hm2 : 1 ≤ m ^ 2 := by nlinarith
    have hp : (2 * m + 1) ^ 2 - 2 = (2 * m ^ 2 + 2 * m - 1) * 2 + 1 := by
      have : (2 * m + 1) ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by ring
      omega
    have hi : 2 * m + 1 - 1 = 2 * m := by omega
    rw [hi, hp, pow_succ', pow_mul, coeff_two_mul _ m hm, ← pow_succ']
    have hq : 2 * m ^ 2 + 2 * m - 1 + 1 = 2 * m * (m + 1) := by
      have : 2 * m * (m + 1) = 2 * m ^ 2 + 2 * m := by ring
      omega
    rw [hq]
    exact frobenius_diagonal v (m + 1) m hm

theorem v_diagonal (n : ℕ) (hn : 1 < n) :
    coeff n (v ^ (n ^ 2)) = coeff n (v ^ (n ^ 2 - 1)) := by
  have hn2 : 2 ≤ n ^ 2 := by nlinarith
  have hp : v ^ (n ^ 2) + v ^ (n ^ 2 - 1) = X * v ^ (n ^ 2 - 2) := by
    calc
      _ = v ^ (n ^ 2 - 1) * (v + 1) := by
        rw [mul_add, mul_one, ← pow_succ]
        rw [show n ^ 2 - 1 + 1 = n ^ 2 by omega]
      _ = v ^ (n ^ 2 - 1) * u := by
        have hv : v + 1 = u := by
          change 1 + u + 1 = u
          linear_combination two_zero
        rw [hv]
      _ = v ^ (n ^ 2 - 2) * (u * v) := by
        rw [show n ^ 2 - 1 = (n ^ 2 - 2) + 1 by omega, pow_succ]
        ring
      _ = _ := by rw [u_mul_v, mul_comm]
  apply CharTwo.add_eq_zero.mp
  rw [← map_add, hp, show n = (n - 1) + 1 by omega, coeff_succ_X_mul]
  simpa only [show n - 1 + 1 = n by omega] using residual_diagonal n hn

private theorem coeff_candidate (n : ℕ) : coeff n C = 1 ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  rw [← coeff_succ_X_mul n C, X_mul_C]
  exact binary_catalan (n + 1)

open private diagonal_multiplier from D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd

noncomputable def r : ℕ → ℤ
  | 0 => 1
  | 1 => -1
  | n + 2 =>
    let P : PowerSeries ℤ := mk fun j => if _h : j < n + 2 then r j else 0
    coeff (n + 2) (P ^ ((n + 2) ^ 2 - 1)) - coeff (n + 2) (P ^ ((n + 2) ^ 2))
termination_by n => n

noncomputable def reciprocalSeries : PowerSeries ℤ := mk r

private noncomputable def strictPrefix (n : ℕ) : PowerSeries ℤ :=
  mk fun j => if j < n then r j else 0

private theorem recurrence (n : ℕ) (hn : 1 < n) :
    r n = coeff n (strictPrefix n ^ (n ^ 2 - 1)) -
      coeff n (strictPrefix n ^ (n ^ 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [r]
  rfl

noncomputable def generatingSeries : PowerSeries ℤ :=
  PowerSeries.invOfUnit reciprocalSeries 1

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

private theorem reciprocal_zero : coeff 0 reciprocalSeries = 1 := by
  simp [reciprocalSeries, r]

private theorem reciprocal_one : coeff 1 reciprocalSeries = -1 := by
  simp [reciprocalSeries, r]

/-- The inverse pair satisfies the defining square-exponent diagonal relation. -/
theorem generating_equation : reciprocalSeries * generatingSeries = 1 ∧
    a 0 = 1 ∧ a 1 = 1 ∧ ∀ n : ℕ, 1 < n →
      coeff n (reciprocalSeries ^ (n ^ 2)) =
        coeff n (reciprocalSeries ^ (n ^ 2 - 1)) := by
  have h0 : constantCoeff reciprocalSeries = 1 := by
    simpa only [coeff_zero_eq_constantCoeff] using reciprocal_zero
  have hinv : reciprocalSeries * generatingSeries = 1 :=
    PowerSeries.mul_invOfUnit reciprocalSeries 1 h0
  have ha0 : a 0 = 1 := by
    simp [a, generatingSeries, coeff_zero_eq_constantCoeff, constantCoeff_invOfUnit]
  refine ⟨hinv, ha0, ?_, ?_⟩
  · have h := congrArg (coeff 1) hinv
    rw [coeff_one_mul, h0, ← coeff_zero_eq_constantCoeff, reciprocal_one] at h
    change (-1) * a 0 + a 1 * 1 = coeff 1 (1 : PowerSeries ℤ) at h
    simp only [coeff_one, one_ne_zero, if_false, mul_one] at h
    linear_combination h + ha0
  · intro n hn
    have hp : constantCoeff (strictPrefix n) = 1 := by
      simp [strictPrefix, r]; omega
    have hag : ∀ j < n, coeff j reciprocalSeries = coeff j (strictPrefix n) := by
      intro j hj
      simp [reciprocalSeries, strictPrefix, hj]
    have h2 := diagonal_multiplier h0 hp hag (n ^ 2)
    have h3 := diagonal_multiplier h0 hp hag (n ^ 2 - 1)
    have hr := recurrence n hn
    have hn2 : 1 ≤ n ^ 2 := by nlinarith
    rw [Nat.cast_sub hn2, Nat.cast_one] at h3
    simp only [reciprocalSeries, strictPrefix, coeff_mk, lt_self_iff_false, if_false,
      sub_zero] at h2 h3
    dsimp only [reciprocalSeries, strictPrefix] at hr ⊢
    linear_combination h2 - h3 + hr

private theorem equation_unique {R : Type*} [CommRing R] (A B : PowerSeries R)
    (hA0 : coeff 0 A = 1) (hB0 : coeff 0 B = 1)
    (hA1 : coeff 1 A = -1) (hB1 : coeff 1 B = -1)
    (hA : ∀ n : ℕ, 1 < n → coeff n (A ^ (n ^ 2)) = coeff n (A ^ (n ^ 2 - 1)))
    (hB : ∀ n : ℕ, 1 < n → coeff n (B ^ (n ^ 2)) = coeff n (B ^ (n ^ 2 - 1))) :
    A = B := by
  have hA0' : constantCoeff A = 1 := by simpa only [coeff_zero_eq_constantCoeff] using hA0
  have hB0' : constantCoeff B = 1 := by simpa only [coeff_zero_eq_constantCoeff] using hB0
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; exact hA0.trans hB0.symm
    by_cases hn1 : n = 1
    · subst n; exact hA1.trans hB1.symm
    have h2 := diagonal_multiplier hA0' hB0' ih (n ^ 2)
    have h3 := diagonal_multiplier hA0' hB0' ih (n ^ 2 - 1)
    have ha := hA n (by omega)
    have hb := hB n (by omega)
    have hn2 : 1 ≤ n ^ 2 := by
      have : 1 < n := by omega
      nlinarith
    rw [Nat.cast_sub hn2, Nat.cast_one] at h3
    linear_combination ha - hb - h2 + h3

/-- Both members of an inverse pair are determined by the reciprocal diagonal equation. -/
theorem generating_unique (B A : PowerSeries ℤ) (h0 : coeff 0 B = 1)
    (h1 : coeff 1 B = -1)
    (he : ∀ n : ℕ, 1 < n → coeff n (B ^ (n ^ 2)) = coeff n (B ^ (n ^ 2 - 1)))
    (hinv : B * A = 1) : B = reciprocalSeries ∧ A = generatingSeries := by
  have hb : B = reciprocalSeries :=
    equation_unique B reciprocalSeries h0 reciprocal_zero h1 reciprocal_one he
      generating_equation.2.2.2
  refine ⟨hb, ?_⟩
  rw [hb] at hinv
  calc
    A = (reciprocalSeries * generatingSeries) * A := by rw [generating_equation.1, one_mul]
    _ = generatingSeries * (reciprocalSeries * A) := by ring
    _ = generatingSeries := by rw [hinv, mul_one]

/-- Reduction of the integer reciprocal is the binary Catalan candidate. -/
theorem mod_two_identity : reciprocalSeries.map (Int.castRingHom (ZMod 2)) = v := by
  apply equation_unique
  · simp [coeff_map, reciprocal_zero]
  · simpa only [coeff_zero_eq_constantCoeff] using artin_schreier.2.1
  · simp [coeff_map, reciprocal_one]
  · have hv : coeff 1 (catalanSeries.map (Int.castRingHom (ZMod 2))) = 1 :=
      (binary_catalan 1).2 ⟨0, by simp⟩
    simp [v, hv, CharTwo.neg_eq]
  · intro n hn
    have h := congrArg (Int.castRingHom (ZMod 2)) (generating_equation.2.2.2 n hn)
    simpa only [← map_pow, coeff_map] using h
  · exact v_diagonal

/-- Hanna's parity conjecture for the coefficients of the defining inverse series. -/
theorem hanna_conjecture_a397356 (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  have hi : v * generatingSeries.map (Int.castRingHom (ZMod 2)) = 1 := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) generating_equation.1
    simpa only [map_mul, map_one, mod_two_identity] using h
  have hc : generatingSeries.map (Int.castRingHom (ZMod 2)) = C := by
    calc
      _ = (v * C) * generatingSeries.map (Int.castRingHom (ZMod 2)) := by
        rw [artin_schreier.2.2, one_mul]
      _ = C * (v * generatingSeries.map (Int.castRingHom (ZMod 2))) := by ring
      _ = C := by rw [hi, mul_one]
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hn : (a n : ZMod 2) = coeff n C := by
    simpa only [coeff_map, Int.coe_castRingHom, a] using congrArg (coeff n) hc
  rw [hn]
  exact coeff_candidate n

#print axioms v_diagonal
#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_identity
#print axioms hanna_conjecture_a397356

end D5.S1.Recurrence.Residue.ReciprocalSquareExponentDiagonalParity
