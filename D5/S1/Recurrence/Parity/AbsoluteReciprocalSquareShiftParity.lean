/- GID: D5/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/AbsoluteReciprocalSquareShiftParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A cubic shift and exact binomial division prove Hanna's A384267 parity. -/

import D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity
import D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity

open PowerSeries
open D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity (absSeries)

namespace D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity

private def Agree (n : ℕ) (F G : PowerSeries ℤ) : Prop :=
  ∀ i < n, coeff i F = coeff i G

private theorem agree_iff (n : ℕ) (F G : PowerSeries ℤ) :
    Agree n F G ↔ (X : PowerSeries ℤ) ^ n ∣ F - G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {F G : PowerSeries ℤ}
    (h : Agree n F G) (k : ℕ) : Agree n (F ^ k) (G ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow F G k))

private theorem agree_inv {n : ℕ} {F G : PowerSeries ℤ}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    Agree n (invOfUnit F 1) (invOfUnit G 1) := by
  have hFI := mul_invOfUnit F 1 (by simpa using hF)
  have hGI := mul_invOfUnit G 1 (by simpa using hG)
  apply (agree_iff _ _ _).mpr
  have hd := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h)
    (-(invOfUnit F 1 * invOfUnit G 1))
  convert hd using 1
  linear_combination invOfUnit G 1 * hFI - invOfUnit F 1 * hGI

private noncomputable def step (F : PowerSeries ℤ) : PowerSeries ℤ :=
  absSeries (1 + X * invOfUnit (F ^ 2) 1)

private theorem step_constant (F : PowerSeries ℤ) : constantCoeff (step F) = 1 := by
  simp [step, absSeries]

private theorem step_agree {n : ℕ} {F G : PowerSeries ℤ}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    Agree (n + 1) (step F) (step G) := by
  have hi := agree_inv (by simp [hF]) (by simp [hG]) (agree_pow h 2)
  intro i hindex
  cases i with
  | zero => simp only [coeff_zero_eq_constantCoeff, step_constant]
  | succ i =>
    simp only [step, absSeries, coeff_mk, map_add, coeff_one,
      Nat.succ_ne_zero, if_false, zero_add, coeff_succ_X_mul]
    rw [hi i (by omega)]

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => step (approximation n)

private theorem approximation_constant (n : ℕ) : constantCoeff (approximation n) = 1 := by
  cases n with
  | zero => simp [approximation]
  | succ n => exact step_constant _

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree n (approximation n) (approximation m) := by
  induction n generalizing m with
  | zero => intro i hi; omega
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      exact step_agree (approximation_constant n) (approximation_constant m) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (n : ℕ) : Agree n generatingSeries (approximation n) := by
  intro i hi
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : i + 1 ≤ n) i (by omega)

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries = absSeries (1 + X * invOfUnit (generatingSeries ^ 2) 1) := by
  have h0 : constantCoeff generatingSeries = 1 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_constant]
  refine ⟨h0, ?_⟩
  ext i
  exact (generating_agree (i + 2) i (by omega)).trans
    (step_agree h0 (approximation_constant (i + 1))
      (generating_agree (i + 1)) i (by omega)).symm

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B = absSeries (1 + X * invOfUnit (B ^ 2) 1)) : B = generatingSeries := by
  have h : ∀ n, Agree n B generatingSeries := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      have hs := step_agree h0 generating_equation.1 ih
      simpa only [step, ← hB, ← generating_equation.2] using hs
  ext i
  exact h (i + 1) i (by omega)

private theorem map_abs (F : PowerSeries ℤ) :
    (absSeries F).map (Int.castRingHom (ZMod 2)) = F.map (Int.castRingHom (ZMod 2)) := by
  ext n
  simp [coeff_map, absSeries, ZMod.intCast_abs_mod_two]

private theorem reduced_cubic :
    (generatingSeries.map (Int.castRingHom (ZMod 2))) ^ 3 =
      (generatingSeries.map (Int.castRingHom (ZMod 2))) ^ 2 + X := by
  let hom := Int.castRingHom (ZMod 2)
  let F := generatingSeries.map hom
  let I := (invOfUnit (generatingSeries ^ 2) 1).map hom
  have hE : F = 1 + X * I := by
    simpa only [map_abs, map_add, map_one, map_mul, map_X, hom] using
      congrArg (PowerSeries.map hom) generating_equation.2
  have hI : F ^ 2 * I = 1 := by
    have hi := mul_invOfUnit (generatingSeries ^ 2) 1
      (by simp [generating_equation.1])
    simpa only [map_mul, map_pow, map_one] using
      congrArg (PowerSeries.map hom) hi
  change F ^ 3 = F ^ 2 + X
  calc
    F ^ 3 = F ^ 2 * (1 + X * I) := by rw [← hE]; ring
    _ = F ^ 2 + X * (F ^ 2 * I) := by ring
    _ = F ^ 2 + X := by rw [hI, mul_one]

private theorem ternary_reduced_equation :
    StripThreeTernaryCatalanParity.generatingSeries.map (Int.castRingHom (ZMod 2)) =
      1 + X * (StripThreeTernaryCatalanParity.generatingSeries.map
        (Int.castRingHom (ZMod 2))) ^ 3 := by
  have hm (F : PowerSeries ℤ) :
      (StripThreeTernaryCatalanParity.strip3Series F).map (Int.castRingHom (ZMod 2)) =
        F.map (Int.castRingHom (ZMod 2)) := by
    ext n
    simpa only [coeff_map, StripThreeTernaryCatalanParity.strip3Series, coeff_mk,
      Int.coe_castRingHom] using StripThreeTernaryCatalanParity.strip3_mod_two (coeff n F)
  simpa only [hm, map_add, map_one, map_mul, map_X, map_pow] using
    congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
      StripThreeTernaryCatalanParity.generating_equation.2

-- The cubic difference factors through a unit when both roots have constant term zero.
private theorem cubic_unique (U V : PowerSeries (ZMod 2))
    (hU0 : constantCoeff U = 0) (hV0 : constantCoeff V = 0)
    (hU : U = X + U ^ 3) (hV : V = X + V ^ 3) : U = V := by
  have hu : IsUnit (1 - (U ^ 2 + U * V + V ^ 2)) := by
    rw [isUnit_iff_constantCoeff]
    simp [hU0, hV0]
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  linear_combination hU - hV

set_option maxHeartbeats 800000 in
theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) =
    1 + X * expand 2 (by decide)
      (StripThreeTernaryCatalanParity.generatingSeries.map (Int.castRingHom (ZMod 2))) := by
  let F := generatingSeries.map (Int.castRingHom (ZMod 2))
  let T := StripThreeTernaryCatalanParity.generatingSeries.map (Int.castRingHom (ZMod 2))
  let E := expand 2 (by decide) T
  have hF0 : constantCoeff F = 1 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [F, coeff_map, coeff_zero_eq_constantCoeff, generating_equation.1]
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (CharTwo.two_eq_zero (R := ZMod 2))
  have hU : F + 1 = X + (F + 1) ^ 3 := by
    have hc : F ^ 3 = F ^ 2 + X := reduced_cubic
    linear_combination -hc - (2 * F ^ 2 + F + X) * htwo
  have hE : E = 1 + X ^ 2 * E ^ 3 := by
    have he := congrArg (expand (R := ZMod 2) 2 (by decide)) ternary_reduced_equation
    simpa only [map_add, map_one, map_mul, expand_X, map_pow] using
      he
  have hV : X * E = X + (X * E) ^ 3 := by
    calc
      X * E = X * (1 + X ^ 2 * E ^ 3) := by rw [← hE]
      _ = X + (X * E) ^ 3 := by ring
  have he := cubic_unique (F + 1) (X * E)
    (by simp [hF0, CharTwo.add_self_eq_zero]) (by simp) hU hV
  change F = 1 + X * E
  linear_combination he - htwo

theorem a_zero : a 0 = 1 := by
  calc
    a 0 = coeff 0 generatingSeries := (coeff_mk 0 a).symm
    _ = constantCoeff generatingSeries := congrFun coeff_zero_eq_constantCoeff _
    _ = 1 := generating_equation.1

private theorem coprime (n : ℕ) (hn : 0 < n) : Nat.Coprime (3 * n - 1) n := by
  apply Nat.coprime_of_dvd'
  intro k _ hk hkn
  have hmul : k ∣ 3 * n := dvd_mul_of_dvd_right hkn 3
  have hone : k ∣ 1 := by
    convert Nat.dvd_sub hmul hk using 1
    omega
  exact hone

private theorem balance (n : ℕ) (hn : 0 < n) :
    (3 * n - 1) * Nat.choose (3 * n - 2) (n - 1) =
      Nat.choose (3 * n - 1) n * n := by
  simpa only [show 3 * n - 2 + 1 = 3 * n - 1 by omega,
    show n - 1 + 1 = n by omega] using
      Nat.add_one_mul_choose_eq (3 * n - 2) (n - 1)

theorem ternary_dvd (n : ℕ) (hn : 0 < n) :
    3 * n - 1 ∣ Nat.choose (3 * n - 1) n := by
  apply (coprime n hn).dvd_of_dvd_mul_right
  rw [← balance n hn]
  exact dvd_mul_right _ _

private theorem quotient_balance (n : ℕ) (hn : 0 < n) :
    n * (Nat.choose (3 * n - 1) n / (3 * n - 1)) =
      Nat.choose (3 * n - 2) (n - 1) := by
  apply Nat.mul_left_cancel (by omega : 0 < 3 * n - 1)
  calc
    (3 * n - 1) * (n * (Nat.choose (3 * n - 1) n / (3 * n - 1))) =
        n * ((3 * n - 1) * (Nat.choose (3 * n - 1) n / (3 * n - 1))) := by ring
    _ = n * Nat.choose (3 * n - 1) n := by rw [Nat.mul_div_cancel' (ternary_dvd n hn)]
    _ = (3 * n - 1) * Nat.choose (3 * n - 2) (n - 1) := by
      rw [balance n hn, Nat.mul_comm]

theorem ternary_div_odd (r : ℕ) :
    Nat.choose (6 * r + 2) (2 * r + 1) / (6 * r + 2) =
      Nat.choose (6 * r + 1) (2 * r) / (2 * r + 1) := by
  apply Nat.eq_div_of_mul_eq_right (by omega)
  simpa only [show 3 * (2 * r + 1) - 1 = 6 * r + 2 by omega,
    show 3 * (2 * r + 1) - 2 = 6 * r + 1 by omega,
    show 2 * r + 1 - 1 = 2 * r by omega] using quotient_balance (2 * r + 1) (by omega)

private theorem lucas_two (n k : ℕ) :
    (Nat.choose n k : ZMod 2) =
      (Nat.choose (n % 2) (k % 2) : ZMod 2) * Nat.choose (n / 2) (k / 2) := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ 2).mpr
    (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2))
  simpa only [Nat.cast_mul] using h

private theorem odd_even_lucas (n k : ℕ) :
    (Nat.choose (2 * n + 1) (2 * k) : ZMod 2) = Nat.choose n k := by
  rw [lucas_two]
  simp [show (2 * n + 1) / 2 = n by omega]

private theorem quotient_odd_parity (r : ℕ) :
    (Nat.choose (6 * r + 2) (2 * r + 1) / (6 * r + 2) : ℕ) =
      (Nat.choose (3 * r) r : ZMod 2) := by
  have hb := quotient_balance (2 * r + 1) (by omega)
  have hc := congrArg (Nat.cast : ℕ → ZMod 2) hb
  simp only [show 3 * (2 * r + 1) - 1 = 6 * r + 2 by omega,
    show 3 * (2 * r + 1) - 2 = 6 * r + 1 by omega,
    show 2 * r + 1 - 1 = 2 * r by omega] at hc
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add, one_mul] at hc
  exact hc.trans (by simpa only [show 2 * (3 * r) + 1 = 6 * r + 1 by omega] using
    (odd_even_lucas (3 * r) r))

private theorem even_choose (r : ℕ) (hr : 0 < r) :
    (Nat.choose (3 * r - 1) r : ZMod 2) = 0 := by
  have hb : Nat.choose (3 * r - 1) r * (3 * r) = Nat.choose (3 * r) r * (2 * r) := by
    simpa only [show 3 * r - 1 + 1 = 3 * r by omega,
      show 3 * r - r = 2 * r by omega] using Nat.choose_mul_succ_eq (3 * r - 1) r
  have he : 3 * Nat.choose (3 * r - 1) r = 2 * Nat.choose (3 * r) r := by
    nlinarith
  have hc := congrArg (Nat.cast : ℕ → ZMod 2) he
  simpa only [Nat.cast_mul, Nat.cast_ofNat, show (3 : ZMod 2) = 1 by decide,
    show (2 : ZMod 2) = 0 by decide, one_mul, zero_mul] using hc

private theorem quotient_even_parity (r : ℕ) (hr : 0 < r) :
    (Nat.choose (6 * r - 1) (2 * r) / (6 * r - 1) : ℕ) = (0 : ZMod 2) := by
  have hd := ternary_dvd (2 * r) (by omega)
  rw [show 3 * (2 * r) - 1 = 6 * r - 1 by omega] at hd
  have he := congrArg (Nat.cast : ℕ → ZMod 2) (Nat.mul_div_cancel' hd)
  have ho : ((6 * r - 1 : ℕ) : ZMod 2) = 1 := by
    rw [show 6 * r - 1 = 2 * (3 * r - 1) + 1 by omega]
    simp [show (2 : ZMod 2) = 0 by decide]
  rw [Nat.cast_mul, ho, one_mul] at he
  calc
    _ = (Nat.choose (6 * r - 1) (2 * r) : ZMod 2) := he
    _ = (Nat.choose (3 * r - 1) r : ZMod 2) := by
      rw [show 6 * r - 1 = 2 * (3 * r - 1) + 1 by omega, odd_even_lucas]
    _ = 0 := even_choose r hr

theorem ternary_div_even (r : ℕ) (hr : 0 < r) :
    2 ∣ Nat.choose (6 * r - 1) (2 * r) / (6 * r - 1) :=
  (ZMod.natCast_eq_zero_iff _ 2).mp (quotient_even_parity r hr)

private theorem coefficient_shift (m : ℕ) :
    (a (m + 1) : ZMod 2) =
      if 2 ∣ m then (Nat.choose (3 * (m / 2)) (m / 2) : ZMod 2) else 0 := by
  have hc := congrArg (coeff (m + 1)) mod_two_identity
  rw [map_add, coeff_one, if_neg (by omega : m + 1 ≠ 0), zero_add,
    coeff_succ_X_mul, coeff_expand, StripThreeTernaryCatalanParity.mod_two_identity,
    coeff_mk] at hc
  simpa only [coeff_map, generatingSeries, coeff_mk, Int.coe_castRingHom] using hc

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) :
    a n % 2 = ((Nat.choose (3 * n - 1) n / (3 * n - 1) : ℕ) : ℤ) % 2 := by
  apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mp
  rw [Int.cast_natCast]
  rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · have hr : 0 < r := by omega
    rw [show r + r = 2 * r by omega, show 3 * (2 * r) - 1 = 6 * r - 1 by omega]
    have ha : (a (2 * r) : ZMod 2) = 0 := by
      rw [show 2 * r = (2 * r - 1) + 1 by omega, coefficient_shift,
        if_neg (by omega : ¬ 2 ∣ 2 * r - 1)]
    exact ha.trans ((ZMod.natCast_eq_zero_iff _ 2).mpr (ternary_div_even r hr)).symm
  · rw [show 3 * (2 * r + 1) - 1 = 6 * r + 2 by omega,
      coefficient_shift, if_pos (dvd_mul_right 2 r), Nat.mul_div_right _ (by decide)]
    exact (quotient_odd_parity r).symm

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_identity
#print axioms a_zero
#print axioms ternary_dvd
#print axioms ternary_div_odd
#print axioms ternary_div_even
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.AbsoluteReciprocalSquareShiftParity
