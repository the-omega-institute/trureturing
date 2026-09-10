/- GID: D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Unit inversion, ternary reduction and binary descent prove Hanna's A380708. -/

import D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity
import D5.S1.Recurrence.Parity.FibbinarySquareSubstitutionParity
import D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity

open PowerSeries
open D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity (absSeries)
open D5.S1.Recurrence.Parity.FibbinarySquareSubstitutionParity (Fibbinary)

namespace D5.S1.Recurrence.Residue.AbsoluteReciprocalSquareFibbinaryParity

private def Agree (n : ℕ) (F G : PowerSeries ℤ) : Prop :=
  ∀ i < n, coeff i F = coeff i G

private theorem agree_iff (n : ℕ) (F G : PowerSeries ℤ) :
    Agree n F G ↔ (X : PowerSeries ℤ) ^ n ∣ F - G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {F G : PowerSeries ℤ}
    (h : Agree n F G) (k : ℕ) : Agree n (F ^ k) (G ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow F G k))

private theorem agree_abs {n : ℕ} {F G : PowerSeries ℤ} (h : Agree n F G) :
    Agree n (absSeries F) (absSeries G) := by
  intro i hi
  simp only [absSeries, coeff_mk, h i hi]

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
  1 + X * (absSeries (invOfUnit F 1)) ^ 2

private theorem step_constant (F : PowerSeries ℤ) : constantCoeff (step F) = 1 := by
  simp [step]

private theorem step_agree {n : ℕ} {F G : PowerSeries ℤ}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    Agree (n + 1) (step F) (step G) := by
  have hm := (agree_iff _ _ _).mp (agree_pow (agree_abs (agree_inv hF hG h)) 2)
  apply (agree_iff _ _ _).mpr
  convert mul_dvd_mul_left X hm using 1
  · ring
  · dsimp [step]; ring

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
    generatingSeries = 1 + X * (absSeries (invOfUnit generatingSeries 1)) ^ 2 := by
  have h0 : constantCoeff generatingSeries = 1 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_constant]
  refine ⟨h0, ?_⟩
  ext i
  exact (generating_agree (i + 2) i (by omega)).trans
    (step_agree h0 (approximation_constant (i + 1))
      (generating_agree (i + 1)) i (by omega)).symm

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B = 1 + X * (absSeries (invOfUnit B 1)) ^ 2) : B = generatingSeries := by
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

private noncomputable def reduced : PowerSeries (ZMod 2) :=
  generatingSeries.map (Int.castRingHom (ZMod 2))

private noncomputable def reciprocal : PowerSeries (ZMod 2) :=
  (invOfUnit generatingSeries 1).map (Int.castRingHom (ZMod 2))

private theorem reciprocal_mul : reciprocal * reduced = 1 := by
  simpa only [reciprocal, reduced, map_mul, map_one] using
    congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
      (invOfUnit_mul generatingSeries 1 generating_equation.1)

private theorem reduced_equation : reduced = 1 + X * reciprocal ^ 2 := by
  simpa only [reduced, reciprocal, map_add, map_one, map_mul, map_X, map_pow, map_abs]
    using congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) generating_equation.2

-- The inverse changes the reciprocal square equation into the ternary equation.
private theorem reciprocal_equation : reciprocal = 1 + X * reciprocal ^ 3 := by
  have hi : 1 = reciprocal + X * reciprocal ^ 3 := by
    calc
      1 = reciprocal * reduced := reciprocal_mul.symm
      _ = reciprocal + X * reciprocal ^ 3 := by rw [reduced_equation]; ring
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (CharTwo.two_eq_zero (R := ZMod 2))
  linear_combination -hi - (X * reciprocal ^ 3) * htwo

private theorem ternary_equation :
    (D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.generatingSeries.map
      (Int.castRingHom (ZMod 2))) = 1 + X *
    (D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.generatingSeries.map
      (Int.castRingHom (ZMod 2))) ^ 3 := by
  have hs (F : PowerSeries ℤ) :
      (D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.strip3Series F).map
        (Int.castRingHom (ZMod 2)) = F.map (Int.castRingHom (ZMod 2)) := by
    ext n
    simpa only [coeff_map,
      D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.strip3Series,
      coeff_mk, Int.coe_castRingHom] using
      D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.strip3_mod_two (coeff n F)
  simpa only [hs, map_add, map_one, map_mul, map_X, map_pow] using
    congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
      D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.generating_equation.2

private theorem ternary_unique (F G : PowerSeries (ZMod 2))
    (hF : F = 1 + X * F ^ 3) (hG : G = 1 + X * G ^ 3) : F = G := by
  let U := 1 - X * (F ^ 2 + F * G + G ^ 2)
  have hu : IsUnit U := by
    rw [isUnit_iff_constantCoeff]
    simp [U]
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  dsimp [U]
  linear_combination hF - hG

theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) =
    1 + X * expand 2 (by decide)
      (D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.generatingSeries.map
        (Int.castRingHom (ZMod 2))) := by
  have ht := ternary_unique _ _ reciprocal_equation ternary_equation
  have hf := MvPowerSeries.map_frobenius_expand (f := reciprocal) 2 (by decide)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at hf
  change expand 2 (by decide) reciprocal = reciprocal ^ 2 at hf
  change reduced = _
  rw [reduced_equation, ← hf, ht]

private theorem fibbinary_bits (n : ℕ) :
    Fibbinary n ↔ ∀ i, (n.testBit i && n.testBit (i + 1)) = false := by
  constructor
  · intro h i
    have he := congrArg (fun k => Nat.testBit k i) h
    simpa only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.zero_testBit,
      Nat.add_comm 1 i] using he
  · intro h
    apply Nat.zero_of_testBit_eq_false
    intro i
    simpa only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.add_comm 1 i] using h i

private theorem fibbinary_bit (b : Bool) (n : ℕ) :
    Fibbinary (Nat.bit b n) ↔ (b && n.testBit 0) = false ∧ Fibbinary n := by
  rw [fibbinary_bits, fibbinary_bits]
  constructor
  · intro h
    refine ⟨?_, fun i => ?_⟩
    · simpa only [Nat.testBit_bit_zero, Nat.testBit_bit_succ] using h 0
    · simpa only [Nat.testBit_bit_succ] using h (i + 1)
  · rintro ⟨hz, hs⟩ i
    cases i with
    | zero => simpa only [Nat.testBit_bit_zero, Nat.testBit_bit_succ] using hz
    | succ i => simpa only [Nat.testBit_bit_succ] using hs i

private theorem fibbinary_even (n : ℕ) : Fibbinary (2 * n) ↔ Fibbinary n := by
  simpa only [Nat.bit_false, two_mul, Bool.false_and, true_and] using fibbinary_bit false n

private theorem fibbinary_one (n : ℕ) : Fibbinary (4 * n + 1) ↔ Fibbinary n := by
  have he : 4 * n + 1 = Nat.bit true (Nat.bit false n) := by simp [Nat.bit]; omega
  simp only [he, fibbinary_bit, Nat.testBit_bit_zero, Bool.true_and, Bool.false_and,
    true_and]

private theorem fibbinary_three (n : ℕ) : ¬ Fibbinary (4 * n + 3) := by
  have he : 4 * n + 3 = Nat.bit true (Nat.bit true n) := by simp [Nat.bit]; omega
  rw [he, fibbinary_bit, Nat.testBit_bit_zero]
  simp

theorem choose_three_odd_iff (f : ℕ) :
    (Nat.choose (3 * f) f : ZMod 2) = 1 ↔ Fibbinary f := by
  induction f using Nat.strong_induction_on with
  | h f ih =>
    cases f with
    | zero => simp [Fibbinary]
    | succ n =>
      by_cases he : (n + 1) % 2 = 0
      · have hi : n + 1 = 2 * ((n + 1) / 2) := by omega
        rw [hi, D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.choose_three_lucas
          ((n + 1) / 2) |>.1, fibbinary_even]
        exact ih _ (by omega)
      · by_cases hp : (n / 2) % 2 = 0
        · have hi : n + 1 = 4 * (n / 2 / 2) + 1 := by omega
          rw [hi, D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.choose_three_lucas
            (n / 2 / 2) |>.2.1, fibbinary_one]
          exact ih _ (by omega)
        · have hi : n + 1 = 4 * (n / 4) + 3 := by omega
          rw [hi, D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.choose_three_lucas
            (n / 4) |>.2.2]
          exact iff_of_false (by decide) (fibbinary_three _)

theorem hanna_conjecture (n : ℕ) (hn : 0 < n) :
    Odd (a n) ↔ ∃ f : ℕ, Fibbinary f ∧ n = 2 * f + 1 := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hc := congrArg (coeff (m + 1)) mod_two_identity
  rw [map_add, coeff_one, if_neg (by omega : m + 1 ≠ 0), zero_add,
    coeff_succ_X_mul, expand_apply 2 (by decide),
    coeff_subst_X_pow (by decide : 2 ≠ 0),
    D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.mod_two_identity] at hc
  simp only [coeff_map, generatingSeries, coeff_mk, Int.coe_castRingHom,
    Algebra.algebraMap_self_apply] at hc
  rw [hc]
  by_cases he : 2 ∣ m
  · rw [if_pos he, choose_three_odd_iff]
    constructor
    · intro hf
      exact ⟨m / 2, hf, by omega⟩
    · rintro ⟨f, hf, heq⟩
      have : m / 2 = f := by omega
      simpa only [this] using hf
  · rw [if_neg he]
    constructor
    · intro h
      exact False.elim (zero_ne_one h)
    · rintro ⟨f, _, heq⟩
      exact False.elim (he ⟨f, by omega⟩)

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_identity
#print axioms choose_three_odd_iff
#print axioms hanna_conjecture

end D5.S1.Recurrence.Residue.AbsoluteReciprocalSquareFibbinaryParity
