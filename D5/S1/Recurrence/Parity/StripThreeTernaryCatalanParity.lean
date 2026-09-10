/- GID: D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/StripThreeTernaryCatalanParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Strip-three contraction, Lucas descent and exact division prove Hanna A378578. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Lucas

open PowerSeries

namespace D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity

def strip3 (m : ℤ) : ℤ := m / 3 ^ padicValInt 3 m

theorem strip3_mod_two (m : ℤ) : (strip3 m : ZMod 2) = m := by
  have he : (3 : ℤ) ^ padicValInt 3 m * strip3 m = m :=
    Int.mul_ediv_cancel' (padicValInt_dvd m)
  have hc := congrArg (Int.castRingHom (ZMod 2)) he
  simpa only [map_mul, map_pow, Int.coe_castRingHom, Int.cast_ofNat,
    show (3 : ZMod 2) = 1 by decide, one_pow, one_mul] using hc

noncomputable def strip3Series (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun n => strip3 (coeff n F))

private def Agree (n : ℕ) (F G : PowerSeries ℤ) : Prop :=
  ∀ i < n, coeff i F = coeff i G

private theorem agree_iff (n : ℕ) (F G : PowerSeries ℤ) :
    Agree n F G ↔ (X : PowerSeries ℤ) ^ n ∣ F - G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {F G : PowerSeries ℤ}
    (h : Agree n F G) (k : ℕ) : Agree n (F ^ k) (G ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow F G k))

private noncomputable def step (F : PowerSeries ℤ) : PowerSeries ℤ :=
  strip3Series (1 + X * F ^ 3)

private theorem step_constant (F : PowerSeries ℤ) : constantCoeff (step F) = 1 := by
  simp [step, strip3Series, strip3]

private theorem step_agree {n : ℕ} {F G : PowerSeries ℤ} (h : Agree n F G) :
    Agree (n + 1) (step F) (step G) := by
  intro i hi
  cases i with
  | zero => simp only [coeff_zero_eq_constantCoeff, step_constant]
  | succ i =>
    simp only [step, strip3Series, coeff_mk, map_add, coeff_one,
      Nat.succ_ne_zero, if_false, zero_add, coeff_succ_X_mul]
    rw [agree_pow h 3 i (by omega)]

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
    | succ m => exact step_agree (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (n : ℕ) : Agree n generatingSeries (approximation n) := by
  intro i hi
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : i + 1 ≤ n) i (by omega)

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries = strip3Series (1 + X * generatingSeries ^ 3) := by
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_constant]
  · ext i
    exact (generating_agree (i + 2) i (by omega)).trans
      (step_agree (generating_agree (i + 1)) i (by omega)).symm

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B = strip3Series (1 + X * B ^ 3)) : B = generatingSeries := by
  have h : ∀ n, Agree n B generatingSeries := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      cases n with
      | zero =>
        intro i hi
        have : i = 0 := by omega
        simpa only [this, coeff_zero_eq_constantCoeff, generating_equation.1] using h0
      | succ n =>
        simpa only [step, ← hB, ← generating_equation.2] using step_agree ih
  ext i
  exact h (i + 1) i (by omega)

private theorem map_strip3 (F : PowerSeries ℤ) :
    (strip3Series F).map (Int.castRingHom (ZMod 2)) =
      F.map (Int.castRingHom (ZMod 2)) := by
  ext n
  simpa only [coeff_map, strip3Series, coeff_mk, Int.coe_castRingHom] using
    strip3_mod_two (coeff n F)

private theorem mod_two_equation :
    generatingSeries.map (Int.castRingHom (ZMod 2)) =
      1 + X * (generatingSeries.map (Int.castRingHom (ZMod 2))) ^ 3 := by
  simpa only [map_strip3, map_add, map_one, map_mul, map_X, map_pow] using
    congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) generating_equation.2

private theorem lucas_two (n k : ℕ) :
    (Nat.choose n k : ZMod 2) =
      (Nat.choose (n % 2) (k % 2) : ZMod 2) * Nat.choose (n / 2) (k / 2) := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ 2).mpr
    (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2))
  simpa only [Nat.cast_mul] using h

theorem choose_three_lucas (r : ℕ) :
    (Nat.choose (3 * (2 * r)) (2 * r) : ZMod 2) = Nat.choose (3 * r) r ∧
    (Nat.choose (3 * (4 * r + 1)) (4 * r + 1) : ZMod 2) = Nat.choose (3 * r) r ∧
    (Nat.choose (3 * (4 * r + 3)) (4 * r + 3) : ZMod 2) = 0 := by
  have he (u v : ℕ) : (Nat.choose (2 * u) (2 * v) : ZMod 2) = Nat.choose u v := by
    rw [lucas_two]
    simp
  have ho (u v : ℕ) : (Nat.choose (2 * u + 1) (2 * v + 1) : ZMod 2) =
      Nat.choose u v := by
    rw [lucas_two]
    simp [show (2 * u + 1) / 2 = u by omega,
      show (2 * v + 1) / 2 = v by omega]
  have hm (u v : ℕ) : (Nat.choose (2 * u + 1) (2 * v) : ZMod 2) =
      Nat.choose u v := by
    rw [lucas_two]
    simp [show (2 * u + 1) / 2 = u by omega]
  have hz (u v : ℕ) : (Nat.choose (2 * u) (2 * v + 1) : ZMod 2) = 0 := by
    rw [lucas_two]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [show 3 * (2 * r) = 2 * (3 * r) by ring, he]
  · rw [show 3 * (4 * r + 1) = 2 * (2 * (3 * r) + 1) + 1 by ring,
      show 4 * r + 1 = 2 * (2 * r) + 1 by ring, ho, hm]
  · rw [show 3 * (4 * r + 3) = 2 * (2 * (3 * r + 2)) + 1 by ring,
      show 4 * r + 3 = 2 * (2 * r + 1) + 1 by ring, ho, hz]

private theorem choose_balance (n : ℕ) (hn : 0 < n) :
    Nat.choose (3 * n) n * n = Nat.choose (3 * n) (n - 1) * (2 * n + 1) := by
  simpa only [show n - 1 + 1 = n by omega,
    show 3 * n - (n - 1) = 2 * n + 1 by omega] using
      Nat.choose_succ_right_eq (3 * n) (n - 1)

private theorem choose_bound (n : ℕ) (hn : 0 < n) :
    2 * Nat.choose (3 * n) (n - 1) ≤ Nat.choose (3 * n) n := by
  have h := choose_balance n hn
  nlinarith

theorem ternary_catalan_div (n : ℕ) (hn : 0 < n) :
    Nat.choose (3 * n) n / (2 * n + 1) =
      Nat.choose (3 * n) n - 2 * Nat.choose (3 * n) (n - 1) := by
  have h := choose_balance n hn
  have hb := choose_bound n hn
  symm
  apply Nat.eq_div_of_mul_eq_right (by omega : 2 * n + 1 ≠ 0)
  have hs := Nat.sub_add_cancel hb
  nlinarith

private theorem ternary_catalan_parity (n : ℕ) :
    (Nat.choose (3 * n) n / (2 * n + 1) : ℕ) ≡
      Nat.choose (3 * n) n [MOD 2] := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [ternary_catalan_div _ (by omega)]
    have hb := choose_bound (n + 1) (by omega)
    apply (ZMod.natCast_eq_natCast_iff _ _ 2).mp
    rw [Nat.cast_sub hb, Nat.cast_mul, Nat.cast_ofNat,
      show (2 : ZMod 2) = 0 by decide, zero_mul, sub_zero]

private theorem square_subst (F : PowerSeries (ZMod 2)) :
    F ^ 2 = F.subst (X ^ 2) := by
  have he := MvPowerSeries.map_frobenius_expand (f := F) 2 (by decide)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at he
  exact he.symm.trans (PowerSeries.expand_apply 2 (by decide) F)

private theorem coeff_square (F : PowerSeries (ZMod 2)) (n : ℕ) :
    coeff n (F ^ 2) = if n % 2 = 0 then coeff (n / 2) F else 0 := by
  rw [square_subst, coeff_subst_X_pow (by decide : 2 ≠ 0)]
  simp only [Nat.dvd_iff_mod_eq_zero, Algebra.algebraMap_self_apply]

private theorem reduced_coeff (F : PowerSeries (ZMod 2)) (n : ℕ) :
    coeff (n + 1) (F ^ 2 + X * F ^ 4) =
      if (n + 1) % 2 = 0 then coeff ((n + 1) / 2) F
      else if (n / 2) % 2 = 0 then coeff (n / 2 / 2) F else 0 := by
  rw [map_add, coeff_succ_X_mul, show F ^ 4 = (F ^ 2) ^ 2 by ring,
    coeff_square, coeff_square]
  by_cases h : (n + 1) % 2 = 0
  · rw [if_pos h, if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg h, if_neg h, if_pos (by omega), zero_add, coeff_square]

private theorem reduced_equation :
    generatingSeries.map (Int.castRingHom (ZMod 2)) =
      (generatingSeries.map (Int.castRingHom (ZMod 2))) ^ 2 +
      X * (generatingSeries.map (Int.castRingHom (ZMod 2))) ^ 4 := by
  let F := generatingSeries.map (Int.castRingHom (ZMod 2))
  have he : F = 1 + X * F ^ 3 := mod_two_equation
  have hm : F ^ 2 = F + X * F ^ 4 := by
    calc
      F ^ 2 = F * (1 + X * F ^ 3) := by rw [← he]; ring
      _ = F + X * F ^ 4 := by ring
  change F = F ^ 2 + X * F ^ 4
  have hz : X * F ^ 4 + X * F ^ 4 = 0 := by
    ext n
    simp only [map_add, map_zero, CharTwo.add_self_eq_zero]
  rw [hm, add_assoc, hz, add_zero]

-- The same binary descent controls the reduced series and the Lucas coefficients.
private theorem reduced_binomial (F : PowerSeries (ZMod 2))
    (h0 : constantCoeff F = 1) (hF : F = F ^ 2 + X * F ^ 4) (n : ℕ) :
    coeff n F = (Nat.choose (3 * n) n : ZMod 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff, Nat.mul_zero,
        Nat.choose_zero_right, Nat.cast_one] using h0
    | succ n =>
      have hc := congrArg (coeff (n + 1)) hF
      rw [reduced_coeff] at hc
      rw [hc]
      by_cases he : (n + 1) % 2 = 0
      · rw [if_pos he, ih _ (by omega)]
        have hi : n + 1 = 2 * ((n + 1) / 2) := by omega
        conv_rhs => rw [hi]
        exact (choose_three_lucas _).1.symm
      · rw [if_neg he]
        by_cases hp : (n / 2) % 2 = 0
        · rw [if_pos hp, ih _ (by omega)]
          have hi : n + 1 = 4 * (n / 2 / 2) + 1 := by omega
          conv_rhs => rw [hi]
          exact (choose_three_lucas _).2.1.symm
        · rw [if_neg hp]
          have hi : n + 1 = 4 * (n / 4) + 3 := by omega
          conv_rhs => rw [hi]
          exact (choose_three_lucas _).2.2.symm

theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) =
    mk (fun n => (Nat.choose (3 * n) n : ZMod 2)) := by
  have h0 : constantCoeff (generatingSeries.map (Int.castRingHom (ZMod 2))) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_one]
  ext n
  simpa only [coeff_mk] using reduced_binomial _ h0 reduced_equation n

theorem hanna_conjecture (n : ℕ) :
    a n % 2 = ((Nat.choose (3 * n) n / (2 * n + 1) : ℕ) : ℤ) % 2 := by
  apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mp
  have hc := congrArg (coeff n) mod_two_identity
  simp only [coeff_map, generatingSeries, coeff_mk, Int.coe_castRingHom] at hc
  rw [Int.cast_natCast, hc]
  exact ((ZMod.natCast_eq_natCast_iff _ _ 2).mpr (ternary_catalan_parity n)).symm

#print axioms strip3_mod_two
#print axioms generating_equation
#print axioms generating_unique
#print axioms choose_three_lucas
#print axioms ternary_catalan_div
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity
