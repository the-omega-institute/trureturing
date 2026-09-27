/- GID: D5/S1/Recurrence/Parity/A380558
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/A380558
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A380558 source uniqueness and full dyadic parity support. -/

import D5.S1.Recurrence.Parity.QuadraticSquareReversionDyadicSupportParity
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

open PowerSeries

namespace D5.S1.Recurrence.Parity.A380558

noncomputable def generatingSeries : PowerSeries ℤ :=
  QuadraticSquareReversionDyadicSupportParity.generatingSeries ^ 2 *
    invOfUnit (1 - QuadraticSquareReversionDyadicSupportParity.generatingSeries ^ 2) 1

private def Support (n : ℕ) : Prop :=
  n = 1 ∨ ∃ j : ℕ, 3 * 2 ^ j ≤ n ∧ n < 4 * 2 ^ j

private theorem support_step (n : ℕ) (hn : 3 ≤ n) :
    Support n ↔ Support (n / 2) := by
  constructor
  · rintro (h | ⟨j, hlo, hhi⟩)
    · omega
    · cases j with
      | zero =>
        left
        norm_num at hlo hhi
        omega
      | succ j =>
        rw [pow_succ] at hlo hhi
        right
        refine ⟨j, ?_, ?_⟩
        all_goals omega
  · rintro (h | ⟨j, hlo, hhi⟩)
    · right
      refine ⟨0, ?_, ?_⟩ <;> norm_num <;> omega
    · right
      have hlo' : 3 * (2 ^ j * 2) ≤ n := by omega
      have hhi' : n < 4 * (2 ^ j * 2) := by omega
      refine ⟨j + 1, ?_, ?_⟩
      · simpa only [pow_succ] using hlo'
      · simpa only [pow_succ] using hhi'

private noncomputable def L : PowerSeries (ZMod 2) :=
  D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity.lacunarySeries

private noncomputable def T : PowerSeries (ZMod 2) :=
  L * invOfUnit (1 - L) 1

private theorem T_equation : T = X + X ^ 2 + (1 + X) * T ^ 2 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
      simpa only [map_ofNat, map_zero] using
        congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide))
  have hL0 : constantCoeff L = 0 := by
    have h := congrArg constantCoeff
      D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity.lacunary_quadratic
    simpa [L] using h
  have hL : L = X + X ^ 2 + X ^ 2 * L ^ 2 :=
    D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity.lacunary_quadratic
  have hv : T * (1 + L) = L := by
    have hi : invOfUnit (1 - L) 1 * (1 + L) = 1 := by
      have h0 := invOfUnit_mul (1 - L) 1 (by simp [hL0])
      have he : (1 - L : PowerSeries (ZMod 2)) = 1 + L := CharTwo.sub_eq_add _ _
      exact (congrArg (fun p : PowerSeries (ZMod 2) => invOfUnit (1 - L) 1 * p) he).symm.trans h0
    change L * invOfUnit (1 - L) 1 * (1 + L) = L
    calc
      L * invOfUnit (1 - L) 1 * (1 + L) = L * (invOfUnit (1 - L) 1 * (1 + L)) := by ring
      _ = L := by rw [hi]; ring
  have hu : IsUnit (1 + L) := by
    rw [isUnit_iff_constantCoeff]
    simp only [map_add, map_one, hL0, add_zero]
    exact isUnit_one
  have hu2 : IsUnit ((1 + L) ^ 2) := hu.pow 2
  apply hu2.mul_right_cancel
  have hv2 : T ^ 2 * (1 + L) ^ 2 = L ^ 2 := by rw [← mul_pow, hv]
  have hs : (1 + L) ^ 2 = 1 + L ^ 2 := by simp only [CharTwo.add_sq, one_pow]
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := CharP.ofNat_eq_zero _ 2
  have hkey : L * (1 + L) = (X + X ^ 2) * (1 + L) ^ 2 + (1 + X) * L ^ 2 := by
    rw [hs]
    calc
      L * (1 + L) = L + L ^ 2 := by ring
      _ = (X + X ^ 2 + X ^ 2 * L ^ 2) + L ^ 2 :=
        congrArg (fun f => f + L ^ 2) hL
      _ = (X + X ^ 2) * (1 + L ^ 2) + (1 + X) * L ^ 2 := by
        calc
          (X + X ^ 2 + X ^ 2 * L ^ 2) + L ^ 2 =
              (X + X ^ 2) * (1 + L ^ 2) + (1 + X) * L ^ 2 -
                (2 : PowerSeries (ZMod 2)) * (X * L ^ 2) := by ring
          _ = (X + X ^ 2) * (1 + L ^ 2) + (1 + X) * L ^ 2 := by rw [htwo]; ring
  calc
    T * (1 + L) ^ 2 = L * (1 + L) := by
      calc
        T * (1 + L) ^ 2 = (T * (1 + L)) * (1 + L) := by ring
        _ = L * (1 + L) := by rw [hv]
    _ = (X + X ^ 2) * (1 + L) ^ 2 + (1 + X) * L ^ 2 := hkey
    _ = (X + X ^ 2 + (1 + X) * T ^ 2) * (1 + L) ^ 2 := by
      calc
        (X + X ^ 2) * (1 + L) ^ 2 + (1 + X) * L ^ 2 =
            (X + X ^ 2) * (1 + L) ^ 2 + (1 + X) * (T ^ 2 * (1 + L) ^ 2) := by rw [hv2]
        _ = (X + X ^ 2 + (1 + X) * T ^ 2) * (1 + L) ^ 2 := by ring

attribute [local instance] Classical.propDecidable

private theorem T_coeff : ∀ n : ℕ, coeff n T = if Support n then 1 else 0 := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
      simpa only [map_ofNat, map_zero] using
        congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide))
  have square_expand (f : PowerSeries (ZMod 2)) :
      f ^ 2 = expand 2 (by decide) f := by
    have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2)
      2 (by decide) (f := f)
    rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
    exact h.symm
  have square_even (f : PowerSeries (ZMod 2)) (k : ℕ) :
      coeff (2 * k) (f ^ 2) = coeff k f := by
    rw [square_expand, coeff_expand_mul]
  have square_odd (f : PowerSeries (ZMod 2)) (k : ℕ) :
      coeff (2 * k + 1) (f ^ 2) = 0 := by
    rw [square_expand, coeff_expand_of_not_dvd]
    omega
  have support_zero : ¬ Support 0 := by
    rintro (h | ⟨j, hlo, _⟩)
    · omega
    · have hp := Nat.one_le_pow j 2 (by omega)
      omega
  have support_two : ¬ Support 2 := by
    rintro (h | ⟨j, hlo, _⟩)
    · omega
    · have hp := Nat.one_le_pow j 2 (by omega)
      omega
  classical
  have hL0 : constantCoeff L = 0 := by
    have h := congrArg constantCoeff
      D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity.lacunary_quadratic
    simpa [L] using h
  have hT0 : constantCoeff T = 0 := by simp [T, hL0]
  have heq : T = X + X ^ 2 + T ^ 2 + X * T ^ 2 := by
    calc
      T = X + X ^ 2 + (1 + X) * T ^ 2 := T_equation
      _ = X + X ^ 2 + T ^ 2 + X * T ^ 2 := by ring
  have hz : coeff 0 T = 0 := by simpa only [coeff_zero_eq_constantCoeff] using hT0
  have hsq0 : coeff 0 (T ^ 2) = 0 := by simpa only [zero_mul] using (square_even T 0).trans hz
  have hsq1 : coeff 1 (T ^ 2) = 0 := by simpa only [mul_zero, zero_add] using square_odd T 0
  have h1 : coeff 1 T = 1 := by
    have hc := congrArg (coeff 1) heq
    simp only [map_add] at hc
    have hx : coeff 1 (X : PowerSeries (ZMod 2)) = 1 := by simp
    have hx2 : coeff 1 (X ^ 2 : PowerSeries (ZMod 2)) = 0 := by simp [coeff_X_pow]
    have hshift : coeff 1 (X * T ^ 2) = 0 := by
      simpa only [Nat.zero_add, coeff_succ_X_mul] using hsq0
    rw [hx, hx2, hsq1, hshift] at hc
    simpa using hc
  have h2 : coeff 2 T = 0 := by
    have hc := congrArg (coeff 2) heq
    simp only [map_add] at hc
    have hx : coeff 2 (X : PowerSeries (ZMod 2)) = 0 := by simp [coeff_X]
    have hx2 : coeff 2 (X ^ 2 : PowerSeries (ZMod 2)) = 1 := by simp [coeff_X_pow]
    have hsq2 : coeff 2 (T ^ 2) = 1 := by simpa only [one_mul] using (square_even T 1).trans h1
    have hshift : coeff 2 (X * T ^ 2) = 0 := by
      simpa only [coeff_succ_X_mul] using hsq1
    rw [hx, hx2, hsq2, hshift] at hc
    have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    simpa only [zero_add, add_zero, h11] using hc
  have hrec (n : ℕ) (hn : 3 ≤ n) : coeff n T = coeff (n / 2) T := by
    by_cases hd : 2 ∣ n
    · obtain ⟨k, rfl⟩ := hd
      have hk : 2 ≤ k := by omega
      have hc := congrArg (coeff (2 * k)) heq
      simp only [map_add] at hc
      have hx : coeff (2 * k) (X : PowerSeries (ZMod 2)) = 0 := by
        simp [coeff_X, show 2 * k ≠ 1 by omega]
      have hx2 : coeff (2 * k) (X ^ 2 : PowerSeries (ZMod 2)) = 0 := by
        simp [coeff_X_pow, show 2 * k ≠ 2 by omega]
      have hshift : coeff (2 * k) (X * T ^ 2) = 0 := by
        have hi : 2 * k = (2 * (k - 1) + 1) + 1 := by omega
        rw [hi, coeff_succ_X_mul, square_odd]
      rw [hx, hx2, square_even, hshift] at hc
      simpa using hc
    · have hm : 2 ∣ n - 1 := by omega
      obtain ⟨k, hk⟩ := hm
      have he : n = 2 * k + 1 := by omega
      subst n
      have hkc : 1 ≤ k := by omega
      have hc := congrArg (coeff (2 * k + 1)) heq
      simp only [map_add] at hc
      have hx : coeff (2 * k + 1) (X : PowerSeries (ZMod 2)) = 0 := by
        rw [coeff_X, if_neg (by omega)]
      have hx2 : coeff (2 * k + 1) (X ^ 2 : PowerSeries (ZMod 2)) = 0 := by
        simp [coeff_X_pow, show 2 * k + 1 ≠ 2 by omega]
      rw [hx, hx2, square_odd, coeff_succ_X_mul, square_even] at hc
      have hdiv : (2 * k + 1) / 2 = k := by omega
      rw [hdiv]
      simpa using hc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa only [if_neg support_zero] using hz
    by_cases hn1 : n = 1
    · subst n
      simpa only [if_pos (show Support 1 from Or.inl rfl)] using h1
    by_cases hn2 : n = 2
    · subst n
      simpa only [if_neg support_two] using h2
    have hn : 3 ≤ n := by omega
    calc
      coeff n T = coeff (n / 2) T := hrec n hn
      _ = if Support (n / 2) then 1 else 0 := ih (n / 2) (by omega)
      _ = if Support n then 1 else 0 := by rw [support_step n hn]

private theorem parity (n : ℕ) :
    Odd (coeff n generatingSeries) ↔ n = 2 ∨
      ∃ m j : ℕ, n = 2 * m ∧ 3 * 2 ^ j ≤ m ∧ m < 4 * 2 ^ j := by
  letI : CharP (PowerSeries (ZMod 2)) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
      simpa only [map_ofNat, map_zero] using
        congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide))
  let hom := Int.castRingHom (ZMod 2)
  let B : PowerSeries ℤ := QuadraticSquareReversionDyadicSupportParity.generatingSeries
  have hB0 : constantCoeff B = 0 :=
    QuadraticSquareReversionDyadicSupportParity.generating_equation.1
  have hBmap : B.map hom = L :=
    QuadraticSquareReversionDyadicSupportParity.mod_two_identity
  have hAmul : generatingSeries * (1 - B ^ 2) = B ^ 2 := by
    change (B ^ 2 * invOfUnit (1 - B ^ 2) 1) * (1 - B ^ 2) = B ^ 2
    rw [mul_assoc, invOfUnit_mul (1 - B ^ 2) 1 (by simp [hB0])]
    ring
  have hmapmul : (generatingSeries.map hom) * (1 - L ^ 2) = L ^ 2 := by
    have h := congrArg (PowerSeries.map hom) hAmul
    simpa only [map_mul, map_sub, map_one, map_pow, hBmap] using h
  have hL0 : constantCoeff L = 0 := by
    have h := congrArg constantCoeff
      D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity.lacunary_quadratic
    simpa [L] using h
  have hTmul : T * (1 - L) = L := by
    change (L * invOfUnit (1 - L) 1) * (1 - L) = L
    rw [mul_assoc, invOfUnit_mul (1 - L) 1 (by simp [hL0])]
    ring
  have hden : (1 - L) ^ 2 = 1 - L ^ 2 := by
    simp only [CharTwo.sub_eq_add, CharTwo.add_sq, one_pow]
  have hTmul2 : T ^ 2 * (1 - L ^ 2) = L ^ 2 := by
    rw [← hden, ← mul_pow, hTmul]
  have hu : IsUnit (1 - L ^ 2) := by
    rw [isUnit_iff_constantCoeff]
    simp [hL0]
  have hAmap : generatingSeries.map hom = T ^ 2 :=
    hu.mul_right_cancel (hmapmul.trans hTmul2.symm)
  have square_expand (f : PowerSeries (ZMod 2)) :
      f ^ 2 = expand 2 (by decide) f := by
    have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2)
      2 (by decide) (f := f)
    rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
    exact h.symm
  have square_even (f : PowerSeries (ZMod 2)) (k : ℕ) :
      coeff (2 * k) (f ^ 2) = coeff k f := by
    rw [square_expand, coeff_expand_mul]
  have square_odd (f : PowerSeries (ZMod 2)) (k : ℕ) :
      coeff (2 * k + 1) (f ^ 2) = 0 := by
    rw [square_expand, coeff_expand_of_not_dvd]
    omega
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hc := congrArg (coeff n) hAmap
  rw [coeff_map] at hc
  change ((coeff n generatingSeries : ℤ) : ZMod 2) = coeff n (T ^ 2) at hc
  rw [hc]
  by_cases hd : 2 ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [square_even, T_coeff]
    have hi : (if Support m then (1 : ZMod 2) else 0) = 1 ↔ Support m := by
      by_cases hs : Support m <;> simp [hs]
    rw [hi]
    constructor
    · rintro (h1 | ⟨j, hlo, hhi⟩)
      · left
        omega
      · right
        exact ⟨m, j, rfl, hlo, hhi⟩
    · rintro (h2 | ⟨k, j, hk, hlo, hhi⟩)
      · left
        omega
      · right
        have hmk : m = k := by omega
        subst k
        exact ⟨j, hlo, hhi⟩
  · have hm : 2 ∣ n - 1 := by omega
    obtain ⟨m, hmn⟩ := hm
    have he : n = 2 * m + 1 := by omega
    rw [he, square_odd]
    constructor
    · intro h
      simp at h
    · rintro (h2 | ⟨k, j, hk, hlo, hhi⟩) <;> omega

theorem result :
    constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 0 ∧
    generatingSeries.subst (X - generatingSeries) =
      X ^ 2 * invOfUnit (1 - X ^ 2) 1 ∧
    (∀ F : PowerSeries ℤ, constantCoeff F = 0 → coeff 1 F = 0 →
      F.subst (X - F) = X ^ 2 * invOfUnit (1 - X ^ 2) 1 →
      F = generatingSeries) ∧
    ∀ n : ℕ, Odd (coeff n generatingSeries) ↔ n = 2 ∨
      ∃ m j : ℕ, n = 2 * m ∧ 3 * 2 ^ j ≤ m ∧ m < 4 * 2 ^ j := by
  let B : PowerSeries ℤ := QuadraticSquareReversionDyadicSupportParity.generatingSeries
  let rational (f : PowerSeries ℤ) : PowerSeries ℤ :=
    f ^ 2 * invOfUnit (1 - f ^ 2) 1
  have hB0 : constantCoeff B = 0 :=
    QuadraticSquareReversionDyadicSupportParity.generating_equation.1
  have hA0 : constantCoeff generatingSeries = 0 := by
    change constantCoeff (rational B) = 0
    simp [rational, hB0]
  have hA1 : coeff 1 generatingSeries = 0 := by
    have hd : (X : PowerSeries ℤ) ^ 2 ∣ rational B := by
      change X ^ 2 ∣ B ^ 2 * invOfUnit (1 - B ^ 2) 1
      exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hB0) 2) _
    exact X_pow_dvd_iff.mp hd 1 (by omega)
  have rational_subst {f g : PowerSeries ℤ}
      (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
      (rational f).subst g = rational (f.subst g) := by
    let hs : HasSubst g := .of_constantCoeff_zero hg
    have hfg : constantCoeff (f.subst g) = 0 :=
      constantCoeff_subst_eq_zero hg f hf
    have hunit : IsUnit (1 - (f.subst g) ^ 2) := by
      rw [isUnit_iff_constantCoeff]
      simp [hfg]
    have hdenom : constantCoeff (1 - (f.subst g) ^ 2) = 1 := by simp [hfg]
    have hone : (1 : PowerSeries ℤ).subst g = 1 := by
      rw [← coe_substAlgHom hs]
      exact map_one _
    have hrec : (invOfUnit (1 - f ^ 2) 1).subst g *
        (1 - (f.subst g) ^ 2) = 1 := by
      have h := congrArg (fun p : PowerSeries ℤ => p.subst g)
        (invOfUnit_mul (1 - f ^ 2) 1 (by simp [hf]))
      simpa only [subst_mul hs, subst_sub hs, subst_pow hs, hone] using h
    have hrec_eq : (invOfUnit (1 - f ^ 2) 1).subst g =
        invOfUnit (1 - (f.subst g) ^ 2) 1 := by
      apply hunit.mul_right_cancel
      exact hrec.trans (invOfUnit_mul _ _ hdenom).symm
    simp only [rational, subst_mul hs, subst_pow hs, hrec_eq]
  have hsource : generatingSeries.subst (X - generatingSeries) =
      X ^ 2 * invOfUnit (1 - X ^ 2) 1 := by
    let U : PowerSeries ℤ := X - generatingSeries
    have hU0 : constantCoeff U = 0 := by simp [U, hA0]
    have hBU : B.subst U = X :=
      QuadraticSquareReversionDyadicSupportParity.generating_equation.2.2
    change (rational B).subst U = rational X
    rw [rational_subst hB0 hU0, hBU]
  have hunique (F : PowerSeries ℤ)
      (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F = 0)
      (hF : F.subst (X - F) = X ^ 2 * invOfUnit (1 - X ^ 2) 1) :
      F = generatingSeries := by
    let U : PowerSeries ℤ := X - F
    have hU0 : constantCoeff U = 0 := by simp [U, hF0]
    have hU1 : coeff 1 U = 1 := by simp [U, hF1]
    have hunit : IsUnit (coeff 1 U) := by rw [hU1]; exact isUnit_one
    let H := U.substInvOfIsUnit hunit
    have hH0 : constantCoeff H = 0 := constantCoeff_substInvOfIsUnit U hunit
    have hH1 : coeff 1 H = 1 := by simp [H, hU1]
    have hUH : U.subst H = X := subst_substInvOfIsUnit_right U hU0 hunit
    have hHU : H.subst U = X := subst_substInvOfIsUnit_left U hU0 hunit
    have hFH : F = rational H := by
      have hsourceF : F.subst U = rational X := hF
      have hc := congrArg (fun p : PowerSeries ℤ => p.subst H) hsourceF
      rw [subst_comp_subst_apply (.of_constantCoeff_zero hU0)
        (HasSubst.substInvOfIsUnit U hunit) F, hUH, X_subst] at hc
      have hR : (rational X).subst H = rational H := by
        rw [rational_subst (f := X) (g := H) (by simp) hH0,
          subst_X (HasSubst.of_constantCoeff_zero hH0)]
      exact hc.trans hR
    have hHeq : H = B := by
      have heq : H.subst (X - rational H) = X := by
        have harg : X - rational H = U := by rw [← hFH]
        rw [harg]
        exact hHU
      exact QuadraticSquareReversionDyadicSupportParity.generating_unique H hH0 hH1 heq
    calc
      F = rational H := hFH
      _ = generatingSeries := by rw [hHeq]; rfl
  exact ⟨hA0, hA1, hsource, hunique, parity⟩

#print axioms result

end D5.S1.Recurrence.Parity.A380558
