/- GID: D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/CubicTernarySubstitutionParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact cubic division and ternary contraction give Hanna's coefficient parity. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries

namespace D5.S1.Recurrence.Invariants.CubicTernarySubstitutionParity

theorem cube_congr_subst_three (B : PowerSeries ℤ) :
    (B ^ 3).map (Int.castRingHom (ZMod 3)) =
      PowerSeries.map (Int.castRingHom (ZMod 3)) (B.subst (X ^ 3)) := by
  let f := Int.castRingHom (ZMod 3)
  have h := MvPowerSeries.map_frobenius_expand 3 (by decide : 3 ≠ 0)
    (f := B.map f)
  change ((B.map f).expand 3 (by decide)).map (frobenius (ZMod 3) 3) =
    (B.map f) ^ 3 at h
  rw [ZMod.frobenius_zmod, PowerSeries.map_id] at h
  rw [map_pow, ← PowerSeries.expand_apply 3 (by decide), PowerSeries.map_expand]
  exact h.symm

private noncomputable def numerator (B : PowerSeries ℤ) : PowerSeries ℤ :=
  2 • B ^ 3 + B.subst (X ^ 3)

private theorem numerator_dvd (B : PowerSeries ℤ) (n : ℕ) :
    (3 : ℤ) ∣ coeff n (numerator B) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have h := congrArg (coeff n) (cube_congr_subst_three B)
  change ((coeff n (B ^ 3) : ℤ) : ZMod 3) = (coeff n (B.subst (X ^ 3)) : ℤ) at h
  change (((coeff n) ((2 : ℕ) • B ^ 3 + B.subst (X ^ 3)) : ℤ) : ZMod 3) = 0
  simp only [two_nsmul, map_add, Int.cast_add]
  rw [h]
  ring_nf
  rw [show (3 : ZMod 3) = 0 from rfl, mul_zero]

private noncomputable def step (B : PowerSeries ℤ) : PowerSeries ℤ :=
  X + X ^ 2 + mk (fun n => coeff n (numerator B) / 3)

private theorem coeff_nsmul (k n : ℕ) (B : PowerSeries ℤ) :
    coeff n (k • B) = k • coeff n B :=
  map_nsmul (coeff n).toAddMonoidHom k B

private theorem step_equation (B : PowerSeries ℤ) :
    3 • step B = 3 • (X + X ^ 2) + numerator B := by
  ext n
  simp only [step, nsmul_add, map_add]
  congr 1
  rw [coeff_nsmul, coeff_mk]
  change (3 : ℤ) * (coeff n (numerator B) / 3) = coeff n (numerator B)
  rw [Int.mul_ediv_cancel' (numerator_dvd B n)]

private theorem step_zero {B : PowerSeries ℤ} (hz : constantCoeff B = 0) :
    constantCoeff (step B) = 0 := by
  simp only [step, map_add, map_pow, constantCoeff_X, zero_pow (by decide : 2 ≠ 0),
    add_zero, zero_add, constantCoeff_mk, numerator, two_nsmul]
  simp [coeff_zero_eq_constantCoeff, hz]

private def Agree (d : ℕ) (B C : PowerSeries ℤ) : Prop :=
  ∀ n < d, coeff n B = coeff n C

private theorem agree_iff (d : ℕ) (B C : PowerSeries ℤ) :
    Agree d B C ↔ (X : PowerSeries ℤ) ^ d ∣ B - C := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem cube_agree {d : ℕ} {B C : PowerSeries ℤ}
    (hb : constantCoeff B = 0) (hc : constantCoeff C = 0)
    (h : Agree d B C) : Agree (d + 1) (B ^ 3) (C ^ 3) := by
  apply (agree_iff _ _ _).mpr
  have hd := (agree_iff _ _ _).mp h
  have hz : (X : PowerSeries ℤ) ∣ B ^ 2 + B * C + C ^ 2 := by
    apply X_dvd_iff.mpr
    simp [hb, hc]
  have hm := mul_dvd_mul hd hz
  rw [← pow_succ] at hm
  convert hm using 1
  ring

private theorem subst_agree {d : ℕ} {B C : PowerSeries ℤ}
    (hb : constantCoeff B = 0) (hc : constantCoeff C = 0)
    (h : Agree d B C) : Agree (d + 1) (B.subst (X ^ 3)) (C.subst (X ^ 3)) := by
  intro n hn
  simp only [coeff_subst_X_pow (by decide : 3 ≠ 0), Algebra.algebraMap_self,
    RingHom.id_apply]
  split_ifs with hd
  · by_cases hn0 : n = 0
    · subst n
      simpa only [Nat.zero_div, coeff_zero_eq_constantCoeff] using hb.trans hc.symm
    · exact h (n / 3) (by omega)
  · rfl

private theorem step_agree {d : ℕ} {B C : PowerSeries ℤ}
    (hb : constantCoeff B = 0) (hc : constantCoeff C = 0)
    (h : Agree d B C) : Agree (d + 1) (step B) (step C) := by
  intro n hn
  have hcube := cube_agree hb hc h n hn
  have hsubst := subst_agree hb hc h n hn
  simp only [step, map_add, coeff_mk, numerator, two_nsmul, hcube, hsubst]

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 0
  | d + 1 => step (approximation d)

private theorem approximation_zero (d : ℕ) :
    constantCoeff (approximation d) = 0 := by
  induction d with
  | zero => simp [approximation]
  | succ d ih => exact step_zero ih

private theorem approximation_stable {d e : ℕ} (h : d ≤ e) :
    Agree d (approximation d) (approximation e) := by
  induction d generalizing e with
  | zero => intro n hn; omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      exact step_agree (approximation_zero d) (approximation_zero e) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (d : ℕ) :
    Agree d generatingSeries (approximation d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_zero : constantCoeff generatingSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
    coeff_zero_eq_constantCoeff]
  exact approximation_zero 1

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  ext n
  have hg := generating_agree (n + 2) n (by omega)
  have hs := step_agree generating_zero (approximation_zero (n + 1))
    (generating_agree (n + 1)) n (by omega)
  exact hg.trans hs.symm

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    3 • generatingSeries = 3 • (X + X ^ 2) + 2 • generatingSeries ^ 3 +
      generatingSeries.subst (X ^ 3) := by
  refine ⟨generating_zero, ?_⟩
  simpa only [← generating_fixed, numerator, add_assoc] using step_equation generatingSeries

theorem generating_unique (B : PowerSeries ℤ) (hz : constantCoeff B = 0)
    (he : 3 • B = 3 • (X + X ^ 2) + 2 • B ^ 3 + B.subst (X ^ 3)) :
    B = generatingSeries := by
  have hf : B = step B := by
    ext n
    have hs : 3 • B = 3 • step B := by
      rw [step_equation, numerator, ← add_assoc]
      exact he
    have hh := congrArg (coeff n) hs
    simp only [coeff_nsmul] at hh
    simp only [nsmul_eq_mul] at hh
    omega
  have ha : ∀ d, Agree d B generatingSeries := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih =>
      simpa only [← hf, ← generating_fixed] using step_agree hz generating_zero ih
  ext n
  exact ha (n + 1) n (by omega)

private theorem coefficient_equation (n : ℕ) :
    3 * a n = 3 * ((if n = 1 then 1 else 0) + (if n = 2 then 1 else 0)) +
      2 * coeff n (generatingSeries ^ 3) + (if 3 ∣ n then a (n / 3) else 0) := by
  have h := congrArg (coeff n) generating_equation.2
  simp only [map_add, coeff_nsmul] at h
  simpa only [nsmul_eq_mul, Nat.cast_ofNat, coeff_X,
    coeff_X_pow, coeff_subst_X_pow (by decide : 3 ≠ 0), Algebra.algebraMap_self,
    RingHom.id_apply, generatingSeries, coeff_mk] using h

private theorem parity_recurrence (n : ℕ) :
    a n % 2 = ((if n = 1 then 1 else 0) + (if n = 2 then 1 else 0) +
      (if 3 ∣ n then a (n / 3) else 0)) % 2 := by
  have h := coefficient_equation n
  omega

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ k, n = 3 ^ k ∨ n = 2 * 3 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hp := parity_recurrence n
    by_cases h1 : n = 1
    · subst n
      have ho : Odd (a 1) := by
        rw [Int.odd_iff]
        simpa using hp
      exact ⟨fun _ => ⟨0, by simp⟩, fun _ => ho⟩
    by_cases h2 : n = 2
    · subst n
      have ho : Odd (a 2) := by
        rw [Int.odd_iff]
        simpa using hp
      exact ⟨fun _ => ⟨0, by simp⟩, fun _ => ho⟩
    by_cases h3 : 3 ∣ n
    · have hsmall : n / 3 < n := by omega
      have hpos : 1 ≤ n / 3 := by omega
      have hmul := Nat.mul_div_cancel' h3
      have hodd : Odd (a n) ↔ Odd (a (n / 3)) := by
        simp only [h1, h2, h3, if_false, if_true, zero_add] at hp
        rw [Int.odd_iff, Int.odd_iff, hp]
      rw [hodd, ih (n / 3) hsmall hpos]
      constructor
      · rintro ⟨k, hk | hk⟩
        · exact ⟨k + 1, Or.inl (by rw [pow_succ]; omega)⟩
        · exact ⟨k + 1, Or.inr (by rw [pow_succ]; omega)⟩
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp only [pow_zero, mul_one] at hk; omega
        | succ k =>
          refine ⟨k, ?_⟩
          simp only [pow_succ] at hk
          rcases hk with hk | hk
          · left; omega
          · right; omega
    · have hnot : ¬ Odd (a n) := by
        rw [Int.odd_iff]
        simp only [h1, h2, h3, if_false, zero_add, Int.zero_emod] at hp
        omega
      refine ⟨fun h => (hnot h).elim, ?_⟩
      rintro ⟨k, hk⟩
      exfalso
      cases k with
      | zero => simp only [pow_zero, mul_one] at hk; omega
      | succ k =>
        simp only [pow_succ] at hk
        rcases hk with hk | hk
        · exact h3 ⟨3 ^ k, by omega⟩
        · exact h3 ⟨2 * 3 ^ k, by omega⟩

#print axioms cube_congr_subst_three
#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.CubicTernarySubstitutionParity
