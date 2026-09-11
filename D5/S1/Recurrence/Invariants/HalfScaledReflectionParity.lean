/- GID: D5/S1/Recurrence/Invariants/HalfScaledReflectionParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HalfScaledReflectionParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral compositional reversion and binary coefficient descent prove Hanna parity. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries

namespace D5.S1.Recurrence.Invariants.HalfScaledReflectionParity

def r (n : ℕ) : ℤ :=
  if h0 : n = 0 then 0 else if h1 : n = 1 then 1 else
    if 2 ∣ n then 2 ^ (n / 2 - 1) * r (n / 2) else 0
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

noncomputable def inverseSeries : PowerSeries ℤ := mk r

private theorem r_zero : r 0 = 0 := by rw [r]; simp
private theorem r_one : r 1 = 1 := by rw [r]; simp

private theorem inverse_zero : constantCoeff inverseSeries = 0 := by
  simpa [inverseSeries] using r_zero

private theorem inverse_one : coeff 1 inverseSeries = 1 := by
  simpa [inverseSeries] using r_one

private theorem inverse_unit : IsUnit (coeff 1 inverseSeries) := by
  rw [inverse_one]
  exact isUnit_one

noncomputable def a (n : ℕ) : ℤ :=
  coeff n (inverseSeries.substInvOfIsUnit inverse_unit)

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_eq_inverse :
    generatingSeries = inverseSeries.substInvOfIsUnit inverse_unit := by
  ext n
  simp [generatingSeries, a]

private theorem generating_zero : constantCoeff generatingSeries = 0 := by
  rw [generating_eq_inverse]
  exact constantCoeff_substInvOfIsUnit _ _

private theorem generating_one : coeff 1 generatingSeries = 1 := by
  rw [generating_eq_inverse, coeff_one_substInvOfIsUnit]
  have hu : inverse_unit.unit = 1 := by
    apply Units.ext
    simpa using inverse_one
  rw [hu]
  rfl

private theorem inverse_left : inverseSeries.subst generatingSeries = X := by
  rw [generating_eq_inverse]
  exact subst_substInvOfIsUnit_right _ inverse_zero _

private theorem inverse_right : generatingSeries.subst inverseSeries = X := by
  rw [generating_eq_inverse]
  exact subst_substInvOfIsUnit_left _ inverse_zero _

private theorem scaled_square_coeff (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (f.subst (2 • (X : PowerSeries ℤ) ^ 2)) =
      if 2 ∣ n then 2 ^ (n / 2) * coeff (n / 2) f else 0 := by
  have hs : HasSubst ((X : PowerSeries ℤ) ^ 2) := .X_pow (by omega)
  have he : f.subst (2 • (X : PowerSeries ℤ) ^ 2) =
      (rescale (2 : ℤ) f).subst (X ^ 2) := by
    rw [rescale_eq_subst, subst_comp_subst_apply (.smul_X' (2 : ℤ)) hs,
      subst_smul hs, subst_X hs]
    congr 1
  rw [he, coeff_subst_X_pow (by omega)]
  simp [coeff_rescale]

private theorem inverse_equation :
    inverseSeries.subst (2 • X ^ 2) = 2 • inverseSeries - 2 • X := by
  ext n
  rw [scaled_square_coeff]
  simp only [two_nsmul, map_sub, map_add, inverseSeries, coeff_mk, coeff_X]
  by_cases h0 : n = 0
  · subst n
    simp [r_zero]
  by_cases h1 : n = 1
  · subst n
    simp [r_one]
  rw [if_neg h1, add_zero, sub_zero]
  rw [r.eq_def n]
  simp only [dif_neg h0, dif_neg h1]
  split_ifs with hd
  · have hp : n / 2 - 1 + 1 = n / 2 := by omega
    have hpow : (2 : ℤ) ^ (n / 2) = 2 ^ (n / 2 - 1) * 2 := by
      conv_lhs => rw [← hp, pow_succ]
    rw [hpow]
    ring
  · simp

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    2 • generatingSeries ^ 2 = generatingSeries.subst (2 • X - 2 • generatingSeries) := by
  refine ⟨generating_zero, generating_one, ?_⟩
  have hA : HasSubst generatingSeries := .of_constantCoeff_zero generating_zero
  have hQ : HasSubst (2 • (X : PowerSeries ℤ) ^ 2) := by
    apply HasSubst.of_constantCoeff_zero
    change constantCoeff (2 • (X : PowerSeries ℤ) ^ 2) = 0
    simp only [two_nsmul, map_add, map_pow, constantCoeff_X, zero_pow (by omega : 2 ≠ 0),
      add_zero]
  have he := congrArg (subst generatingSeries) inverse_equation
  have hi : inverseSeries.subst (2 • generatingSeries ^ 2) =
      2 • X - 2 • generatingSeries := by
    rw [subst_comp_subst_apply hQ hA] at he
    simpa only [two_nsmul, subst_add hA, subst_pow hA, subst_X hA,
      subst_sub hA, inverse_left] using he
  have hS : HasSubst (2 • generatingSeries ^ 2) := by
    apply HasSubst.of_constantCoeff_zero
    change constantCoeff (2 • generatingSeries ^ 2) = 0
    simp only [two_nsmul, map_add, map_pow, generating_zero,
      zero_pow (by omega : 2 ≠ 0), add_zero]
  calc
    2 • generatingSeries ^ 2 = PowerSeries.subst (2 • generatingSeries ^ 2)
        (generatingSeries.subst inverseSeries) := by rw [inverse_right, subst_X hS]
    _ = generatingSeries.subst (2 • X - 2 • generatingSeries) := by
      rw [subst_comp_subst_apply (.of_constantCoeff_zero inverse_zero) hS, hi]

private theorem inverse_unique (S : PowerSeries ℤ) (h0 : constantCoeff S = 0)
    (h1 : coeff 1 S = 1)
    (he : S.subst (2 • X ^ 2) = 2 • S - 2 • X) : S = inverseSeries := by
  ext n
  simp only [inverseSeries, coeff_mk]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa [coeff_zero_eq_constantCoeff, r_zero] using h0
    by_cases hn1 : n = 1
    · subst n
      simpa [r_one] using h1
    have hc := congrArg (coeff n) he
    rw [scaled_square_coeff] at hc
    simp only [two_nsmul, map_sub, map_add, coeff_X, if_neg hn1, add_zero,
      sub_zero] at hc
    rw [r.eq_def n]
    simp only [dif_neg hn0, dif_neg hn1]
    by_cases hd : 2 ∣ n
    · rw [if_pos hd] at hc ⊢
      rw [ih (n / 2) (Nat.div_lt_self (by omega) (by omega))] at hc
      have hp : n / 2 - 1 + 1 = n / 2 := by omega
      have hpow : (2 : ℤ) ^ (n / 2) = 2 ^ (n / 2 - 1) * 2 := by
        conv_lhs => rw [← hp, pow_succ]
      rw [hpow] at hc
      nlinarith [hc]
    · rw [if_neg hd] at hc ⊢
      omega

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 0)
    (h1 : coeff 1 B = 1)
    (he : 2 • B ^ 2 = B.subst (2 • X - 2 • B)) : B = generatingSeries := by
  have hu : IsUnit (coeff 1 B) := h1 ▸ isUnit_one
  let S := B.substInvOfIsUnit hu
  have hs0 : constantCoeff S = 0 := constantCoeff_substInvOfIsUnit B hu
  have hs1 : coeff 1 S = 1 := by
    dsimp [S]
    rw [coeff_one_substInvOfIsUnit]
    have hu1 : hu.unit = 1 := by apply Units.ext; simpa using h1
    rw [hu1]
    rfl
  have hBS : B.subst S = X := subst_substInvOfIsUnit_right B h0 hu
  have hSB : S.subst B = X := subst_substInvOfIsUnit_left B h0 hu
  have hB : HasSubst B := .of_constantCoeff_zero h0
  have hS : HasSubst S := .of_constantCoeff_zero hs0
  have hU : HasSubst (2 • X - 2 • B) := by
    apply HasSubst.of_constantCoeff_zero
    change constantCoeff (2 • X - 2 • B) = 0
    simp [h0]
  have heS := congrArg (subst S) he
  rw [subst_comp_subst_apply hU hS] at heS
  have hE : 2 • (X : PowerSeries ℤ) ^ 2 = B.subst (2 • S - 2 • X) := by
    simpa only [two_nsmul, subst_add hS, subst_sub hS, subst_pow hS,
      subst_X hS, hBS] using heS
  have hV : HasSubst (2 • S - 2 • X) := by
    apply HasSubst.of_constantCoeff_zero
    change constantCoeff (2 • S - 2 • X) = 0
    simp [hs0]
  have hSE : S.subst (2 • X ^ 2) = 2 • S - 2 • X := by
    rw [hE, ← subst_comp_subst_apply hB hV, hSB, subst_X hV]
  have hSR : S = inverseSeries := inverse_unique S hs0 hs1 hSE
  calc
    B = PowerSeries.subst generatingSeries (B.subst inverseSeries) := by
      rw [subst_comp_subst_apply (.of_constantCoeff_zero inverse_zero)
        (.of_constantCoeff_zero generating_zero), inverse_left, X_subst]
    _ = generatingSeries := by rw [← hSR, hBS, subst_X
      (.of_constantCoeff_zero generating_zero)]

private theorem inverse_mod_two :
    inverseSeries.map (Int.castRingHom (ZMod 2)) = X + X ^ 2 := by
  ext n
  simp only [coeff_map, inverseSeries, coeff_mk, Int.coe_castRingHom,
    map_add, coeff_X, coeff_X_pow]
  by_cases h0 : n = 0
  · subst n
    simp [r_zero]
  by_cases h1 : n = 1
  · subst n
    simp [r_one]
  by_cases h2 : n = 2
  · subst n
    rw [r]
    norm_num [r_one]
  rw [if_neg h1, if_neg h2, zero_add, r.eq_def n]
  simp only [dif_neg h0, dif_neg h1]
  by_cases hd : 2 ∣ n
  · rw [if_pos hd, Int.cast_mul, Int.cast_pow]
    have hn : n / 2 - 1 ≠ 0 := by omega
    rw [Int.cast_ofNat, show (2 : ZMod 2) = 0 by decide, zero_pow hn, zero_mul]
  · simp [hd]

private theorem binary_equation :
    let A := generatingSeries.map (Int.castRingHom (ZMod 2))
    A + A ^ 2 = X := by
  let hom := Int.castRingHom (ZMod 2)
  have h := congrArg (PowerSeries.map hom) inverse_left
  have hm : PowerSeries.map hom (inverseSeries.subst generatingSeries) =
      (inverseSeries.map hom).subst (generatingSeries.map hom) :=
    map_subst (.of_constantCoeff_zero generating_zero) _
  rw [hm, map_X] at h
  rw [show PowerSeries.map hom inverseSeries = X + X ^ 2 from inverse_mod_two] at h
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_zero, map_zero]
  simpa only [subst_add (.of_constantCoeff_zero hz),
    subst_pow (.of_constantCoeff_zero hz), subst_X (.of_constantCoeff_zero hz)] using h

private theorem square_subst (A : PowerSeries (ZMod 2)) : A ^ 2 = A.subst (X ^ 2) := by
  have h := MvPowerSeries.map_frobenius_expand 2 (by omega : 2 ≠ 0) (f := A)
  change (A.expand 2 (by omega)).map (frobenius (ZMod 2) 2) = A ^ 2 at h
  rw [ZMod.frobenius_zmod, PowerSeries.map_id, expand_apply] at h
  exact h.symm

private theorem parity_recurrence (n : ℕ) :
    (a n : ZMod 2) + (if 2 ∣ n then (a (n / 2) : ZMod 2) else 0) =
      if n = 1 then 1 else 0 := by
  have he := binary_equation
  dsimp only at he
  rw [square_subst] at he
  have hc := congrArg (coeff n) he
  simpa only [map_add, coeff_subst_X_pow (by omega : 2 ≠ 0), coeff_map,
    generatingSeries, coeff_mk, Int.coe_castRingHom, Algebra.algebraMap_self,
    RingHom.id_apply, coeff_X] using hc

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ k, n = 2 ^ k := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hp := parity_recurrence n
    by_cases h1 : n = 1
    · subst n
      have ha : (a 1 : ZMod 2) = 1 := by simpa using hp
      exact ⟨fun _ => ⟨0, by simp⟩, fun _ => ha⟩
    rw [if_neg h1] at hp
    by_cases hd : 2 ∣ n
    · rw [if_pos hd] at hp
      have ha : (a n : ZMod 2) = (a (n / 2) : ZMod 2) := by
        exact (eq_neg_of_add_eq_zero_left hp).trans (ZMod.neg_eq_self_mod_two _)
      rw [ha, ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) (by omega)]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        rw [pow_succ, ← hk]
        omega
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; contradiction
        | succ k =>
          refine ⟨k, ?_⟩
          rw [hk, pow_succ, Nat.mul_div_cancel _ (by omega : 0 < 2)]
    · rw [if_neg hd, add_zero] at hp
      constructor
      · intro ha
        rw [hp] at ha
        exact (zero_ne_one ha).elim
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; contradiction
        | succ k =>
          exact (hd (hk ▸ dvd_pow_self 2 (by omega : k + 1 ≠ 0))).elim

#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.HalfScaledReflectionParity
