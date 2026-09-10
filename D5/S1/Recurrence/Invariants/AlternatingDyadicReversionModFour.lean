/- GID: D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral dyadic reversion and characteristic-four perturbation prove Hanna A389537. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

open PowerSeries
namespace D5.S1.Recurrence.Invariants.AlternatingDyadicReversionModFour

private def r (n : ℕ) : ℤ :=
  if _h0 : n = 0 then 0 else if _h1 : n = 1 then 1 else
    if 2 ∣ n then -r (n / 2) else 0
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
  rw [inverse_one]; exact isUnit_one

noncomputable def a (n : ℕ) : ℤ :=
  coeff n (inverseSeries.substInvOfIsUnit inverse_unit)
noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_eq_inverse :
    generatingSeries = inverseSeries.substInvOfIsUnit inverse_unit := by
  ext n
  simp [generatingSeries, a]
private theorem generating_zero : constantCoeff generatingSeries = 0 := by
  rw [generating_eq_inverse]; exact constantCoeff_substInvOfIsUnit _ _
private theorem generating_one : coeff 1 generatingSeries = 1 := by
  rw [generating_eq_inverse, coeff_one_substInvOfIsUnit]
  have hu : inverse_unit.unit = 1 := by apply Units.ext; simpa using inverse_one
  rw [hu]; rfl
private theorem inverse_left : inverseSeries.subst generatingSeries = X := by
  rw [generating_eq_inverse]; exact subst_substInvOfIsUnit_right _ inverse_zero _
private theorem inverse_right : generatingSeries.subst inverseSeries = X := by
  rw [generating_eq_inverse]; exact subst_substInvOfIsUnit_left _ inverse_zero _

theorem inverse_equation : inverseSeries + inverseSeries.subst (X ^ 2) = X := by
  ext n
  simp only [map_add, coeff_subst_X_pow (by omega : 2 ≠ 0),
    Algebra.algebraMap_self, RingHom.id_apply, inverseSeries, coeff_mk, coeff_X]
  by_cases h0 : n = 0
  · subst n; simp [r_zero]
  by_cases h1 : n = 1
  · subst n; simp [r_one]
  rw [if_neg h1, r.eq_def n]
  simp only [dif_neg h0, dif_neg h1]
  split_ifs <;> simp

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries.subst (generatingSeries - X) = generatingSeries ^ 2 := by
  refine ⟨generating_zero, generating_one, ?_⟩
  have hA : HasSubst generatingSeries := .of_constantCoeff_zero generating_zero
  have hQ : HasSubst ((X : PowerSeries ℤ) ^ 2) := .X_pow (by omega)
  have he := congrArg (subst generatingSeries) inverse_equation
  rw [subst_add hA, subst_comp_subst_apply hQ hA, subst_pow hA, subst_X hA,
    inverse_left] at he
  have hi : inverseSeries.subst (generatingSeries ^ 2) = generatingSeries - X := by
    linear_combination he
  have hS : HasSubst (generatingSeries ^ 2) := .of_constantCoeff_zero (by
    change constantCoeff (generatingSeries ^ 2) = 0
    simp [generating_zero])
  rw [← hi, ← subst_comp_subst_apply (.of_constantCoeff_zero inverse_zero) hS,
    inverse_right, subst_X hS]

private theorem inverse_unique {R : Type*} [CommRing R] {F : PowerSeries R} (S T : PowerSeries R)
    (h0 : constantCoeff S = constantCoeff T)
    (hS : S + S.subst (X ^ 2) = F) (hT : T + T.subst (X ^ 2) = F) : S = T := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simpa only [coeff_zero_eq_constantCoeff] using h0
    have hs := congrArg (coeff n) hS
    have ht := congrArg (coeff n) hT
    simp only [map_add, coeff_subst_X_pow (by omega : 2 ≠ 0),
      Algebra.algebraMap_self, RingHom.id_apply] at hs ht
    by_cases hd : 2 ∣ n
    · rw [if_pos hd, ih (n / 2) (Nat.div_lt_self (by omega) (by omega))] at hs
      rw [if_pos hd] at ht
      exact add_right_cancel (hs.trans ht.symm)
    · simpa only [if_neg hd, add_zero] using hs.trans ht.symm

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 0)
    (h1 : coeff 1 B = 1) (he : B.subst (B - X) = B ^ 2) :
    B = generatingSeries := by
  have hu : IsUnit (coeff 1 B) := h1 ▸ isUnit_one
  let S := B.substInvOfIsUnit hu
  have hs0 : constantCoeff S = 0 := constantCoeff_substInvOfIsUnit B hu
  have hBS : B.subst S = X := subst_substInvOfIsUnit_right B h0 hu
  have hSB : S.subst B = X := subst_substInvOfIsUnit_left B h0 hu
  have hB : HasSubst B := .of_constantCoeff_zero h0
  have hS : HasSubst S := .of_constantCoeff_zero hs0
  have hU : HasSubst (B - X) := .of_constantCoeff_zero (by
    change constantCoeff (B - X) = 0
    simp [h0])
  have heS := congrArg (subst S) he
  rw [subst_comp_subst_apply hU hS, subst_sub hS, subst_X hS,
    subst_pow hS, hBS] at heS
  have hV : HasSubst (X - S) := .of_constantCoeff_zero (by
    change constantCoeff (X - S) = 0
    simp [hs0])
  have hSE : S.subst (X ^ 2) = X - S := by
    rw [← heS, ← subst_comp_subst_apply hB hV, hSB, subst_X hV]
  have hSR : S = inverseSeries := inverse_unique S inverseSeries
    (hs0.trans inverse_zero.symm) (by rw [hSE]; ring) inverse_equation
  calc
    B = PowerSeries.subst generatingSeries (B.subst inverseSeries) := by
      rw [subst_comp_subst_apply (.of_constantCoeff_zero inverse_zero)
        (.of_constantCoeff_zero generating_zero), inverse_left, X_subst]
    _ = generatingSeries := by rw [← hSR, hBS, subst_X (.of_constantCoeff_zero generating_zero)]

private noncomputable def dyadic : PowerSeries (ZMod 4) := by
  classical
  exact mk fun n => if ∃ k : ℕ, n = 3 * 2 ^ k then 1 else 0

private theorem support_halve (n : ℕ) (hn : n ≠ 3) :
    (∃ k : ℕ, n = 3 * 2 ^ k) ↔ 2 ∣ n ∧ ∃ k : ℕ, n / 2 = 3 * 2 ^ k := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => simp at hn
    | succ k =>
      rw [pow_succ, ← mul_assoc]
      exact ⟨dvd_mul_left _ _, k, Nat.mul_div_cancel _ (by omega)⟩
  · rintro ⟨hd, k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [pow_succ, ← mul_assoc, ← hk, Nat.div_mul_cancel hd]

private theorem dyadic_zero : constantCoeff dyadic = 0 := by
  have hn : ¬ ∃ k : ℕ, 0 = 3 * 2 ^ k := by
    rintro ⟨k, hk⟩
    have := pow_pos (by omega : 0 < (2 : ℕ)) k
    omega
  simp only [dyadic, constantCoeff_mk, if_neg hn]

private theorem dyadic_equation : dyadic = X ^ 3 + dyadic.subst (X ^ 2) := by
  classical
  ext n
  rw [map_add, coeff_subst_X_pow (by omega : 2 ≠ 0)]
  by_cases hn : n = 3
  · subst n
    simp [dyadic]
  · simp only [dyadic, coeff_mk, coeff_X_pow, if_neg hn, zero_add,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [support_halve n hn]
    by_cases hd : 2 ∣ n <;> simp [hd]

private theorem four_zero : (4 : PowerSeries (ZMod 4)) = 0 := by
  rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 by decide, map_zero]

-- Squaring erases a perturbation divisible by two in characteristic four.
private theorem square_perturb (S T : PowerSeries (ZMod 4)) :
    (S + 2 * T) ^ 2 = S ^ 2 := by
  linear_combination (S * T + T ^ 2) * four_zero

private noncomputable def reducedInverse : PowerSeries (ZMod 4) :=
  inverseSeries.map (Int.castRingHom (ZMod 4))

private theorem reduced_zero : constantCoeff reducedInverse = 0 := by
  rw [← coeff_zero_eq_constantCoeff, reducedInverse, coeff_map,
    coeff_zero_eq_constantCoeff, inverse_zero, map_zero]

private theorem reduced_equation : reducedInverse + reducedInverse.subst (X ^ 2) = X := by
  have he := congrArg (PowerSeries.map (Int.castRingHom (ZMod 4))) inverse_equation
  have hm : PowerSeries.map (Int.castRingHom (ZMod 4)) (inverseSeries.subst (X ^ 2)) =
      reducedInverse.subst (PowerSeries.map (Int.castRingHom (ZMod 4)) (X ^ 2)) :=
    map_subst (HasSubst.X_pow (R := ℤ) (by omega : 2 ≠ 0)) _
  simp only [map_pow, map_X] at hm
  rw [map_add, hm, map_X] at he
  exact he

private theorem reduced_at (S : PowerSeries (ZMod 4)) (hS : constantCoeff S = 0) :
    reducedInverse.subst S + reducedInverse.subst (S ^ 2) = S := by
  have hs : HasSubst S := .of_constantCoeff_zero hS
  have he := congrArg (subst S) reduced_equation
  rw [subst_add hs, subst_comp_subst_apply (.X_pow (by omega)) hs,
    subst_pow hs, subst_X hs] at he
  exact he

private theorem reduced_perturb (S T : PowerSeries (ZMod 4))
    (hS : constantCoeff S = 0) (hT : constantCoeff T = 0) :
    reducedInverse.subst (S + 2 * T) = reducedInverse.subst S + 2 * T := by
  have he := reduced_at (S + 2 * T) (by simp [hS, hT])
  rw [square_perturb] at he
  linear_combination he - reduced_at S hS

private theorem reduced_quadratic :
    reducedInverse.subst (X + X ^ 2) = X + 2 * dyadic := by
  let U : PowerSeries (ZMod 4) := X + X ^ 2
  let H : PowerSeries (ZMod 4) := reducedInverse.subst U
  have hU : constantCoeff U = 0 := by simp [U]
  have hH : constantCoeff H = 0 := constantCoeff_subst_eq_zero hU _ reduced_zero
  have hs : HasSubst ((X : PowerSeries (ZMod 4)) ^ 2) := .X_pow (by omega)
  have hsq : U ^ 2 = U.subst (X ^ 2) + 2 * X ^ 3 := by
    simp only [U, subst_add hs, subst_pow hs, subst_X hs]
    ring
  have hUS : constantCoeff (U.subst ((X : PowerSeries (ZMod 4)) ^ 2)) = 0 :=
    constantCoeff_subst_eq_zero (by
      change constantCoeff ((X : PowerSeries (ZMod 4)) ^ 2) = 0
      simp) _ hU
  have hE : H + H.subst (X ^ 2) = U - 2 * X ^ 3 := by
    have he := reduced_at U hU
    rw [hsq, reduced_perturb _ _ hUS (by simp),
      ← subst_comp_subst_apply (.of_constantCoeff_zero hU) hs] at he
    dsimp only [H]
    linear_combination he
  have hD : (X + 2 * dyadic : PowerSeries (ZMod 4)) +
      (X + 2 * dyadic).subst (X ^ 2) = U - 2 * X ^ 3 := by
    have htwo : (2 : PowerSeries (ZMod 4)).subst ((X : PowerSeries (ZMod 4)) ^ 2) = 2 := by
      rw [← coe_substAlgHom hs]
      exact map_ofNat _ 2
    rw [subst_add hs, subst_mul hs, subst_X hs, htwo]
    dsimp only [U]
    linear_combination 2 * dyadic_equation +
      (X ^ 3 + dyadic.subst (X ^ 2)) * four_zero
  exact inverse_unique H (X + 2 * dyadic) (by simp [hH, dyadic_zero]) hE hD

private theorem generating_mod_four :
    generatingSeries.map (Int.castRingHom (ZMod 4)) = X + X ^ 2 + 2 * dyadic := by
  let hom := Int.castRingHom (ZMod 4)
  let A := generatingSeries.map hom
  let B : PowerSeries (ZMod 4) := X + X ^ 2 + 2 * dyadic
  have hB : constantCoeff B = 0 := by simp [B, dyadic_zero]
  have hRB : reducedInverse.subst B = X := by
    dsimp only [B]
    rw [reduced_perturb _ _ (by simp) dyadic_zero, reduced_quadratic]
    linear_combination dyadic * four_zero
  have hAR : A.subst reducedInverse = X := by
    have he := congrArg (PowerSeries.map hom) inverse_right
    have hm : PowerSeries.map hom (generatingSeries.subst inverseSeries) =
        A.subst reducedInverse := map_subst (.of_constantCoeff_zero inverse_zero) _
    rw [hm, map_X] at he
    exact he
  calc
    A = A.subst (reducedInverse.subst B) := by rw [hRB, X_subst]
    _ = B := by
      rw [← subst_comp_subst_apply (.of_constantCoeff_zero reduced_zero)
        (.of_constantCoeff_zero hB), hAR, subst_X (.of_constantCoeff_zero hB)]

theorem hanna_conjecture (n : ℕ) (hn : 2 < n) :
    (a n % 4 = 2 ↔ ∃ k : ℕ, n = 3 * 2 ^ k) ∧
    (a n % 4 = 0 ↔ ¬ ∃ k : ℕ, n = 3 * 2 ^ k) := by
  classical
  have hc := congrArg (coeff n) generating_mod_four
  have htwo : (2 : PowerSeries (ZMod 4)) = C 2 := (map_ofNat C 2).symm
  simp only [coeff_map, generatingSeries, coeff_mk, Int.coe_castRingHom,
    map_add, coeff_X, coeff_X_pow, if_neg (by omega : n ≠ 1),
    if_neg (by omega : n ≠ 2), zero_add, htwo, coeff_C_mul, dyadic, coeff_mk] at hc
  by_cases hp : ∃ k : ℕ, n = 3 * 2 ^ k
  · rw [if_pos hp, mul_one] at hc
    have ha : a n % 4 = 2 := (ZMod.intCast_eq_intCast_iff' (a n) 2 4).mp hc
    simp [ha, hp]
  · rw [if_neg hp, mul_zero] at hc
    have ha : a n % 4 = 0 := (ZMod.intCast_eq_intCast_iff' (a n) 0 4).mp hc
    simp [ha, hp]

#print axioms inverse_equation
#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture
end D5.S1.Recurrence.Invariants.AlternatingDyadicReversionModFour
