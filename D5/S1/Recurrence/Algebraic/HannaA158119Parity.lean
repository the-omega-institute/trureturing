/- GID: D5/S1/Recurrence/Algebraic/HannaA158119Parity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA158119Parity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The original factorial-product series and its normalized reversion quotient. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
import D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime

/-! # The original factorial-product reversion quotient in OEIS A158119 -/

open PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Algebraic.HannaA158119Parity

noncomputable def summand (n : ℕ) : PowerSeries ℤ :=
  C (n.factorial : ℤ) * X ^ n *
    ∏ k ∈ Finset.range n, invOfUnit (1 + C (2 * (k + 1) : ℤ) * X) 1

/-- The original infinite OGF, interpreted coefficientwise. -/
noncomputable def F : PowerSeries ℤ :=
  mk fun d => ∑ᶠ n : ℕ, coeff d (summand n)

private theorem summand_order (n : ℕ) : (X : PowerSeries ℤ) ^ n ∣ summand n := by
  refine ⟨C (n.factorial : ℤ) *
    ∏ k ∈ Finset.range n, invOfUnit (1 + C (2 * (k + 1) : ℤ) * X) 1, ?_⟩
  dsimp [summand]
  ring

private theorem F_coeff (d : ℕ) :
    coeff d F = ∑ n ∈ Finset.range (d + 1), coeff d (summand n) := by
  classical
  rw [F, coeff_mk]
  apply finsum_eq_sum_of_support_subset
  intro n hn
  change coeff d (summand n) ≠ 0 at hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hn (X_pow_dvd_iff.mp (summand_order n) d (by omega))

private theorem F_zero : constantCoeff F = 1 := by
  rw [← coeff_zero_eq_constantCoeff, F_coeff]
  simp [summand]

private theorem linear_unit : IsUnit (coeff 1 (X * F)) := by
  simp [coeff_zero_eq_constantCoeff, F_zero]

noncomputable def Q : PowerSeries ℤ := (X * F).substInvOfIsUnit linear_unit

/-- The inverse equation gives this normalized quotient without dividing by a nonunit. -/
noncomputable def B : PowerSeries ℤ := F.subst Q

noncomputable def a (m : ℕ) : ℕ := (coeff (2 * m) B).natAbs

def claim : Prop := ∀ m : ℕ, Odd (a m) ↔ m = 0 ∨ ∃ j : ℕ, m = 2 ^ j

private theorem Q_zero : constantCoeff Q = 0 := by simp [Q]

private theorem inverse_equation : (X * F).subst Q = X :=
  subst_substInvOfIsUnit_right _ (by simp) linear_unit

theorem quotient_equation : B * Q = X := by
  have h := inverse_equation
  rw [subst_mul (.of_constantCoeff_zero Q_zero), subst_X (.of_constantCoeff_zero Q_zero)] at h
  simpa [B, mul_comm] using h

private theorem summand_mod_two (n : ℕ) :
    (summand n).map (Int.castRingHom (ZMod 2)) =
      if n = 0 then 1 else if n = 1 then X else 0 := by
  classical
  let hom := Int.castRingHom (ZMod 2)
  have htwo : (2 : ZMod 2) = 0 := by decide
  have htwoS : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (C (R := ZMod 2)) htwo
  have hi (k : ℕ) :
      (invOfUnit (1 + C (2 * (k + 1) : ℤ) * X) 1).map hom = 1 := by
    rw [D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime.map_inverse hom _ (by simp)]
    have hd : (1 + C (2 * (k + 1) : ℤ) * X).map hom = 1 := by
      simp [hom, map_ofNat, htwoS]
    rw [hd]
    simpa using mul_invOfUnit (1 : PowerSeries (ZMod 2)) 1 (by simp)
  rcases n with _ | n
  · simp [summand]
  rcases n with _ | n
  · simpa [summand, hom] using hi 0
  · have hd : 2 ∣ (n + 2).factorial := Nat.dvd_factorial (by omega) (by omega)
    have hz : ((n + 1 + 1).factorial : ZMod 2) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
    simp only [summand, map_mul, map_C, map_pow, map_X,
      Int.coe_castRingHom, Int.cast_natCast, hz, map_zero, zero_mul]
    simp

private theorem F_mod_two : F.map (Int.castRingHom (ZMod 2)) = 1 + X := by
  classical
  ext d
  simp only [coeff_map, F_coeff, map_sum]
  simp_rw [← coeff_map, summand_mod_two]
  rcases d with _ | d
  · simp
  · simp_rw [apply_ite (coeff (d + 1))]
    simp only [coeff_one, show d + 1 ≠ 0 by omega, ite_false]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b hb hb1
      by_cases hb0 : b = 0 <;> simp [hb0, hb1]
    · simp

private theorem B_mod_two : B.map (Int.castRingHom (ZMod 2)) =
    1 + Q.map (Int.castRingHom (ZMod 2)) := by
  have hz : constantCoeff (Q.map (Int.castRingHom (ZMod 2))) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      Q_zero, map_zero]
  have hs : HasSubst (Q.map (Int.castRingHom (ZMod 2))) := .of_constantCoeff_zero hz
  have he : B.map (Int.castRingHom (ZMod 2)) =
      (F.map (Int.castRingHom (ZMod 2))).subst (Q.map (Int.castRingHom (ZMod 2))) :=
    map_subst (.of_constantCoeff_zero Q_zero) F
  rw [he, F_mod_two, subst_add hs, subst_X hs]
  congr 1
  rw [← coe_substAlgHom hs, map_one]

private theorem Q_mod_two : Q.map (Int.castRingHom (ZMod 2)) =
    D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries.map
      (Int.castRingHom (ZMod 2)) := by
  let hom := Int.castRingHom (ZMod 2)
  let q := Q.map hom
  let k := D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries.map hom
  let p : PowerSeries (ZMod 2) := X + X ^ 2
  have hq0 : constantCoeff q = 0 := by
    dsimp only [q]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      Q_zero, map_zero]
  have hk0 : constantCoeff k = 0 := by
    dsimp only [k]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalan_equation.1, map_zero]
  have hp0 : constantCoeff p = 0 := by simp [p]
  have hp1 : IsUnit (coeff 1 p) := by simp [p]
  have hq : q + q ^ 2 = X := by
    have h := congrArg (PowerSeries.map hom) quotient_equation
    rw [map_mul, B_mod_two, map_X] at h
    change (1 + q) * q = X at h
    linear_combination h
  have hk : k + k ^ 2 = X := by
    have h := congrArg (PowerSeries.map hom)
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalan_equation.2.2
    simp only [map_add, map_X, map_pow] at h
    change k = X + k ^ 2 at h
    have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg (C (R := ZMod 2))
        (show (2 : ZMod 2) = 0 by decide)
    linear_combination (norm := (ring_nf; simp [htwo])) h
  have hqi : p.subst q = X := by
    simpa only [p, subst_add (.of_constantCoeff_zero hq0),
      subst_X (.of_constantCoeff_zero hq0), subst_pow (.of_constantCoeff_zero hq0)] using hq
  have hki : p.subst k = X := by
    simpa only [p, subst_add (.of_constantCoeff_zero hk0),
      subst_X (.of_constantCoeff_zero hk0), subst_pow (.of_constantCoeff_zero hk0)] using hk
  exact (eq_substInvOfIsUnit_of_subst_eq_X p hp0 hp1 (.of_constantCoeff_zero hq0) hqi).trans
    (eq_substInvOfIsUnit_of_subst_eq_X p hp0 hp1 (.of_constantCoeff_zero hk0) hki).symm

theorem result : claim := by
  intro m
  by_cases hm : m = 0
  · subst m
    have h0 : constantCoeff B = 1 := by
      change MvPowerSeries.constantCoeff (F.subst Q) = 1
      simpa only [Algebra.algebraMap_self, RingHom.id_apply, F_zero] using
        constantCoeff_subst_of_constantCoeff_zero Q_zero F
    simp [a, coeff_zero_eq_constantCoeff, h0]
  · rw [a, Int.natAbs_odd, ← ZMod.intCast_eq_one_iff_odd]
    have hb := congrArg (coeff (2 * m)) B_mod_two
    rw [Q_mod_two] at hb
    change (coeff (2 * m) (B.map (Int.castRingHom (ZMod 2))) = 1) ↔ _
    rw [hb]
    simp only [map_add, coeff_one, show 2 * m ≠ 0 by omega, ite_false, zero_add,
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.binary_catalan,
      hm, false_or]
    constructor
    · rintro ⟨j, hj⟩
      cases j with
      | zero => simp at hj
      | succ j =>
        refine ⟨j, ?_⟩
        rw [pow_succ] at hj
        omega
    · rintro ⟨j, rfl⟩
      exact ⟨j + 1, by rw [pow_succ]; omega⟩

#print axioms result

end D5.S1.Recurrence.Algebraic.HannaA158119Parity
