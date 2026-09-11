/- GID: D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/IterateProductTwoThreeModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Degree contraction and a rational mod-four fixed point prove Hanna A396099. -/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import Mathlib.Tactic.ReduceModChar

open PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (iterate mobius)

namespace D5.S1.Recurrence.Parity.IterateProductTwoThreeModFour

variable {R : Type*} [CommRing R]

private theorem coeff_eq_of_dvd {f g : PowerSeries R} {d n : ℕ}
    (h : (X : PowerSeries R) ^ d ∣ f - g) (hn : n < d) : coeff n f = coeff n g := by
  simpa only [map_sub, sub_eq_zero] using X_pow_dvd_iff.mp h n hn

private theorem subst_congr {f g u v : PowerSeries R} {d : ℕ}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hf : (X : PowerSeries R) ^ d ∣ f - g)
    (huv : (X : PowerSeries R) ^ d ∣ u - v) :
    (X : PowerSeries R) ^ d ∣ f.subst u - g.subst v := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  simp only [map_sub, sub_eq_zero]
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  apply finsum_congr
  intro k
  by_cases hk : k < d
  · rw [coeff_eq_of_dvd hf hk,
      coeff_eq_of_dvd (huv.trans (sub_dvd_pow_sub_pow u v k)) hn]
  · have vanishes (w : PowerSeries R) (hw : constantCoeff w = 0) :
        coeff n (w ^ k) = 0 :=
      X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hw) k) n (by omega)
    rw [vanishes u hu, vanishes v hv, smul_zero, smul_zero]

private theorem iterate_constant (f : PowerSeries R) (h : constantCoeff f = 0) (k : ℕ) :
    constantCoeff (iterate f k) = 0 := by
  induction k with
  | zero => simp [iterate]
  | succ k ih => exact constantCoeff_subst_eq_zero h _ ih

private theorem iterate_congr {f g : PowerSeries R} {d : ℕ}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : (X : PowerSeries R) ^ d ∣ f - g) (k : ℕ) :
    (X : PowerSeries R) ^ d ∣ iterate f k - iterate g k := by
  induction k with
  | zero => simp [iterate]
  | succ k ih => exact subst_congr hf hg ih h

-- Both factors vanish at zero, so their product improves agreement by one degree.
private theorem product_contract {f g : PowerSeries R} {d : ℕ}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : (X : PowerSeries R) ^ d ∣ f - g) :
    (X : PowerSeries R) ^ (d + 1) ∣
      (X + iterate f 2 * iterate f 3) - (X + iterate g 2 * iterate g 3) := by
  have hp := mul_dvd_mul (iterate_congr hf hg h 2)
    (X_dvd_iff.mpr (iterate_constant f hf 3))
  have hq := mul_dvd_mul (iterate_congr hf hg h 3)
    (X_dvd_iff.mpr (iterate_constant g hg 2))
  rw [← pow_succ] at hp hq
  convert dvd_add hp hq using 1
  ring

private noncomputable def step (f : PowerSeries R) : PowerSeries R :=
  X + iterate f 2 * iterate f 3

private theorem step_constant {f : PowerSeries R} (h : constantCoeff f = 0) :
    constantCoeff (step f) = 0 := by
  simp [step, iterate_constant f h]

private theorem unique {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hff : f = step f) (hgg : g = step g) : f = g := by
  have hd : ∀ d : ℕ, (X : PowerSeries R) ^ d ∣ f - g := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have h := product_contract hf hg ih
      change (X : PowerSeries R) ^ (d + 1) ∣ step f - step g at h
      simpa only [← hff, ← hgg] using h
  ext n
  exact coeff_eq_of_dvd (hd (n + 1)) (Nat.lt_succ_self n)

private noncomputable def approx (d : ℕ) : PowerSeries R := step^[d] 0

private theorem approx_succ (d : ℕ) :
    approx (R := R) (d + 1) = step (approx d) :=
  Function.iterate_succ_apply' step d 0

private theorem approx_constant (d : ℕ) : constantCoeff (approx (R := R) d) = 0 := by
  induction d with
  | zero => simp [approx]
  | succ d ih => rw [approx_succ]; exact step_constant ih

private theorem approx_stable {d e : ℕ} (h : d ≤ e) :
    (X : PowerSeries R) ^ d ∣ approx d - approx e := by
  induction d generalizing e with
  | zero => simp
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      rw [approx_succ, approx_succ]
      exact product_contract (approx_constant d) (approx_constant e) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approx (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_approx (d : ℕ) :
    (X : PowerSeries ℤ) ^ d ∣ generatingSeries - approx d := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  simp only [map_sub, sub_eq_zero, generatingSeries, coeff_mk, a]
  exact coeff_eq_of_dvd (approx_stable (by omega : n + 1 ≤ d)) (Nat.lt_succ_self n)

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries = X + iterate generatingSeries 2 * iterate generatingSeries 3 := by
  have hz : constantCoeff generatingSeries = 0 := by
    rw [← coeff_zero_eq_constantCoeff,
      coeff_eq_of_dvd (generating_approx 1) (by omega : 0 < 1), coeff_zero_eq_constantCoeff]
    exact approx_constant 1
  have he : generatingSeries = step generatingSeries := by
    ext n
    have h := coeff_eq_of_dvd (generating_approx (n + 2)) (by omega : n < n + 2)
    rw [approx_succ] at h
    exact h.trans (coeff_eq_of_dvd
      (product_contract hz (approx_constant (n + 1)) (generating_approx (n + 1)))
      (by omega : n < n + 1 + 1)).symm
  refine ⟨hz, ?_, he⟩
  have hc := congrArg (coeff 1) he
  simpa [step, coeff_one_mul, iterate_constant generatingSeries hz] using hc

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 0)
    (hB : B = X + iterate B 2 * iterate B 3) : B = generatingSeries :=
  unique h0 generating_equation.1 hB generating_equation.2.2

private theorem map_iterates {S : Type*} [CommRing S] (hom : R →+* S)
    {f : PowerSeries R} (hf : constantCoeff f = 0) (k : ℕ) :
    (iterate f k).map hom = iterate (f.map hom) k := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    calc
      (iterate f (k + 1)).map hom =
          ((iterate f k).map hom).subst (f.map hom) :=
        map_subst (.of_constantCoeff_zero hf) _
      _ = iterate (f.map hom) (k + 1) := by rw [ih]; rfl

private abbrev S := PowerSeries (ZMod 4)

private noncomputable def den (x : S) := (1 - x) * (1 + x ^ 2)

private noncomputable def num (x : S) := x + x ^ 3 + 2 * x ^ 4

private noncomputable def f : S := num X * invOfUnit (den X) 1

private theorem f_zero : constantCoeff f = 0 := by simp [f, num]

private theorem f_den : f * den X = num X := by
  rw [f, mul_assoc, invOfUnit_mul _ _ (by simp [den]), mul_one]

private theorem den_unit (x : S) (hx : constantCoeff x = 0) : IsUnit (den x) := by
  rw [isUnit_iff_constantCoeff]
  simp [den, hx]

private theorem compose_den : f.subst f * den f = num f := by
  have h : HasSubst f := .of_constantCoeff_zero f_zero
  have he := congrArg (subst f) f_den
  have h1 : (1 : S).subst f = 1 := by rw [← coe_substAlgHom h]; exact map_one _
  have h2 : (2 : S).subst f = 2 := by rw [← coe_substAlgHom h]; exact map_ofNat _ 2
  simpa only [den, num, subst_mul h, subst_sub h, subst_add h, subst_pow h,
    subst_X h, h1, h2] using he

-- Clearing four powers of the unit denominator turns composition into this identity.
private theorem polynomial_identity (x : S) :
    (x + 2 * x ^ 2) * ((den x) ^ 4 - num x * (den x) ^ 3 + (num x) ^ 2 * (den x) ^ 2 -
      (num x) ^ 3 * den x) = num x * (den x) ^ 3 + (num x) ^ 3 * den x + 2 * (num x) ^ 4 := by
  dsimp [den, num]
  apply sub_eq_zero.mp
  ring_nf
  simp only [← map_ofNat C]
  reduce_mod_char
  simp

private theorem f_two : f.subst f = X + 2 * X ^ 2 := by
  apply (den_unit f f_zero).mul_right_cancel
  rw [compose_den]
  apply ((den_unit X (by simp)).pow 4).mul_right_cancel
  calc
    num f * den X ^ 4 = num X * den X ^ 3 + num X ^ 3 * den X + 2 * num X ^ 4 := by
      calc
        _ = (f * den X) * den X ^ 3 + (f * den X) ^ 3 * den X +
            2 * (f * den X) ^ 4 := by dsimp [num]; ring
        _ = _ := by rw [f_den]
    _ = (X + 2 * X ^ 2) * (den X ^ 4 - num X * den X ^ 3 +
        num X ^ 2 * den X ^ 2 - num X ^ 3 * den X) := (polynomial_identity X).symm
    _ = ((X + 2 * X ^ 2) * den f) * den X ^ 4 := by
      rw [← f_den]
      dsimp [den]
      ring

private theorem fixed_poly (x : S) :
    num x * den x = x * den x ^ 2 + (x + 2 * x ^ 2) * (num x * den x + 2 * num x ^ 2) := by
  dsimp [den,num]
  apply sub_eq_zero.mp
  ring_nf
  simp only [← map_ofNat C]
  reduce_mod_char
  simp

private theorem f_fixed : f = X + (X + 2 * X ^ 2) * (f + 2 * f ^ 2) := by
  apply ((den_unit X (by simp)).pow 2).mul_right_cancel
  calc
    f * den X ^ 2 = num X * den X := by rw [pow_two, ← mul_assoc, f_den]
    _ = X * den X ^ 2 + (X + 2 * X ^ 2) * (num X * den X + 2 * num X ^ 2) := fixed_poly X
    _ = (X + (X + 2 * X ^ 2) * (f + 2 * f ^ 2)) * den X ^ 2 := by rw [← f_den]; ring

private theorem shift_poly (x : S) :
    (num x * den x - x * (num x * den x + 2 * num x ^ 2)) * (1 - x) =
      (x * (1 - x) + 2 * x ^ 3) * den x ^ 2 := by
  dsimp [den,num]
  apply sub_eq_zero.mp
  ring_nf
  simp only [← map_ofNat C]
  reduce_mod_char
  simp

private theorem f_shift : f - X * (f + 2 * f ^ 2) = X + 2 * X ^ 3 * mk 1 := by
  have hu : IsUnit (1 - X : S) := by rw [isUnit_iff_constantCoeff]; simp
  apply hu.mul_right_cancel
  have hgeom : (mk 1 : S) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one _
  have hr : (X + 2 * X ^ 3 * mk 1 : S) * (1 - X) = X * (1 - X) + 2 * X ^ 3 := by
    rw [add_mul, mul_assoc, hgeom, mul_one]
  rw [hr]
  apply ((den_unit X (by simp)).pow 2).mul_right_cancel
  calc
    ((f - X * (f + 2 * f ^ 2)) * (1 - X)) * den X ^ 2 =
        (num X * den X - X * (num X * den X + 2 * num X ^ 2)) * (1 - X) := by
      rw [← f_den]; ring
    _ = _ := shift_poly X

-- The reciprocal denominator is (1 + X)/(1 - X^4), exposing periodic support.
private theorem f_explicit : f = X * mk 1 + 2 * X ^ 4 * ((1 + X) * (mk 1 : S).subst (X ^ 4)) := by
  have hgeom : (mk 1 : S) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one _
  have hs : HasSubst ((X : S) ^ 4) := .X_pow (by omega)
  have h1 : (1: S).subst ((X: S) ^ 4) = 1 := by rw [← coe_substAlgHom hs]; exact map_one _
  have h4 : (mk 1 : S).subst ((X: S) ^ 4) * (1 - X ^ 4) = 1 := by
    have he : ((mk 1 : S) * (1 - X)).subst ((X: S) ^ 4) = (1: S).subst ((X: S) ^ 4) :=
      congrArg (subst ((X: S) ^ 4)) hgeom
    rw [subst_mul hs, subst_sub hs, subst_X hs, h1] at he
    exact he
  apply (den_unit X (by simp)).mul_right_cancel
  rw [f_den]
  calc
    num X = X * (1 + X ^ 2) + 2 * X ^ 4 := by dsimp [num]; ring
    _ = X * ((mk 1 : S) * (1 - X)) * (1 + X ^ 2) + 2 * X ^ 4 * ((mk 1: S).subst (X ^ 4) * (1 - X ^ 4)) := by
      rw [hgeom, h4]; ring
    _ = _ := by dsimp [den]; ring

private theorem f_rational : f =
    mobius (1 : ZMod 4) +
      2 * X ^ 4 * invOfUnit ((1 - X) * (1 + X ^ 2) : S) 1 := by
  change f = mobius 1 +
    2 * X ^ 4 * invOfUnit (den X) 1
  have hgeom : (mk 1 : S) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one _
  apply (den_unit X (by simp)).mul_right_cancel
  rw [f_den, add_mul, mul_assoc, invOfUnit_mul _ _ (by simp [den])]
  simp only [mobius,
    rescale_one, mul_one]
  calc
    num X = X * (1 + X ^ 2) + 2 * X ^ 4 := by dsimp [num]; ring
    _ = X * ((mk 1 : S) * (1 - X)) * (1 + X ^ 2) + 2 * X ^ 4 := by rw [hgeom]; ring
    _ = _ := by dsimp [den]; ring

private theorem f_coeff (n : ℕ) (hn : 2 < n) :
    coeff n f = if n % 4 = 3 ∨ n % 4 = 2 then 1 else 3 := by
  rw [f_explicit]
  have htwo : (2: S) = C 2 := (map_ofNat C 2).symm
  have hm (k : ℕ) : coeff k ((mk 1 : S).subst ((X: S) ^ 4)) = if 4 ∣ k then 1 else 0 := by
    simp [coeff_subst_X_pow (by omega : 4 ≠ 0)]
  have hc : coeff n (X * mk 1 : S) = 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp
  rw [map_add, hc, mul_assoc, htwo, coeff_C_mul]
  by_cases h4 : n < 4
  · have hn3 : n = 3 := by omega
    subst n
    simp [coeff_X_pow_mul']
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 4 ≤ n)
    rw [coeff_X_pow_mul', if_pos (by omega : 4 ≤ 4 + k)]
    simp only [Nat.add_sub_cancel_left, add_mul, one_mul, map_add]
    cases k with
    | zero => simp [hm]; decide
    | succ k =>
      simp only [coeff_succ_X_mul, hm]
      simp only [Nat.dvd_iff_mod_eq_zero]
      have hr : k % 4 < 4 := Nat.mod_lt _ (by omega)
      have hh : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
      rcases hh with h | h | h | h <;>
        simp [Nat.add_mod, h] <;> decide

private theorem f_iter_two : iterate f 2 = X + 2 * X ^ 2 := by
  simpa only [iterate, subst_X (.of_constantCoeff_zero f_zero)] using f_two

private theorem f_iter_three : iterate f 3 = f + 2 * f ^ 2 := by
  have hs : HasSubst f := .of_constantCoeff_zero f_zero
  have htwo : (2 : S).subst f = 2 := by
    rw [← coe_substAlgHom hs]
    exact map_ofNat _ 2
  change (iterate f 2).subst f = _
  rw [f_iter_two, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, htwo]

theorem mod_four_identity : generatingSeries.map (Int.castRingHom (ZMod 4)) =
    mobius (1 : ZMod 4) + 2 * X ^ 4 *
      invOfUnit ((1 - X) * (1 + X ^ 2) : PowerSeries (ZMod 4)) 1 := by
  let hom := Int.castRingHom (ZMod 4)
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have he : generatingSeries.map hom = step (generatingSeries.map hom) := by
    have h := congrArg (PowerSeries.map hom) generating_equation.2.2
    simpa [step, map_iterates hom generating_equation.1] using h
  have hf : f = step f := by
    simpa only [step, f_iter_two, f_iter_three] using f_fixed
  exact (unique hz f_zero he hf).trans f_rational

private theorem reduction : generatingSeries.map (Int.castRingHom (ZMod 4)) = f :=
  mod_four_identity.trans f_rational.symm

theorem hanna_conjecture (n : ℕ) (hn : 2 < n) :
    a n % 4 = if n % 4 = 3 ∨ n % 4 = 2 then 1 else 3 := by
  have hc := congrArg (coeff n) reduction
  simp only [coeff_map, generatingSeries, coeff_mk, Int.coe_castRingHom, f_coeff n hn] at hc
  split_ifs at hc ⊢ with hp
  · exact (ZMod.intCast_eq_intCast_iff' (a n) 1 4).mp hc
  · exact (ZMod.intCast_eq_intCast_iff' (a n) 3 4).mp hc

theorem all_odd (n : ℕ) (hn : 1 ≤ n) : Odd (a n) := by
  apply Int.odd_iff.mpr
  by_cases hbig : 2 < n
  · have h := hanna_conjecture n hbig
    split_ifs at h <;> omega
  · have hc := congrArg (coeff n) reduction
    have hf : coeff n f = 1 := by
      rw [f_explicit]
      have htwo : (2 : S) = C 2 := (map_ofNat C 2).symm
      rw [map_add, mul_assoc, htwo, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega)]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      simp
    simp only [coeff_map, generatingSeries, coeff_mk, Int.coe_castRingHom, hf] at hc
    have h := (ZMod.intCast_eq_intCast_iff' (a n) 1 4).mp hc
    omega

theorem iterate_two_mod_four (n : ℕ) (hn : 2 < n) :
    coeff n (iterate generatingSeries 2) % 4 = 0 := by
  have he : (iterate generatingSeries 2).map (Int.castRingHom (ZMod 4)) =
      X + 2 * X ^ 2 := by
    rw [map_iterates _ generating_equation.1, reduction, f_iter_two]
  have hc := congrArg (coeff n) he
  have htwo : (2 : S) = C 2 := (map_ofNat C 2).symm
  simp only [coeff_map, Int.coe_castRingHom, map_add, coeff_X,
    if_neg (by omega : n ≠ 1), htwo, coeff_C_mul, coeff_X_pow,
    if_neg (by omega : n ≠ 2), mul_zero, add_zero] at hc
  exact (ZMod.intCast_eq_intCast_iff' _ 0 4).mp hc

theorem shift_mod_four (n : ℕ) (hn : 2 < n) :
    coeff n (generatingSeries - X * iterate generatingSeries 3) % 4 = 2 := by
  have he : (generatingSeries - X * iterate generatingSeries 3).map
      (Int.castRingHom (ZMod 4)) = X + 2 * X ^ 3 * mk 1 := by
    rw [map_sub, map_mul, map_X, map_iterates _ generating_equation.1,
      reduction, f_iter_three, f_shift]
  have hc := congrArg (coeff n) he
  have htwo : (2 : S) = C 2 := (map_ofNat C 2).symm
  simp only [coeff_map, Int.coe_castRingHom, map_add, coeff_X,
    if_neg (by omega : n ≠ 1), mul_assoc, htwo, coeff_C_mul, coeff_X_pow_mul',
    if_pos (by omega : 3 ≤ n), coeff_mk, Pi.one_apply, mul_one, zero_add] at hc
  exact (ZMod.intCast_eq_intCast_iff' _ 2 4).mp hc

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_four_identity
#print axioms all_odd
#print axioms hanna_conjecture
#print axioms iterate_two_mod_four
#print axioms shift_mod_four

end D5.S1.Recurrence.Parity.IterateProductTwoThreeModFour
