/- GID: D5/S1/Recurrence/Parity/CompositionalSquareAllOddCoefficients
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/CompositionalSquareAllOddCoefficients
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Characteristic-two uniqueness and an all-one solution prove Hanna A396843. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

open PowerSeries

namespace D5.S1.Recurrence.Parity.CompositionalSquareAllOddCoefficients

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_mono {d e : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (he : e ≤ d) : Agree e f g :=
  fun n hn => h n (lt_of_lt_of_le hn he)

private theorem agree_add {d : ℕ} {f g u v : PowerSeries R}
    (h : Agree d f g) (h' : Agree d u v) : Agree d (f + u) (g + v) := by
  intro n hn
  simp only [map_add, h n hn, h' n hn]

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans
    (sub_dvd_pow_sub_pow f g k))

private theorem agree_X {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) : Agree (d + 1) (X * f) (X * g) := by
  intro n hn
  cases n with
  | zero => simp
  | succ n => simpa using h n (by omega)

private theorem pow_low {f : PowerSeries R} (hf : constantCoeff f = 0)
    {n k : ℕ} (hn : n < k) : coeff n (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) k) n hn

private noncomputable def inner (f : PowerSeries R) : PowerSeries R :=
  X * (f + f ^ 2)

private theorem inner_zero (f : PowerSeries R) : constantCoeff (inner f) = 0 := by
  simp [inner]

private theorem inner_order {f : PowerSeries R} (hf : constantCoeff f = 0) :
    (X : PowerSeries R) ^ 2 ∣ inner f := by
  obtain ⟨u, rfl⟩ := X_dvd_iff.mpr hf
  refine ⟨u + X * u ^ 2, ?_⟩
  dsimp [inner]
  ring

private theorem square_agree {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) : Agree (d + 1) (f ^ 2) (g ^ 2) := by
  apply (agree_iff _ _ _).mpr
  have hd := (agree_iff _ _ _).mp h
  have hz : X ∣ f + g := X_dvd_iff.mpr (by simp [hf, hg])
  have hm := mul_dvd_mul hd hz
  rw [← pow_succ] at hm
  convert hm using 1
  ring

private theorem inner_agree {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) : Agree (d + 1) (inner f) (inner g) :=
  agree_X (agree_add h (agree_mono (square_agree hf hg h) (by omega)))

private theorem inner_top {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) :
    coeff (d + 1) (inner f) - coeff (d + 1) (inner g) =
      coeff d f - coeff d g := by
  simp only [inner, coeff_succ_X_mul, map_add]
  rw [square_agree hf hg h d (by omega)]
  ring

private theorem pow_agree_extra {d k : ℕ} {u v : PowerSeries R}
    (hu : X ^ 2 ∣ u) (hv : X ^ 2 ∣ v) (h : Agree d u v) (hk : 2 ≤ k) :
    Agree (d + 2) (u ^ k) (v ^ k) := by
  apply (agree_iff _ _ _).mpr
  have hd := (agree_iff _ _ _).mp h
  have hu' : X ^ 2 ∣ u ^ (k - 1) :=
    hu.trans (dvd_pow_self u (by omega))
  have hp : X ^ d ∣ u ^ (k - 1) - v ^ (k - 1) :=
    hd.trans (sub_dvd_pow_sub_pow u v (k - 1))
  have hfirst := mul_dvd_mul hd hu'
  have hsecond := mul_dvd_mul hv hp
  have hfirst' : X ^ (d + 2) ∣ (u - v) * u ^ (k - 1) := by
    simpa only [pow_add] using hfirst
  have hsecond' : X ^ (d + 2) ∣ v * (u ^ (k - 1) - v ^ (k - 1)) := by
    rw [show d + 2 = 2 + d by omega, pow_add]
    exact hsecond
  have huk : u ^ k = u * u ^ (k - 1) := by
    calc
      u ^ k = u ^ (1 + (k - 1)) := by congr 1; omega
      _ = u * u ^ (k - 1) := by rw [pow_add, pow_one]
  have hvk : v ^ k = v * v ^ (k - 1) := by
    calc
      v ^ k = v ^ (1 + (k - 1)) := by congr 1; omega
      _ = v * v ^ (k - 1) := by rw [pow_add, pow_one]
  convert dvd_add hfirst' hsecond' using 1
  rw [huk, hvk]
  ring

private theorem subst_inner_top {d : ℕ} {f u v : PowerSeries R}
    (hf1 : coeff 1 f = 1) (hu : X ^ 2 ∣ u) (hv : X ^ 2 ∣ v)
    (h : Agree d u v) :
    coeff d (f.subst u) - coeff d (f.subst v) = coeff d u - coeff d v := by
  have hu0 : constantCoeff u = 0 :=
    X_dvd_iff.mp ((dvd_pow_self X (by omega : 2 ≠ 0)).trans hu)
  have hv0 : constantCoeff v = 0 :=
    X_dvd_iff.mp ((dvd_pow_self X (by omega : 2 ≠ 0)).trans hv)
  rw [coeff_subst' (.of_constantCoeff_zero hu0),
    coeff_subst' (.of_constantCoeff_zero hv0),
    ← finsum_sub_distrib
      (coeff_subst_finite' (.of_constantCoeff_zero hu0) f d)
      (coeff_subst_finite' (.of_constantCoeff_zero hv0) f d)]
  rw [finsum_eq_single _ 1]
  · simp [hf1]
  · intro k hk
    obtain (_ | _ | k) := k
    · simp
    · exact (hk rfl).elim
    · rw [pow_agree_extra hu hv h (by omega) d (by omega)]
      simp

private theorem subst_outer_agree {d : ℕ} {f g u : PowerSeries R}
    (h : Agree d f g) (hu : X ^ 2 ∣ u) :
    Agree (2 * d) (f.subst u) (g.subst u) := by
  have hu0 : constantCoeff u = 0 :=
    X_dvd_iff.mp ((dvd_pow_self X (by omega : 2 ≠ 0)).trans hu)
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hu0),
    coeff_subst' (.of_constantCoeff_zero hu0)]
  apply finsum_congr
  intro k
  by_cases hk : k < d
  · rw [h k hk]
  · have hz : coeff n (u ^ k) = 0 := by
      apply X_pow_dvd_iff.mp (show X ^ (2 * k) ∣ u ^ k by
        simpa only [pow_mul] using pow_dvd_pow_of_dvd hu k)
      omega
    rw [hz, smul_zero, smul_zero]

private theorem composition_top {d : ℕ} {f g : PowerSeries R}
    (hd : 2 ≤ d) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (h : Agree d f g) :
    coeff (d + 1) (f.subst (inner f)) - coeff (d + 1) (g.subst (inner g)) =
      coeff d f - coeff d g := by
  have hi := subst_inner_top hf1 (inner_order hf) (inner_order hg)
    (inner_agree hf hg h)
  have ho := subst_outer_agree h (inner_order hg) (d + 1) (by omega)
  have ht := inner_top hf hg h
  linear_combination hi + ho + ht

private theorem equation_coeff_one {f : PowerSeries (ZMod 2)}
    (hf : constantCoeff f = 0) (he : f.subst (inner f) = X ^ 2) :
    coeff 1 f = 1 := by
  have hc := congrArg (coeff 2) he
  rw [coeff_subst' (.of_constantCoeff_zero (inner_zero f)), finsum_eq_single _ 1] at hc
  · have hi : coeff 2 (inner f) = coeff 1 f := by
      simp only [inner, coeff_succ_X_mul, map_add]
      rw [pow_low hf (by omega : 1 < 2), add_zero]
    rw [pow_one, hi] at hc
    have hrhs : coeff 2 (X ^ 2 : PowerSeries (ZMod 2)) = 1 :=
      coeff_X_pow_self 2
    rw [hrhs] at hc
    calc
      coeff 1 f = (coeff 1 f) ^ 2 := (ZMod.pow_card _).symm
      _ = 1 := by simpa only [smul_eq_mul, pow_two] using hc
  · intro k hk
    obtain (_ | _ | k) := k
    · simp
    · exact (hk rfl).elim
    · have hd : X ^ (2 * (k + 2)) ∣ (inner f) ^ (k + 2) := by
        simpa only [pow_mul] using pow_dvd_pow_of_dvd (inner_order hf) (k + 2)
      have hz : coeff 2 ((inner f) ^ (k + 2)) = 0 :=
        X_pow_dvd_iff.mp hd 2 (by omega)
      rw [hz, smul_zero]

private theorem solution_unique {f g : PowerSeries (ZMod 2)}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (ef : f.subst (inner f) = X ^ 2) (eg : g.subst (inner g) = X ^ 2) :
    f = g := by
  have hf1 := equation_coeff_one hf ef
  have hg1 := equation_coeff_one hg eg
  have hall : ∀ d, Agree (d + 2) f g := by
    intro d
    induction d with
    | zero =>
        intro n hn
        interval_cases n <;> simp_all [coeff_zero_eq_constantCoeff]
    | succ d ih =>
        intro n hn
        by_cases hnd : n < d + 2
        · exact ih n hnd
        · have hn : n = d + 2 := by omega
          subst n
          have ht := composition_top (by omega : 2 ≤ d + 2) hf hg hf1 ih
          rw [ef, eg] at ht
          linear_combination -ht
  ext n
  exact hall n n (by omega)

private instance : CharP (PowerSeries (ZMod 2)) 2 :=
  charP_of_injective_ringHom (f := C) C_injective 2

private noncomputable def allOnes : PowerSeries (ZMod 2) := X * mk 1

private theorem allOnes_zero : constantCoeff allOnes = 0 := by
  simp [allOnes]

private theorem allOnes_relation : allOnes * (1 + X) = X := by
  have hchar : (2 : PowerSeries (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
  have hsign : (1 + X : PowerSeries (ZMod 2)) = 1 - X := by
    linear_combination X * hchar
  rw [allOnes, mul_assoc, hsign, mk_one_mul_one_sub_eq_one, mul_one]

private theorem allOnes_equation : allOnes.subst (inner allOnes) = X ^ 2 := by
  let s := allOnes
  let h := inner s
  have hs : s * (1 + X) = X := allOnes_relation
  have hx : X * (1 + s) = s := by
    have hchar : (2 : PowerSeries (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
    linear_combination -hs + X * s * hchar
  have hh : h = s ^ 2 := by
    calc
      h = X * (s + s ^ 2) := by rfl
      _ = s * (X * (1 + s)) := by ring
      _ = s ^ 2 := by rw [hx]; ring
  have hsubst : s.subst h * (1 + h) = h := by
    have hhs : PowerSeries.HasSubst h := .of_constantCoeff_zero' (by
      simpa only [h] using inner_zero s)
    have hone : (1 : PowerSeries (ZMod 2)).subst h = 1 := by
      rw [← coe_substAlgHom hhs]
      exact map_one _
    have he := congrArg (fun t : PowerSeries (ZMod 2) => t.subst h) hs
    simpa only [subst_mul hhs, subst_add hhs, subst_X hhs, hone] using he
  have hright : X ^ 2 * (1 + h) = h := by
    rw [hh]
    have hsq : (1 + s) ^ 2 = 1 + s ^ 2 := by
      have hchar : (2 : PowerSeries (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
      linear_combination s * hchar
    calc
      X ^ 2 * (1 + s ^ 2) = (X * (1 + s)) ^ 2 := by
        rw [← hsq]
        ring
      _ = s ^ 2 := by rw [hx]
  have hu : IsUnit (1 + h) := by
    rw [isUnit_iff_constantCoeff]
    simp [h, inner]
  change s.subst h = X ^ 2
  apply hu.mul_right_cancel
  calc
    s.subst h * (1 + h) = h := hsubst
    _ = X ^ 2 * (1 + h) := hright.symm

/-- If an integer power series with zero constant coefficient satisfies
`A(x A(x) - 3 x A(x)^2) = x^2`, then every positive-index coefficient is odd. -/
theorem hanna_conjecture (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hEq : A.subst (X * A - 3 * X * A ^ 2) = X ^ 2) :
    ∀ n, 1 ≤ n → Odd (coeff n A) := by
  let hom := Int.castRingHom (ZMod 2)
  let f := PowerSeries.map hom A
  have hf0 : constantCoeff f = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, h0, map_zero]
  have harg : constantCoeff (X * A - 3 * X * A ^ 2) = 0 := by simp
  have hm : PowerSeries.map hom (A.subst (X * A - 3 * X * A ^ 2)) =
      f.subst (PowerSeries.map hom (X * A - 3 * X * A ^ 2)) :=
    map_subst (.of_constantCoeff_zero harg) A
  have he := congrArg (PowerSeries.map hom) hEq
  rw [hm] at he
  have hthree : (3 : PowerSeries (ZMod 2)) = 1 := by
    have hchar : (2 : PowerSeries (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
    linear_combination hchar
  have hfEq : f.subst (inner f) = X ^ 2 := by
    have hmaparg : PowerSeries.map hom (X * A - 3 * X * A ^ 2) = inner f := by
      rw [sub_eq_add_neg]
      simp only [map_add, map_neg, map_mul, map_pow, map_X, map_ofNat, hthree,
        one_mul]
      have hneg : -(X * f ^ 2) = X * f ^ 2 := by
        have hchar : (2 : PowerSeries (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
        rw [neg_eq_iff_add_eq_zero, ← two_mul, hchar, zero_mul]
      rw [hneg]
      dsimp only [inner]
      ring
    have hmaprhs : PowerSeries.map hom (X ^ 2 : PowerSeries ℤ) =
        (X : PowerSeries (ZMod 2)) ^ 2 := by simp
    rw [hmaparg, hmaprhs] at he
    exact he
  have hid : f = allOnes := solution_unique hf0 allOnes_zero hfEq allOnes_equation
  intro n hn
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hc := congrArg (coeff n) hid
  cases n with
  | zero => omega
  | succ n =>
      simpa [f, hom, allOnes] using hc

#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.CompositionalSquareAllOddCoefficients
