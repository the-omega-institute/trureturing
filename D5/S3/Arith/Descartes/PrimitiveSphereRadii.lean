/- GID: D5/S3/Arith/Descartes/PrimitiveSphereRadii
   generality: I
   mirror-B: D5/B/S3/Arith/Descartes/PrimitiveSphereRadii
   mirror-E: none(waiver:symbolic-unbounded-classification)
   anchors: []
   utility: none
   digest: Primitive spherical Descartes radius quadruples have 3-adic orders zero,e,e,e. -/

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Descartes.PrimitiveSphereRadii

open Finset

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The common gcd of the four radii; no pairwise coprimality is required. -/
def gcd4 (r : Fin 4 → ℕ) : ℕ := univ.gcd r

/-- Descartes' equation for four spheres together with a tangent plane. -/
def sphereDescartes (r : Fin 4 → ℕ) : Prop :=
  (∑ i, (1 / r i : ℚ)) ^ 2 = 3 * ∑ i, (1 / r i : ℚ) ^ 2

private def commonMultiple (r : Fin 4 → ℕ) : ℕ := univ.lcm r

private def curvature (r : Fin 4 → ℕ) (i : Fin 4) : ℕ := commonMultiple r / r i

private lemma radius_dvd (r : Fin 4 → ℕ) (i : Fin 4) : r i ∣ commonMultiple r :=
  dvd_lcm (mem_univ i)

private lemma commonMultiple_pos (r : Fin 4 → ℕ) (hpos : ∀ i, 0 < r i) :
    0 < commonMultiple r := by
  exact Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun i _ => (hpos i).ne')

private lemma curvature_pos (r : Fin 4 → ℕ) (hpos : ∀ i, 0 < r i) (i : Fin 4) :
    0 < curvature r i :=
  Nat.div_pos (Nat.le_of_dvd (commonMultiple_pos r hpos) (radius_dvd r i)) (hpos i)

private lemma curvature_mul_radius (r : Fin 4 → ℕ) (i : Fin 4) :
    curvature r i * r i = commonMultiple r := Nat.div_mul_cancel (radius_dvd r i)

private lemma curvature_primitive (r : Fin 4 → ℕ) (hpos : ∀ i, 0 < r i) :
    gcd4 (curvature r) = 1 := by
  let d := gcd4 (curvature r)
  have hd (i : Fin 4) : d ∣ curvature r i := gcd_dvd (mem_univ i)
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (hd 0) (curvature_pos r hpos 0)
  have hdL : d ∣ commonMultiple r :=
    (hd 0).trans (Nat.div_dvd_of_dvd (radius_dvd r 0))
  have hsmaller : commonMultiple r ∣ commonMultiple r / d := by
    apply Finset.lcm_dvd
    intro i _
    apply (Nat.dvd_div_iff_mul_dvd hdL).mpr
    simpa only [Nat.mul_comm] using Nat.mul_dvd_of_dvd_div (radius_dvd r i) (hd i)
  have hLpos := commonMultiple_pos r hpos
  have hquotpos := Nat.div_pos (Nat.le_of_dvd hLpos hdL) hdpos
  have hle := Nat.le_of_dvd hquotpos hsmaller
  by_contra hne
  have htwo : 1 < d := by change d ≠ 1 at hne; omega
  have := Nat.div_lt_self hLpos htwo
  omega

private lemma curvature_equation (r : Fin 4 → ℕ) (hpos : ∀ i, 0 < r i)
    (hdesc : sphereDescartes r) :
    (∑ i, curvature r i) ^ 2 = 3 * ∑ i, curvature r i ^ 2 := by
  have hc (i : Fin 4) : (curvature r i : ℚ) = commonMultiple r * (1 / r i : ℚ) := by
    rw [curvature, Nat.cast_div (radius_dvd r i) (by exact_mod_cast (hpos i).ne')]
    ring
  have heq : (∑ i, (curvature r i : ℚ)) ^ 2 =
      3 * ∑ i, (curvature r i : ℚ) ^ 2 := by
    simp_rw [hc, mul_pow]
    rw [← mul_sum, ← mul_sum, mul_pow]
    rw [sphereDescartes] at hdesc
    rw [hdesc]
    ring
  exact_mod_cast heq

private lemma exists_three_unit (b : Fin 4 → ℕ) (hprim : gcd4 b = 1) :
    ∃ i, ¬3 ∣ b i := by
  by_contra! hall
  have hd : 3 ∣ gcd4 b := Finset.dvd_gcd fun i _ => hall i
  rw [hprim] at hd
  norm_num at hd

private lemma curvature_unit_count (b : Fin 4 → ℕ) (hprim : gcd4 b = 1)
    (heq : (∑ i, b i) ^ 2 = 3 * ∑ i, b i ^ 2) :
    (univ.filter fun i => ¬3 ∣ b i).card = 3 := by
  have hsum : 3 ∣ ∑ i, b i :=
    (show Nat.Prime 3 by decide).dvd_of_dvd_pow ⟨∑ i, b i ^ 2, heq⟩
  obtain ⟨k, hk⟩ := hsum
  have hsquares : 3 ∣ ∑ i, b i ^ 2 := ⟨k ^ 2, by nlinarith [heq]⟩
  have hs : (∑ i, (b i : ZMod 3) ^ 2) = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (∑ i, b i ^ 2) 3).mpr hsquares
    simpa only [Nat.cast_sum, Nat.cast_pow] using h
  have hc : ((univ.filter fun i => ¬3 ∣ b i).card : ZMod 3) = 0 := by
    rw [← Finset.sum_boole]
    convert hs using 1
    apply sum_congr rfl
    intro i _
    simpa only [Nat.reduceSub, ne_eq, ZMod.natCast_eq_zero_iff] using
      (ZMod.pow_card_sub_one (b i : ZMod 3)).symm
  have hd := (ZMod.natCast_eq_zero_iff _ 3).mp hc
  have hle : (univ.filter fun i => ¬3 ∣ b i).card ≤ 4 :=
    (card_filter_le _ _).trans (by simp)
  obtain ⟨i, hi⟩ := exists_three_unit b hprim
  have hpos : 0 < (univ.filter fun i => ¬3 ∣ b i).card :=
    card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  omega

/-- In a positive primitive spherical Descartes quadruple, exactly three radii have
the same positive 3-adic order, and the remaining radius has order zero. -/
theorem primitive_sphere_radii_v3 (r : Fin 4 → ℕ)
    (hpos : ∀ i, 0 < r i) (hprim : gcd4 r = 1) (hdesc : sphereDescartes r) :
    ∃ e : ℕ, 0 < e
      ∧ (univ.filter (fun i => padicValNat 3 (r i) = e)).card = 3
      ∧ ∀ i, padicValNat 3 (r i) = 0 ∨ padicValNat 3 (r i) = e := by
  let e := padicValNat 3 (commonMultiple r)
  have hval (i : Fin 4) : padicValNat 3 (curvature r i) + padicValNat 3 (r i) = e := by
    rw [← padicValNat.mul (curvature_pos r hpos i).ne' (hpos i).ne',
      curvature_mul_radius]
  have hunit (i : Fin 4) : ¬3 ∣ curvature r i ↔ padicValNat 3 (r i) = e := by
    rw [dvd_iff_padicValNat_ne_zero (curvature_pos r hpos i).ne', not_not]
    have := hval i
    omega
  have hcount : (univ.filter fun i => padicValNat 3 (r i) = e).card = 3 := by
    have hc := curvature_unit_count (curvature r) (curvature_primitive r hpos)
      (curvature_equation r hpos hdesc)
    simpa only [hunit] using hc
  have he : 0 < e := by
    by_contra h
    have he0 : e = 0 := by omega
    have hall (i : Fin 4) : padicValNat 3 (r i) = e := by
      have := hval i
      omega
    have hfilter : (univ.filter fun i => padicValNat 3 (r i) = e) = univ :=
      filter_eq_self.mpr fun i _ => hall i
    rw [hfilter] at hcount
    norm_num at hcount
  have hother : (univ.filter fun i => ¬padicValNat 3 (r i) = e).card = 1 := by
    have h := card_filter_add_card_filter_not (s := univ)
      (fun i => padicValNat 3 (r i) = e)
    simp only [hcount, card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨j, hj⟩ := card_eq_one.mp hother
  have hindex (i : Fin 4) (hi : padicValNat 3 (r i) ≠ e) : i = j := by
    have hm : i ∈ univ.filter (fun i => ¬padicValNat 3 (r i) = e) :=
      mem_filter.mpr ⟨mem_univ i, hi⟩
    rw [hj] at hm
    exact mem_singleton.mp hm
  obtain ⟨k, hk⟩ := exists_three_unit r hprim
  have hk0 := padicValNat.eq_zero_of_not_dvd hk
  have hkj : k = j := hindex k (by omega)
  refine ⟨e, he, hcount, fun i => ?_⟩
  by_cases hi : padicValNat 3 (r i) = e
  · exact Or.inr hi
  · have hik : i = k := (hindex i hi).trans hkj.symm
    exact Or.inl (hik ▸ hk0)

#print axioms primitive_sphere_radii_v3

end D5.S3.Arith.Descartes.PrimitiveSphereRadii
