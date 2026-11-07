/- GID: D5/S3/ArithUnits/MercaQuarticMoments
   generality: G
   mirror-B: D5/B/S3/ArithUnits/MercaQuarticMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral odd coordinates of the actual normalized quartic-character first moment. -/

import D5.S3.ArithUnits.MercaQuarticCharacter
import D5.S3.ArithUnits.MercaPrimeCharacterMoment
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Least representatives of units are positive. Sums here are integer sums of
those representatives, on the actual four ordered kernel cosets. No class
number is defined by a norm or finite sum in this module.
-/

set_option autoImplicit false
open scoped BigOperators Pointwise
noncomputable section

namespace D5.S3.ArithUnits.MercaQuarticMoments

open MercaQuarticCharacter MercaCosetFiberLift MercaPrimeCharacterMoment

/-- The unit represented by two, independently of its multiplicative order. -/
def twoUnit (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : (ZMod r)ˣ :=
  Units.mk0 2 (Ring.two_ne_zero ((ZMod.ringChar_zmod_n r).substr (by omega)))

/-- The literal integer sum of least-positive representatives in `c K`. -/
def sumRep (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) (c : (ZMod r)ˣ) : ℤ :=
  ∑ u ∈ cosetFinset (kernel r hr) c, ((u : ZMod r).val : ℤ)

/-- The quotient is exact at conductors greater than five, as proved below. -/
def coordinate (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) (c : (ZMod r)ˣ) : ℤ :=
  2 * (sumRep r hr c / (r : ℤ)) - ((r - 1) / 4 : ℕ)

/-- Real coordinate, with the source orientation `chi(2)=i`. -/
def realCoordinate (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : ℤ :=
  coordinate r hr 1

/-- Imaginary coordinate, belonging to the coset `2 K`. -/
def imagCoordinate (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : ℤ :=
  coordinate r hr (twoUnit r hr)

/-- The actual first generalized Bernoulli value, on native unit representatives. -/
def bernoulli (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : ℂ :=
  characterMoment r (character r hr) / (r : ℂ)

private lemma coset_card (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (c : (ZMod r)ˣ) : (cosetFinset (kernel r hr) c).card = (r - 1) / 4 := by
  classical
  let e : cosetFinset (kernel r hr) c ≃
      (c • (kernel r hr : Set (ZMod r)ˣ) : Set (ZMod r)ˣ) :=
    Equiv.subtypeEquivRight (fun u => by simp [cosetFinset, mem_leftCoset_iff])
  have h := Nat.card_congr (e.trans (Subgroup.leftCosetEquivSubgroup c))
  rw [(kernel_structure r hr).2.2.2.2.2.1] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

private lemma representative_pos (r : ℕ) [Fact r.Prime] (_hr : r % 8 = 5)
    (u : (ZMod r)ˣ) : 0 < (u : ZMod r).val := by
  have hu : (u : ZMod r) ≠ 0 := Units.ne_zero u
  have hv : (u : ZMod r).val ≠ 0 := by
    intro h
    apply hu
    rw [← ZMod.natCast_zmod_val (u : ZMod r), h, Nat.cast_zero]
  omega

private lemma sumRep_dvd (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) (c : (ZMod r)ˣ) : (r : ℤ) ∣ sumRep r hr c := by
  classical
  let K := kernel r hr
  let C := cosetFinset K c
  have hcard : 1 < Nat.card K := by
    rw [show Nat.card K = (r - 1) / 4 from (kernel_structure r hr).2.2.2.2.2.1]
    omega
  have : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨v, hv⟩ := exists_ne (1 : K)
  have hv' : (v : (ZMod r)ˣ) ≠ 1 := by
    intro h
    exact hv (Subtype.ext h)
  have hmem (u : (ZMod r)ˣ) : u ∈ C ↔ (v : (ZMod r)ˣ) * u ∈ C := by
    simp only [C, cosetFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show c⁻¹ * ((v : (ZMod r)ˣ) * u) =
      (v : (ZMod r)ˣ) * (c⁻¹ * u) by ac_rfl]
    exact (K.mul_mem_cancel_left v.property).symm
  let S : ZMod r := ∑ u ∈ C, (u : ZMod r)
  have hmul : (v.val : ZMod r) * S = S := by
    dsimp only [S]
    rw [Finset.mul_sum]
    exact Finset.sum_equiv (Equiv.mulLeft (v : (ZMod r)ˣ)) hmem
      (fun _ _ => rfl)
  have hzero : S = 0 := by
    have hp : ((v.val : ZMod r) - 1) * S = 0 := by
      rw [sub_mul, one_mul, hmul, sub_self]
    rcases mul_eq_zero.mp hp with h | h
    · exact (hv' (Units.ext (sub_eq_zero.mp h))).elim
    · exact h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa [sumRep, S, C, Int.cast_sum, Int.cast_natCast,
    ZMod.natCast_zmod_val] using hzero

private lemma sumRep_neg (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (c : (ZMod r)ˣ) :
    sumRep r hr (-c) = (r : ℤ) * ((r - 1) / 4 : ℕ) - sumRep r hr c := by
  classical
  have hmem (u : (ZMod r)ˣ) :
      u ∈ cosetFinset (kernel r hr) c ↔ -u ∈ cosetFinset (kernel r hr) (-c) := by
    simp [cosetFinset]
  have heq : (∑ u ∈ cosetFinset (kernel r hr) c,
      (((-u : (ZMod r)ˣ) : ZMod r).val : ℤ)) = sumRep r hr (-c) :=
    Finset.sum_equiv (Equiv.neg (ZMod r)ˣ) hmem (fun _ _ => rfl)
  rw [← heq]
  calc
    _ = ∑ u ∈ cosetFinset (kernel r hr) c, ((r : ℤ) - (u : ZMod r).val) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Units.val_neg, ZMod.neg_val, ite_eq_right (Units.ne_zero u),
        Nat.cast_sub (ZMod.val_le _)]
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, coset_card]
      dsimp [sumRep]
      ring

/-- Exact divisibility and complementation for every coset, and odd nonzero
integral coordinates. Divisibility uses a nonidentity element of the actual
kernel, which is available precisely after excluding conductor five. -/
theorem representative_properties (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) :
    (∀ u : (ZMod r)ˣ, 0 < (u : ZMod r).val ∧ (u : ZMod r).val < r) ∧
    ∀ c : (ZMod r)ˣ,
      (r : ℤ) ∣ sumRep r hr c ∧
      sumRep r hr (-c) = (r : ℤ) * ((r - 1) / 4 : ℕ) - sumRep r hr c ∧
      Odd (coordinate r hr c) ∧ coordinate r hr c ≠ 0 := by
  refine ⟨fun u => ⟨representative_pos r hr u, ZMod.val_lt _⟩, ?_⟩
  intro c
  have hm : (r - 1) / 4 % 2 = 1 := by omega
  have hc : Odd (coordinate r hr c) := by
    rw [Int.odd_iff]
    dsimp [coordinate]
    omega
  refine ⟨sumRep_dvd r hr hr5 c, sumRep_neg r hr c, hc, ?_⟩
  intro hz
  rw [hz, Int.odd_iff] at hc
  norm_num at hc

private lemma mem_coset_iff (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (c u : (ZMod r)ˣ) :
    u ∈ cosetFinset (kernel r hr) c ↔ character r hr u = character r hr c := by
  classical
  simp only [cosetFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    kernel, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
    Units.ext_iff, MulChar.coe_toUnitHom]
  exact eq_comm

private lemma fourth_values (z : ℂ) (hz : z ^ 4 = 1) :
    z = 1 ∨ z = Complex.I ∨ z = -1 ∨ z = -Complex.I := by
  have hs : z ^ 2 = 1 ∨ z ^ 2 = -1 :=
    sq_eq_one_iff.mp (by simpa only [← pow_mul] using hz)
  rcases hs with h | h
  · rcases sq_eq_one_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans Complex.I_sq.symm) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

private lemma moment_four_cosets (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    characterMoment r (character r hr) =
      (sumRep r hr 1 : ℂ) + Complex.I * (sumRep r hr (twoUnit r hr) : ℂ) -
      (sumRep r hr (-1) : ℂ) - Complex.I * (sumRep r hr (-twoUnit r hr) : ℂ) := by
  classical
  let f (c u : (ZMod r)ˣ) : ℂ :=
    if u ∈ cosetFinset (kernel r hr) c then ((u : ZMod r).val : ℂ) else 0
  have hf (c : (ZMod r)ˣ) : (∑ u, f c u) = (sumRep r hr c : ℂ) := by
    simp [f, sumRep]
  obtain ⟨horder, htwo, _, hodd, _, _, _, _⟩ := kernel_structure r hr
  have hfour : character r hr ^ 4 = 1 := horder ▸ pow_orderOf_eq_one _
  have htwoU : character r hr (twoUnit r hr) = Complex.I := by
    simpa only [twoUnit, Units.val_mk0] using htwo
  have hnegone : character r hr (-1 : ZMod r) = -1 := hodd
  have hnegtwo : character r hr (-(twoUnit r hr : ZMod r)) =
      -Complex.I := by
    rw [hodd.eval_neg, htwoU]
  calc
    _ = ∑ u : (ZMod r)ˣ,
        (f 1 u + Complex.I * f (twoUnit r hr) u - f (-1) u -
          Complex.I * f (-twoUnit r hr) u) := by
      apply Finset.sum_congr rfl
      intro u _
      have hu : character r hr u ^ 4 = 1 := by
        rw [← MulChar.pow_apply_coe, hfour, MulChar.one_apply_coe]
      rcases fourth_values _ hu with h | h | h | h <;>
        norm_num [f, mem_coset_iff, Units.val_neg, htwoU, hnegone, hnegtwo, h,
          Complex.ext_iff] <;> ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hf]

private lemma coordinate_scaled (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) (c : (ZMod r)ˣ) :
    (r : ℤ) * coordinate r hr c =
      2 * sumRep r hr c - (r : ℤ) * ((r - 1) / 4 : ℕ) := by
  dsimp only [coordinate]
  calc
    _ = 2 * (sumRep r hr c / (r : ℤ) * r) - (r : ℤ) * ((r - 1) / 4 : ℕ) := by ring
    _ = _ := by rw [Int.ediv_mul_cancel (sumRep_dvd r hr hr5 c)]

private lemma bernoulli_interval (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    bernoulli r hr =
      (∑ a ∈ Finset.Icc 1 (r - 1), (a : ℂ) * character r hr (a : ZMod r)) / r := by
  classical
  rw [bernoulli, character_moment_eq_zmod_sum]
  congr 1
  have hsum : (∑ a : ZMod r, (a.val : ℂ) * character r hr a) =
      ∑ a ∈ Finset.range r, (a : ℂ) * character r hr (a : ZMod r) := by
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro a _ b _ hab
      exact ZMod.val_injective r hab
    · intro a ha
      refine ⟨(a : ZMod r), Finset.mem_univ _, ?_⟩
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
    · intro a _
      rw [ZMod.natCast_zmod_val]
  rw [hsum]
  have hset : Finset.range r = insert 0 (Finset.Icc 1 (r - 1)) := by
    ext a
    have hp := (Fact.out : r.Prime).pos
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp

/-- The actual Bernoulli value has odd nonzero integer coordinates in the
ordered cosets `K, 2K, -K, -2K`. The interval expression and the analytic
L-value use the same actual character, not a supplied scalar. -/
theorem bernoulli_coordinates (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (hr5 : 5 < r) :
    let k := realCoordinate r hr
    let t := imagCoordinate r hr
    bernoulli r hr = (k : ℂ) + (t : ℂ) * Complex.I ∧
    Odd k ∧ Odd t ∧ k ≠ 0 ∧ t ≠ 0 ∧
    (k : ℚ) = 2 * (sumRep r hr 1 : ℚ) / r - ((r - 1) / 4 : ℕ) ∧
    (t : ℚ) = 2 * (sumRep r hr (twoUnit r hr) : ℚ) / r - ((r - 1) / 4 : ℕ) ∧
    bernoulli r hr =
      (∑ a ∈ Finset.Icc 1 (r - 1), (a : ℂ) * character r hr (a : ZMod r)) / r ∧
    DirichletCharacter.LFunction (character r hr) 0 = -bernoulli r hr := by
  have hprops := representative_properties r hr hr5
  have hk := coordinate_scaled r hr hr5 1
  have ht := coordinate_scaled r hr hr5 (twoUnit r hr)
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero
  have hB : bernoulli r hr =
      (realCoordinate r hr : ℂ) + (imagCoordinate r hr : ℂ) * Complex.I := by
    apply (div_eq_iff hr0).mpr
    rw [moment_four_cosets, sumRep_neg, sumRep_neg]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    have hkC : (r : ℂ) * (realCoordinate r hr : ℂ) =
        2 * (sumRep r hr 1 : ℂ) - (r : ℂ) * ((r - 1) / 4 : ℕ) := by
      have hc := congrArg (fun z : ℤ => (z : ℂ)) hk
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
        realCoordinate] using hc
    have htC : (r : ℂ) * (imagCoordinate r hr : ℂ) =
        2 * (sumRep r hr (twoUnit r hr) : ℂ) - (r : ℂ) * ((r - 1) / 4 : ℕ) := by
      have hc := congrArg (fun z : ℤ => (z : ℂ)) ht
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
        imagCoordinate] using hc
    calc
      _ = (2 * (sumRep r hr 1 : ℂ) - r * ((r - 1) / 4 : ℕ)) +
          Complex.I * (2 * (sumRep r hr (twoUnit r hr) : ℂ) - r * ((r - 1) / 4 : ℕ)) := by ring
      _ = _ := by rw [← hkC, ← htC]; ring
  have hquot (c : (ZMod r)ˣ) : (coordinate r hr c : ℚ) =
      2 * (sumRep r hr c : ℚ) / r - ((r - 1) / 4 : ℕ) := by
    have hs : (r : ℚ) * (coordinate r hr c : ℚ) =
        2 * (sumRep r hr c : ℚ) - (r : ℚ) * ((r - 1) / 4 : ℕ) := by
      have hc := congrArg (fun z : ℤ => (z : ℚ)) (coordinate_scaled r hr hr5 c)
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast] using hc
    have hrQ : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff hrQ).mpr
    nlinarith [hs]
  have hχne : character r hr ≠ 1 := by
    intro h
    have ho := (kernel_structure r hr).1
    rw [h, orderOf_one] at ho
    norm_num at ho
  refine ⟨hB, (hprops.2 1).2.2.1, (hprops.2 (twoUnit r hr)).2.2.1,
    (hprops.2 1).2.2.2, (hprops.2 (twoUnit r hr)).2.2.2,
    hquot 1, hquot (twoUnit r hr), bernoulli_interval r hr, ?_⟩
  rw [D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum
      r (character r hr) hχne, ← character_moment_eq_zmod_sum]
  simp only [bernoulli, neg_div]

end D5.S3.ArithUnits.MercaQuarticMoments
