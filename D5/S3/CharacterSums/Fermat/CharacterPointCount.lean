/- GID: D5/S3/CharacterSums/Fermat/CharacterPointCount
   generality: G
   mirror-B: D5/B/S3/CharacterSums/Fermat/CharacterPointCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Character sums count actual projective Fermat points with the Weil bound. -/

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! # Finite-field character fibers and Fermat point counts -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CharacterSums.Fermat.CharacterPointCount

open Finset

variable {F : Type*} [Field F] [Fintype F]

local instance : DecidableEq F := Classical.decEq F

def affinePoints (F : Type*) [Field F] (d : ℕ) :=
  {xy : F × F // xy.1 ^ d + xy.2 ^ d = 1}

private theorem unit_mem_power_range_iff (χ : MulChar F ℂ) {d : ℕ}
    (hχ : orderOf χ = d) (u : Fˣ) :
    u ∈ (powMonoidHom d : Fˣ →* Fˣ).range ↔ χ u = 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  let ev : MulChar F ℂ →* ℂˣ :=
    (MonoidHom.eval g).comp MulChar.mulEquivToUnitHom.toMonoidHom
  have hev : Function.Injective ev := by
    intro ψ φ h
    apply (MulChar.eq_iff hg ψ φ).mpr
    change ψ.toUnitHom g = φ.toUnitHom g at h
    exact congrArg (fun z : ℂˣ => (z : ℂ)) h
  have horder : orderOf (χ.toUnitHom g) = d := by
    calc
      _ = orderOf χ := orderOf_injective ev hev χ
      _ = d := hχ
  constructor
  · rintro ⟨v, rfl⟩
    change χ ((v : F) ^ d) = 1
    have hp : χ ^ d = 1 := by
      rw [← hχ]
      exact pow_orderOf_eq_one χ
    calc
      χ ((v : F) ^ d) = χ v ^ d := map_pow χ (v : F) d
      _ = (χ ^ d) v := (χ.pow_apply_coe d v).symm
      _ = 1 := by rw [hp, MulChar.one_apply_coe]
  · intro hu
    obtain ⟨n, rfl⟩ := show u ∈ Submonoid.powers g from
      mem_powers_iff_mem_zpowers.mpr (hg u)
    have hp : (χ.toUnitHom g) ^ n = 1 := by
      rw [← map_pow]
      apply Units.ext
      exact hu
    have hdn : d ∣ n := horder ▸ orderOf_dvd_of_pow_eq_one hp
    obtain ⟨k, hk⟩ := hdn
    refine ⟨g ^ k, ?_⟩
    change (g ^ k) ^ d = g ^ n
    rw [← pow_mul, hk, Nat.mul_comm k d]

theorem character_kernel_eq_power_image (χ : MulChar F ℂ) {d : ℕ}
    (hχ : orderOf χ = d) :
    χ.toUnitHom.ker = (powMonoidHom d : Fˣ →* Fˣ).range := by
  ext u
  constructor
  · intro hu
    apply (unit_mem_power_range_iff χ hχ u).mpr
    exact congrArg (fun z : ℂˣ => (z : ℂ)) hu
  · intro hu
    apply Units.ext
    exact (unit_mem_power_range_iff χ hχ u).mp hu

private theorem character_eq_one_iff_exists_power (χ : MulChar F ℂ) {d : ℕ}
    (hd : 0 < d) (hχ : orderOf χ = d) {a : F} (ha : a ≠ 0) :
    χ a = 1 ↔ ∃ x : F, x ^ d = a := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (unit_mem_power_range_iff χ hχ (Units.mk0 a ha)).mpr h
    exact ⟨u, congrArg (fun z : Fˣ => (z : F)) hu⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, zero_pow hd.ne'] at hx
      exact ha hx.symm
    apply (unit_mem_power_range_iff χ hχ (Units.mk0 a ha)).mp
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩

private theorem power_fiber_card_zero {d : ℕ} (hd : 0 < d) :
    Nat.card {x : F // x ^ d = 0} = 1 := by
  letI : Unique {x : F // x ^ d = 0} :=
    { default := ⟨0, zero_pow hd.ne'⟩
      uniq := by
        intro x
        apply Subtype.ext
        exact (pow_eq_zero_iff hd.ne').mp x.property }
  exact Nat.card_unique

private theorem power_fiber_card_of_character_eq_one (χ : MulChar F ℂ) {d : ℕ}
    (hd : 0 < d) (hχ : orderOf χ = d) {a : F} (ha : a ≠ 0) (hχa : χ a = 1) :
    Nat.card {x : F // x ^ d = a} = d := by
  classical
  let au : Fˣ := Units.mk0 a ha
  let f : Fˣ →* Fˣ := powMonoidHom d
  let e : {x : F // x ^ d = a} ≃ {u : Fˣ // u ^ d = au} :=
    { toFun := fun x =>
        ⟨Units.mk0 x.val (by
          intro hx
          have h := x.property
          rw [hx, zero_pow hd.ne'] at h
          exact ha h.symm), Units.ext x.property⟩
      invFun := fun u => ⟨u.val.val, congrArg (fun z : Fˣ => (z : F)) u.property⟩
      left_inv := by intro x; rfl
      right_inv := by
        intro u
        apply Subtype.ext
        apply Units.ext
        rfl }
  obtain ⟨u, hu⟩ := (unit_mem_power_range_iff χ hχ au).mpr hχa
  have hcard : Nat.card {v : Fˣ // v ^ d = au} = Nat.card f.ker := by
    rw [← hu]
    exact Nat.card_congr (f.fiberEquivKer u)
  have hdiv : d ∣ Nat.card Fˣ := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units, hχ] using
      MulChar.orderOf_dvd_card_sub_one F χ
  calc
    Nat.card {x : F // x ^ d = a} = Nat.card {v : Fˣ // v ^ d = au} :=
      Nat.card_congr e
    _ = Nat.card f.ker := hcard
    _ = d := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdiv]

private theorem power_fiber_card_piecewise (χ : MulChar F ℂ) {d : ℕ}
    (hd : 0 < d) (hχ : orderOf χ = d) (a : F) :
    Nat.card {x : F // x ^ d = a} =
      if a = 0 then 1 else if χ a = 1 then d else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simpa using (power_fiber_card_zero (F := F) hd)
  · by_cases hχa : χ a = 1
    · simpa [ha, hχa] using power_fiber_card_of_character_eq_one χ hd hχ ha hχa
    · letI : IsEmpty {x : F // x ^ d = a} :=
        ⟨fun x => hχa ((character_eq_one_iff_exists_power χ hd hχ ha).mpr
          ⟨x.val, x.property⟩)⟩
      simp [ha, hχa]

private theorem sum_character_powers_nonzero (χ : MulChar F ℂ) {d : ℕ}
    (hχ : orderOf χ = d) {a : F} (ha : a ≠ 0) :
    (∑ i ∈ range d, (χ ^ i) a) = if χ a = 1 then (d : ℂ) else 0 := by
  have hterm (i : ℕ) : (χ ^ i) a = χ a ^ i :=
    χ.pow_apply_coe i (Units.mk0 a ha)
  simp_rw [hterm]
  by_cases hχa : χ a = 1
  · simp [hχa]
  · have hp : χ ^ d = 1 := by
      rw [← hχ]
      exact pow_orderOf_eq_one χ
    have hpow : χ a ^ d = 1 := by
      calc
        χ a ^ d = (χ ^ d) (Units.mk0 a ha) :=
          (χ.pow_apply_coe d (Units.mk0 a ha)).symm
        _ = 1 := by rw [hp, MulChar.one_apply_coe]
    rw [if_neg hχa, geom_sum_eq hχa d, hpow, sub_self, zero_div]

theorem power_fiber_card_eq_character_sum (χ : MulChar F ℂ) {d : ℕ}
    (hd : 0 < d) (hχ : orderOf χ = d) (a : F) :
    (Nat.card {x : F // x ^ d = a} : ℂ) =
      (if a = 0 then 1 else 0) + ∑ i ∈ range d, (χ ^ i) a := by
  classical
  rw [power_fiber_card_piecewise χ hd hχ a]
  by_cases ha : a = 0
  · simp [ha, MulChar.map_zero]
  · rw [if_neg ha, if_neg ha, zero_add,
      sum_character_powers_nonzero χ hχ ha]
    by_cases hχa : χ a = 1 <;> simp [hχa]

theorem power_fiber_card_eq_one_add_character_sum (χ : MulChar F ℂ) {d : ℕ}
    (hd : 0 < d) (hχ : orderOf χ = d) (a : F) :
    (Nat.card {x : F // x ^ d = a} : ℂ) =
      1 + ∑ i ∈ Ico 1 d, (χ ^ i) a := by
  classical
  rw [power_fiber_card_eq_character_sum χ hd hχ a,
    Finset.sum_Ico_eq_sub _ hd]
  simp only [Finset.sum_range_one, pow_zero]
  have hzero : (if a = 0 then (1 : ℂ) else 0) + (1 : MulChar F ℂ) a = 1 := by
    by_cases ha : a = 0
    · simp [ha, MulChar.map_zero]
    · simpa [ha] using (MulChar.one_apply (isUnit_iff_ne_zero.mpr ha))
  calc
    _ = ((if a = 0 then (1 : ℂ) else 0) + (1 : MulChar F ℂ) a) +
        ((∑ i ∈ range d, (χ ^ i) a) - (1 : MulChar F ℂ) a) := by ring
    _ = _ := by rw [hzero]

section AffineFibers

variable {d : ℕ}

/-- Record the actual first-coordinate power of an affine Fermat point. -/
def affinePowerFiberEquiv :
    affinePoints F d ≃
      Σ t : F, {x : F // x ^ d = t} × {y : F // y ^ d = 1 - t} where
  toFun P :=
    ⟨P.1.1 ^ d, ⟨P.1.1, rfl⟩, ⟨P.1.2, by
      apply (eq_sub_iff_add_eq).2
      simpa [add_comm] using P.2⟩⟩
  invFun P :=
    ⟨(P.2.1.1, P.2.2.1), by
      rw [P.2.1.2, P.2.2.2]
      ring⟩
  left_inv P := by
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨t, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩
    subst t
    rfl

/-- Count affine points by their common power value `t = x^d`. -/
theorem affine_card_eq_sum_power_fibers :
    Nat.card (affinePoints F d) =
      ∑ t : F,
        Nat.card {x : F // x ^ d = t} * Nat.card {y : F // y ^ d = 1 - t} := by
  calc
    Nat.card (affinePoints F d) =
        Nat.card (Σ t : F, {x : F // x ^ d = t} × {y : F // y ^ d = 1 - t}) :=
      Nat.card_congr (affinePowerFiberEquiv (F := F) (d := d))
    _ = ∑ t : F,
        Nat.card ({x : F // x ^ d = t} × {y : F // y ^ d = 1 - t}) :=
      Nat.card_sigma
    _ = ∑ t : F,
        Nat.card {x : F // x ^ d = t} * Nat.card {y : F // y ^ d = 1 - t} := by
      simp only [Nat.card_prod]

/-- The same decomposition after the natural point counts are cast into a semiring. -/
theorem affine_card_cast_eq_sum_power_fibers
    (K : Type*) [Semiring K] :
    (Nat.card (affinePoints F d) : K) =
      ∑ t : F,
        (Nat.card {x : F // x ^ d = t} : K) *
          (Nat.card {y : F // y ^ d = 1 - t} : K) := by
  simpa only [Nat.cast_sum, Nat.cast_mul] using
    congrArg (fun n : ℕ => (n : K))
      (affine_card_eq_sum_power_fibers (F := F) (d := d))

end AffineFibers

theorem affine_point_count (χ : MulChar F ℂ) {d : ℕ}
    (hd : 0 < d) (hχ : orderOf χ = d) :
    (Nat.card (affinePoints F d) : ℂ) = (Fintype.card F : ℂ) +
      ∑ i ∈ Ico 1 d, ∑ j ∈ Ico 1 d, jacobiSum (χ ^ i) (χ ^ j) := by
  classical
  have hnontrivial (i : ℕ) (hi : i ∈ Ico 1 d) : χ ^ i ≠ 1 := by
    have hi0 : 0 < i := lt_of_lt_of_le Nat.zero_lt_one (mem_Ico.mp hi).1
    exact pow_ne_one_of_lt_orderOf hi0.ne' (by simpa only [hχ] using (mem_Ico.mp hi).2)
  have hsum (i : ℕ) (hi : i ∈ Ico 1 d) : ∑ t : F, (χ ^ i) t = 0 :=
    MulChar.sum_eq_zero_of_ne_one (hnontrivial i hi)
  have hsub (i : ℕ) (hi : i ∈ Ico 1 d) : ∑ t : F, (χ ^ i) (1 - t) = 0 := by
    calc
      _ = ∑ t : F, (χ ^ i) t := by
        simpa only [Equiv.subLeft_apply] using
          (Equiv.subLeft (1 : F)).sum_comp (fun t => (χ ^ i) t)
      _ = 0 := hsum i hi
  have hleft : (∑ t : F, ∑ i ∈ Ico 1 d, (χ ^ i) t) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i hi => hsum i hi
  have hright : (∑ t : F, ∑ j ∈ Ico 1 d, (χ ^ j) (1 - t)) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun j hj => hsub j hj
  have hjacobi :
      (∑ t : F, ∑ i ∈ Ico 1 d, ∑ j ∈ Ico 1 d,
        (χ ^ i) t * (χ ^ j) (1 - t)) =
      ∑ i ∈ Ico 1 d, ∑ j ∈ Ico 1 d, jacobiSum (χ ^ i) (χ ^ j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    rfl
  rw [affine_card_cast_eq_sum_power_fibers (F := F) (d := d) ℂ]
  simp_rw [power_fiber_card_eq_one_add_character_sum χ hd hχ]
  have hexpand (t : F) :
      (1 + ∑ i ∈ Ico 1 d, (χ ^ i) t) *
        (1 + ∑ j ∈ Ico 1 d, (χ ^ j) (1 - t)) =
      1 + (∑ i ∈ Ico 1 d, (χ ^ i) t) +
        (∑ j ∈ Ico 1 d, (χ ^ j) (1 - t)) +
        ∑ i ∈ Ico 1 d, ∑ j ∈ Ico 1 d, (χ ^ i) t * (χ ^ j) (1 - t) := by
    rw [← Finset.sum_mul_sum]
    ring
  simp_rw [hexpand, Finset.sum_add_distrib]
  rw [hleft, hright, hjacobi]
  simp

end D5.S3.CharacterSums.Fermat.CharacterPointCount


/- The projective carrier is defined in the actual projective plane.
The hypothesis d is nonzero is needed for the infinity chart. -/

noncomputable section

namespace D5.S3.CharacterSums.Fermat.CharacterPointCount

variable {F : Type*} [Field F] {d : ℕ}

def infinityPoints (F : Type*) [Field F] (d : ℕ) :=
  {t : F // t ^ d + 1 = 0}

private def fermatEquation (d : ℕ) (v : Fin 3 → F) : Prop :=
  v 0 ^ d + v 1 ^ d = v 2 ^ d

/-- The Fermat curve as a genuine subset of the projective plane. -/
def projectivePoints (F : Type*) [Field F] (d : ℕ) :=
  {P : Projectivization F (Fin 3 → F) // fermatEquation d P.rep}

private theorem fermatEquation_smul_iff (d : ℕ) (a : F) (ha : a ≠ 0)
    (v : Fin 3 → F) :
    fermatEquation d (a • v) ↔ fermatEquation d v := by
  change (a * v 0) ^ d + (a * v 1) ^ d = (a * v 2) ^ d ↔
    v 0 ^ d + v 1 ^ d = v 2 ^ d
  rw [mul_pow, mul_pow, mul_pow, ← mul_add,
    mul_right_inj' (pow_ne_zero d ha)]

/-- Membership does not depend on the representative selected by `rep`. -/
private theorem fermatEquation_mk_iff (v : Fin 3 → F) (hv : v ≠ 0) :
    fermatEquation d (Projectivization.mk F v hv).rep ↔ fermatEquation d v := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  rw [← ha, Units.smul_def]
  exact fermatEquation_smul_iff d (a : F) a.ne_zero v

private def affineVector (xy : F × F) : Fin 3 → F := ![xy.1, xy.2, 1]

private def infinityVector (t : F) : Fin 3 → F := ![t, 1, 0]

private theorem affineVector_ne_zero (xy : F × F) : affineVector xy ≠ 0 := by
  intro h
  have h2 := congrFun h (2 : Fin 3)
  simpa [affineVector] using h2

private theorem infinityVector_ne_zero (t : F) : infinityVector t ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 3)
  simpa [infinityVector] using h1

def affineToProjective (P : affinePoints F d) : projectivePoints F d :=
  ⟨Projectivization.mk F (affineVector P.1) (affineVector_ne_zero P.1),
    (fermatEquation_mk_iff _ _).2 (by
      simpa [fermatEquation, affineVector] using P.2)⟩

def infinityToProjective (hd : d ≠ 0) (t : infinityPoints F d) :
    projectivePoints F d :=
  ⟨Projectivization.mk F (infinityVector t.1) (infinityVector_ne_zero t.1),
    (fermatEquation_mk_iff _ _).2 (by
      simpa [fermatEquation, infinityVector, zero_pow hd] using t.2)⟩

private theorem affineToProjective_injective :
    Function.Injective (affineToProjective : affinePoints F d → projectivePoints F d) := by
  intro P Q h
  have hp :
      Projectivization.mk F (affineVector P.1) (affineVector_ne_zero P.1) =
      Projectivization.mk F (affineVector Q.1) (affineVector_ne_zero Q.1) :=
    congrArg Subtype.val h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).1 hp
  have ha1 : (a : F) = 1 := by
    have h2 := congrFun ha (2 : Fin 3)
    simpa [affineVector, Units.smul_def, Pi.smul_apply, smul_eq_mul] using h2
  apply Subtype.ext
  apply Prod.ext
  · have h0 := congrFun ha (0 : Fin 3)
    simpa [affineVector, Units.smul_def, Pi.smul_apply, smul_eq_mul, ha1] using h0.symm
  · have h1 := congrFun ha (1 : Fin 3)
    simpa [affineVector, Units.smul_def, Pi.smul_apply, smul_eq_mul, ha1] using h1.symm

private theorem infinityToProjective_injective (hd : d ≠ 0) :
    Function.Injective (infinityToProjective hd : infinityPoints F d → projectivePoints F d) := by
  intro P Q h
  have hp :
      Projectivization.mk F (infinityVector P.1) (infinityVector_ne_zero P.1) =
      Projectivization.mk F (infinityVector Q.1) (infinityVector_ne_zero Q.1) :=
    congrArg Subtype.val h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).1 hp
  have ha1 : (a : F) = 1 := by
    have h1 := congrFun ha (1 : Fin 3)
    simpa [infinityVector, Units.smul_def, Pi.smul_apply, smul_eq_mul] using h1
  apply Subtype.ext
  have h0 := congrFun ha (0 : Fin 3)
  simpa [infinityVector, Units.smul_def, Pi.smul_apply, smul_eq_mul, ha1] using h0.symm

private theorem affineToProjective_ne_infinityToProjective (hd : d ≠ 0)
    (P : affinePoints F d) (Q : infinityPoints F d) :
    affineToProjective P ≠ infinityToProjective hd Q := by
  intro h
  have hp :
      Projectivization.mk F (affineVector P.1) (affineVector_ne_zero P.1) =
      Projectivization.mk F (infinityVector Q.1) (infinityVector_ne_zero Q.1) :=
    congrArg Subtype.val h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).1 hp
  have h2 := congrFun ha (2 : Fin 3)
  simpa [affineVector, infinityVector, Units.smul_def, Pi.smul_apply, smul_eq_mul] using h2

def fromCharts (hd : d ≠ 0) :
    affinePoints F d ⊕ infinityPoints F d → projectivePoints F d :=
  Sum.elim affineToProjective (infinityToProjective hd)

private theorem fromCharts_injective (hd : d ≠ 0) :
    Function.Injective (fromCharts (F := F) hd) := by
  intro P Q h
  cases P with
  | inl P =>
    cases Q with
    | inl Q =>
      change affineToProjective P = affineToProjective Q at h
      exact congrArg Sum.inl (affineToProjective_injective h)
    | inr Q =>
      change affineToProjective P = infinityToProjective hd Q at h
      exact False.elim (affineToProjective_ne_infinityToProjective hd P Q h)
  | inr P =>
    cases Q with
    | inl Q =>
      change infinityToProjective hd P = affineToProjective Q at h
      exact False.elim (affineToProjective_ne_infinityToProjective hd Q P h.symm)
    | inr Q =>
      change infinityToProjective hd P = infinityToProjective hd Q at h
      exact congrArg Sum.inr (infinityToProjective_injective hd h)

private theorem mk_affine_normalization (v : Fin 3 → F) (hv : v ≠ 0) (hz : v 2 ≠ 0) :
    Projectivization.mk F (affineVector (v 0 / v 2, v 1 / v 2))
        (affineVector_ne_zero _) =
      Projectivization.mk F v hv := by
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
  refine ⟨(v 2)⁻¹, ?_⟩
  ext i
  fin_cases i <;>
    simp [affineVector, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, hz]

private theorem mk_infinity_normalization (v : Fin 3 → F) (hv : v ≠ 0)
    (hz : v 2 = 0) (hy : v 1 ≠ 0) :
    Projectivization.mk F (infinityVector (v 0 / v 1)) (infinityVector_ne_zero _) =
      Projectivization.mk F v hv := by
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
  refine ⟨(v 1)⁻¹, ?_⟩
  ext i
  fin_cases i <;>
    simp [infinityVector, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, hz, hy]

private theorem fromCharts_surjective (hd : d ≠ 0) :
    Function.Surjective (fromCharts (F := F) hd) := by
  intro P
  let v : Fin 3 → F := P.1.rep
  have hv : v ≠ 0 := P.1.rep_nonzero
  have heq : v 0 ^ d + v 1 ^ d = v 2 ^ d := P.2
  by_cases hz : v 2 = 0
  · have heq0 : v 0 ^ d + v 1 ^ d = 0 := by
      simpa [hz, zero_pow hd] using heq
    have hy : v 1 ≠ 0 := by
      intro hy
      have hxpow : v 0 ^ d = 0 := by
        simpa [hy, zero_pow hd] using heq0
      have hx : v 0 = 0 := eq_zero_of_pow_eq_zero hxpow
      apply hv
      funext i
      fin_cases i
      · simpa using hx
      · simpa using hy
      · simpa using hz
    have hroot : (v 0 / v 1) ^ d + 1 = 0 := by
      calc
        (v 0 / v 1) ^ d + 1 = (v 0 ^ d + v 1 ^ d) / v 1 ^ d := by
          rw [div_pow, add_div, div_self (pow_ne_zero d hy)]
        _ = 0 := by rw [heq0, zero_div]
    refine ⟨Sum.inr ⟨v 0 / v 1, hroot⟩, ?_⟩
    apply Subtype.ext
    change Projectivization.mk F (infinityVector (v 0 / v 1))
      (infinityVector_ne_zero _) = P.1
    exact (mk_infinity_normalization v hv hz hy).trans (Projectivization.mk_rep P.1)
  · have haff : (v 0 / v 2) ^ d + (v 1 / v 2) ^ d = 1 := by
      rw [div_pow, div_pow, ← add_div, heq, div_self (pow_ne_zero d hz)]
    refine ⟨Sum.inl ⟨(v 0 / v 2, v 1 / v 2), haff⟩, ?_⟩
    apply Subtype.ext
    change Projectivization.mk F (affineVector (v 0 / v 2, v 1 / v 2))
      (affineVector_ne_zero _) = P.1
    exact (mk_affine_normalization v hv hz).trans (Projectivization.mk_rep P.1)

/-- The affine chart and infinity chart exhaust the actual projective Fermat curve. -/
def projectiveChartsEquiv (hd : d ≠ 0) :
    affinePoints F d ⊕ infinityPoints F d ≃ projectivePoints F d :=
  Equiv.ofBijective (fromCharts hd) ⟨fromCharts_injective hd, fromCharts_surjective hd⟩

/-- The projective point count is the affine point count plus the infinity-root count. -/
theorem projective_card_eq_affine_add_infinity [Finite F] (hd : d ≠ 0) :
    Nat.card (projectivePoints F d) =
      Nat.card (affinePoints F d) + Nat.card (infinityPoints F d) := by
  letI : Finite (affinePoints F d) := by
    unfold affinePoints
    infer_instance
  letI : Finite (infinityPoints F d) := by
    unfold infinityPoints
    infer_instance
  calc
    Nat.card (projectivePoints F d) =
        Nat.card (affinePoints F d ⊕ infinityPoints F d) :=
      (Nat.card_congr (projectiveChartsEquiv (F := F) hd)).symm
    _ = Nat.card (affinePoints F d) + Nat.card (infinityPoints F d) := Nat.card_sum

end D5.S3.CharacterSums.Fermat.CharacterPointCount

/- Jacobi-sum norm and exponent helpers used by the projective point-count bound. -/

noncomputable section
open scoped BigOperators
namespace D5.S3.CharacterSums.Fermat.CharacterPointCount

variable {F : Type*} [Field F] [Fintype F]

lemma norm_jacobiSum {χ ψ : MulChar F ℂ}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  classical
  have hs : star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
    simp [jacobiSum, star_mul, MulChar.star_apply', mul_comm]
  have hc : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.ringChar_ne_zero_of_finite F).symm
  have hp := jacobiSum_mul_jacobiSum_inv hc hχ hψ hχψ
  have hn := congrArg norm hp
  rw [← hs, norm_mul, norm_star, Complex.norm_natCast] at hn
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa only [pow_two] using hn

lemma pow_mul_pow_ne_one {χ : MulChar F ℂ} {d i j : ℕ}
    (hd : orderOf χ = d) (hi0 : 1 ≤ i) (hi : i < d)
    (hj0 : 1 ≤ j) (hj : j < d) (hjne : j ≠ d - i) :
    χ ^ i * χ ^ j ≠ 1 := by
  rw [← pow_add]
  by_cases hij : i + j < d
  · apply pow_ne_one_of_lt_orderOf (by omega)
    simpa only [hd] using hij
  · have hpow : χ ^ d = 1 := by
      rw [← hd]
      exact pow_orderOf_eq_one χ
    have heq : χ ^ (i + j) = χ ^ (i + j - d) := by
      calc
        χ ^ (i + j) = χ ^ (d + (i + j - d)) := by congr 1; omega
        _ = χ ^ d * χ ^ (i + j - d) := pow_add _ _ _
        _ = χ ^ (i + j - d) := by rw [hpow, one_mul]
    rw [heq]
    apply pow_ne_one_of_lt_orderOf (by omega)
    rw [hd]
    omega

lemma norm_fermatJacobiError_le (χ : MulChar F ℂ) {d : ℕ}
    (hd2 : 2 ≤ d) (hd : orderOf χ = d) :
    ‖∑ i ∈ Finset.Ico 1 d,
        ∑ j ∈ (Finset.Ico 1 d).erase (d - i), jacobiSum (χ ^ i) (χ ^ j)‖ ≤
      (((d - 1) * (d - 2) : ℕ) : ℝ) * Real.sqrt (Fintype.card F) := by
  classical
  let s := Finset.Ico 1 d
  have ht (i : ℕ) (hi : i ∈ s) (j : ℕ) (hj : j ∈ s.erase (d - i)) :
      ‖jacobiSum (χ ^ i) (χ ^ j)‖ = Real.sqrt (Fintype.card F) := by
    obtain ⟨hi0, hid⟩ := Finset.mem_Ico.mp hi
    obtain ⟨hjne, hj⟩ := Finset.mem_erase.mp hj
    obtain ⟨hj0, hjd⟩ := Finset.mem_Ico.mp hj
    apply norm_jacobiSum
    · apply pow_ne_one_of_lt_orderOf (by omega)
      simpa only [hd] using hid
    · apply pow_ne_one_of_lt_orderOf (by omega)
      simpa only [hd] using hjd
    · exact pow_mul_pow_ne_one hd hi0 hid hj0 hjd hjne
  have hcard (i : ℕ) (hi : i ∈ s) :
      ((s.erase (d - i)).card : ℝ) = ((d - 2 : ℕ) : ℝ) := by
    have hm : d - i ∈ s := by
      simp only [s, Finset.mem_Ico] at hi ⊢
      omega
    rw [Finset.card_erase_of_mem hm]
    simp only [s, Nat.card_Ico]
    congr 1
  change ‖∑ i ∈ s, ∑ j ∈ s.erase (d - i), jacobiSum (χ ^ i) (χ ^ j)‖ ≤ _
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ s.erase (d - i), jacobiSum (χ ^ i) (χ ^ j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s.erase (d - i), ‖jacobiSum (χ ^ i) (χ ^ j)‖ :=
      Finset.sum_le_sum fun i hi => norm_sum_le _ _
    _ = ∑ _i ∈ s, ((d - 2 : ℕ) : ℝ) * Real.sqrt (Fintype.card F) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ∑ _j ∈ s.erase (d - i), Real.sqrt (Fintype.card F) :=
          Finset.sum_congr rfl fun j hj => ht i hi j hj
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [hcard i hi]
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, s, Nat.card_Ico]
      rw [Nat.cast_mul, mul_assoc]

end D5.S3.CharacterSums.Fermat.CharacterPointCount

/- Combine the affine count with the actual infinity chart, then estimate the remaining Jacobi sums. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.CharacterSums.Fermat.CharacterPointCount

variable {F : Type*} [Field F] [Fintype F]

private def infinityPowerFiberEquiv {d : ℕ} :
    infinityPoints F d ≃ {x : F // x ^ d = -1} where
  toFun x := ⟨x.1, by
    have h := congrArg (fun z : F => z - 1) x.2
    simpa using h⟩
  invFun x := ⟨x.1, by
    have h := congrArg (fun z : F => z + 1) x.2
    simpa using h⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem infinity_card_character_sum (χ : MulChar F ℂ) {d : ℕ}
    (hd : 0 < d) (hχ : orderOf χ = d) :
    (Nat.card (infinityPoints F d) : ℂ) =
      1 + ∑ i ∈ Finset.Ico 1 d, (χ ^ i) (-1) := by
  rw [Nat.card_congr (infinityPowerFiberEquiv (F := F) (d := d))]
  exact power_fiber_card_eq_one_add_character_sum χ hd hχ (-1)

private theorem complementary_power_eq_inv (χ : MulChar F ℂ) {d i : ℕ}
    (hχ : orderOf χ = d) (hi : i ∈ Finset.Ico 1 d) :
    χ ^ (d - i) = (χ ^ i)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← pow_add, show d - i + i = d by
    have hi' := Finset.mem_Ico.mp hi
    omega]
  rw [← hχ, pow_orderOf_eq_one]

/-- Exact Jacobi-sum point count of the genuine projective Fermat curve.
The omitted term in each row is precisely the inverse-character pair. -/
theorem projective_point_count (χ : MulChar F ℂ) {d : ℕ}
    (hd : 0 < d) (hχ : orderOf χ = d) :
    (Nat.card (projectivePoints F d) : ℂ) =
      (Fintype.card F : ℂ) + 1 +
        ∑ i ∈ Finset.Ico 1 d,
          ∑ j ∈ (Finset.Ico 1 d).erase (d - i), jacobiSum (χ ^ i) (χ ^ j) := by
  classical
  let s := Finset.Ico 1 d
  have hmem (i : ℕ) (hi : i ∈ s) : d - i ∈ s := by
    simp only [s, Finset.mem_Ico] at hi ⊢
    omega
  have hdiag (i : ℕ) (hi : i ∈ s) :
      jacobiSum (χ ^ i) (χ ^ (d - i)) = -(χ ^ i) (-1) := by
    rw [complementary_power_eq_inv χ hχ hi]
    apply jacobiSum_nontrivial_inv
    apply pow_ne_one_of_lt_orderOf
    · have hi' := Finset.mem_Ico.mp hi
      omega
    · have hi' := (Finset.mem_Ico.mp hi).2
      simpa only [hχ] using hi'
  have hfull :
      (∑ i ∈ s, ∑ j ∈ s, jacobiSum (χ ^ i) (χ ^ j)) =
        (∑ i ∈ s, ∑ j ∈ s.erase (d - i), jacobiSum (χ ^ i) (χ ^ j)) +
          ∑ i ∈ s, -(χ ^ i) (-1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (∑ j ∈ s.erase (d - i), jacobiSum (χ ^ i) (χ ^ j)) +
          jacobiSum (χ ^ i) (χ ^ (d - i)) :=
        (Finset.sum_erase_add s (fun j => jacobiSum (χ ^ i) (χ ^ j)) (hmem i hi)).symm
      _ = _ := by rw [hdiag i hi]
  rw [projective_card_eq_affine_add_infinity (F := F) hd.ne', Nat.cast_add,
    affine_point_count χ hd hχ, infinity_card_character_sum χ hd hχ]
  change (Fintype.card F : ℂ) + (∑ i ∈ s, ∑ j ∈ s, jacobiSum (χ ^ i) (χ ^ j)) +
      (1 + ∑ i ∈ s, (χ ^ i) (-1)) =
    (Fintype.card F : ℂ) + 1 +
      ∑ i ∈ s, ∑ j ∈ s.erase (d - i), jacobiSum (χ ^ i) (χ ^ j)
  rw [hfull, Finset.sum_neg_distrib]
  ring

/-- The degree-d Fermat curve has the expected Weil point-count error.
This bounds the cardinality of the projective subtype, not a synthetic sum. -/
theorem projective_weil_bound {d : ℕ}
    (hd2 : 2 ≤ d) (hdiv : d ∣ Fintype.card F - 1) :
    |(Nat.card (projectivePoints F d) : ℝ) - ((Fintype.card F : ℝ) + 1)| ≤
      (((d - 1) * (d - 2) : ℕ) : ℝ) * Real.sqrt (Fintype.card F) := by
  classical
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf F hdiv
    (Complex.isPrimitiveRoot_exp d (by omega))
  have hc := projective_point_count χ (show 0 < d by omega) hχ
  have hr := congrArg Complex.re hc
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at hr
  have he :
      (Nat.card (projectivePoints F d) : ℝ) - ((Fintype.card F : ℝ) + 1) =
        (∑ i ∈ Finset.Ico 1 d,
          ∑ j ∈ (Finset.Ico 1 d).erase (d - i), jacobiSum (χ ^ i) (χ ^ j)).re := by
    linarith only [hr]
  rw [he]
  exact (Complex.abs_re_le_norm _).trans (norm_fermatJacobiError_le χ hd2 hχ)

end D5.S3.CharacterSums.Fermat.CharacterPointCount
