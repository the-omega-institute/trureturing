/- GID: D5/S3/CharacterSums/PrimePowerKloostermanStationaryPhase
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact unit-fiber cancellation for the standard additive character at prime powers. -/

import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.ZMod.Units
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Stationary phase for the elementary Kloosterman sum at prime powers

For `e ≥ 2`, the unit digit at modulus `p^(e - e/2)` determines the base phase.
The sum over the remaining `p^(e/2)` digits survives exactly at the solutions
of the quadratic congruence modulo `p^(e/2)`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase

/-- The inverse in `ZMod q` is affine in a square-zero increment at a unit. -/
theorem inv_add_of_sq_zero {q : ℕ} (x d : ZMod q) (hx : IsUnit x) (hd : d ^ 2 = 0) :
    (x + d)⁻¹ = x⁻¹ - d * x⁻¹ ^ 2 := by
  apply ZMod.inv_eq_of_mul_eq_one
  calc
    (x + d) * (x⁻¹ - d * x⁻¹ ^ 2) =
        x * x⁻¹ + d * x⁻¹ * (1 - x * x⁻¹) - d ^ 2 * x⁻¹ ^ 2 := by ring
    _ = 1 := by rw [ZMod.mul_inv_of_unit x hx, hd]; simp

/-- The phase with the usual `exp(2π i t/q)` normalization. -/
def phase {q : ℕ} [NeZero q] (a b x : ZMod q) : ℂ :=
  ZMod.stdAddChar (a * x + b * x⁻¹)

/-- The unnormalized Kloosterman sum with a unit second coefficient. -/
def kloosterman {q : ℕ} [NeZero q] (a : ZMod q) (b : (ZMod q)ˣ) : ℂ :=
  ∑ x : (ZMod q)ˣ, phase a (b : ZMod q) (x : ZMod q)

variable {p : ℕ} [Fact p.Prime]

private instance primeNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

private theorem isUnit_iff_prime_reduction {t : ℕ} (ht : 0 < t) (x : ZMod (p ^ t)) :
    IsUnit x ↔ ZMod.castHom (dvd_pow_self p ht.ne') (ZMod p) x ≠ 0 := by
  obtain ⟨j, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast, ZMod.isUnit_natCast_iff_not_dvd_pow Fact.out ht,
    ne_eq, ZMod.natCast_eq_zero_iff]

section Digits

variable {e m n : ℕ}

private def digitValue (u : ZMod (p ^ m)) (k : ZMod (p ^ n)) : ZMod (p ^ e) :=
  (u.val : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e)) * (k.val : ZMod (p ^ e))

private theorem digitValue_isUnit (hm : 0 < m) (he : 0 < e)
    (u : (ZMod (p ^ m))ˣ) (k : ZMod (p ^ n)) :
    IsUnit (digitValue (e := e) (u : ZMod (p ^ m)) k) := by
  have hstep : ((p ^ m : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (dvd_pow_self p hm.ne')
  apply (isUnit_iff_prime_reduction he _).2
  simp only [digitValue, map_add, map_mul, map_natCast, hstep, zero_mul, add_zero]
  have hu := (isUnit_iff_prime_reduction hm (u : ZMod (p ^ m))).1 u.isUnit
  rw [← ZMod.natCast_zmod_val (u : ZMod (p ^ m)), map_natCast] at hu
  exact hu

private def digitUnit (hm : 0 < m) (he : 0 < e)
    (u : (ZMod (p ^ m))ˣ) (k : ZMod (p ^ n)) : (ZMod (p ^ e))ˣ :=
  (digitValue_isUnit hm he u k).unit

private theorem coe_digitUnit (hm : 0 < m) (he : 0 < e)
    (u : (ZMod (p ^ m))ˣ) (k : ZMod (p ^ n)) :
    (digitUnit hm he u k : ZMod (p ^ e)) = digitValue (u : ZMod (p ^ m)) k :=
  IsUnit.unit_spec _

private theorem digitUnit_val (hm : 0 < m) (he : 0 < e) (hsplit : e = m + n)
    (u : (ZMod (p ^ m))ˣ) (k : ZMod (p ^ n)) :
    (digitUnit hm he u k : ZMod (p ^ e)).val = (u : ZMod (p ^ m)).val + p ^ m * k.val := by
  rw [coe_digitUnit, digitValue, ← Nat.cast_mul, ← Nat.cast_add]
  apply ZMod.val_natCast_of_lt
  let hi : Fin (p ^ n) := ⟨k.val, k.val_lt⟩
  let lo : Fin (p ^ m) := ⟨(u : ZMod (p ^ m)).val, (u : ZMod (p ^ m)).val_lt⟩
  have h := (finProdFinEquiv (hi, lo)).isLt
  change (u : ZMod (p ^ m)).val + p ^ m * k.val < p ^ n * p ^ m at h
  rw [hsplit, pow_add, mul_comm (p ^ m) (p ^ n)]
  exact h

private theorem digitUnit_bijective (hm : 0 < m) (he : 0 < e) (hsplit : e = m + n) :
    Function.Bijective (fun uk : (ZMod (p ^ m))ˣ × ZMod (p ^ n) => digitUnit hm he uk.1 uk.2) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨u, k⟩ ⟨v, j⟩ h
    have hval := congrArg (fun x : (ZMod (p ^ e))ˣ => (x : ZMod (p ^ e)).val) h
    simp only [digitUnit_val hm he hsplit] at hval
    have hd : ((u : ZMod (p ^ m)), k.val) = ((v : ZMod (p ^ m)), j.val) :=
      (Nat.residueClassesEquiv (p ^ m)).symm.injective hval
    exact Prod.ext (Units.ext (congrArg Prod.fst hd))
      (ZMod.val_injective _ (congrArg Prod.snd hd))
  · intro x
    have hdiv : p ^ m ∣ p ^ e := pow_dvd_pow p (by omega)
    let u := ZMod.unitsMap hdiv x
    let k : ZMod (p ^ n) := ((x : ZMod (p ^ e)).val / p ^ m : ℕ)
    have hu : (u : ZMod (p ^ m)).val = (x : ZMod (p ^ e)).val % p ^ m := by
      change (ZMod.castHom hdiv (ZMod (p ^ m)) (x : ZMod (p ^ e))).val = _
      conv_lhs => rw [← ZMod.natCast_zmod_val (x : ZMod (p ^ e)),
        map_natCast, ZMod.val_natCast]
    have hk : (x : ZMod (p ^ e)).val / p ^ m < p ^ n := by
      apply (Nat.div_lt_iff_lt_mul (pow_pos (Fact.out : p.Prime).pos _)).2
      rw [mul_comm (p ^ n) (p ^ m), ← pow_add, ← hsplit]
      exact (x : ZMod (p ^ e)).val_lt
    refine ⟨(u, k), Units.ext (ZMod.val_injective _ ?_)⟩
    change (digitUnit hm he u k : ZMod (p ^ e)).val = (x : ZMod (p ^ e)).val
    rw [digitUnit_val hm he hsplit, hu, show k.val = _ from ZMod.val_natCast_of_lt hk,
      Nat.mod_add_div]

private def digitUnitEquiv (hm : 0 < m) (he : 0 < e) (hsplit : e = m + n) :
    (ZMod (p ^ m))ˣ × ZMod (p ^ n) ≃ (ZMod (p ^ e))ˣ :=
  Equiv.ofBijective (fun uk => digitUnit hm he uk.1 uk.2) (digitUnit_bijective hm he hsplit)

end Digits

section Stationary

variable {e : ℕ}

local notation "M" => p ^ (e - e / 2)
local notation "N" => p ^ (e / 2)
local notation "R" => ZMod (p ^ e)
local notation "U" => (ZMod M)ˣ

private theorem split_exponent (e : ℕ) : e = (e - e / 2) + e / 2 := by omega

omit [Fact p.Prime] in
private theorem split_modulus : p ^ e = M * N := by
  rw [← pow_add, ← split_exponent e]

/-- Reduction to the modulus of the summation digit. -/
def reduceLow : R →+* ZMod N :=
  ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod N)

/-- Reduction of the base modulus to the modulus of the congruence. -/
def reduceBase : ZMod M →+* ZMod N :=
  ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod N)

/-- The least nonnegative representative of the base digit in the full modulus. -/
def liftBase (u : ZMod M) : R := u.val

private theorem reduceLow_liftBase (u : ZMod M) :
    reduceLow (liftBase u : R) = reduceBase (e := e) u := by
  have hu : (u.val : ZMod M) = u := ZMod.natCast_zmod_val u
  calc
    _ = (u.val : ZMod N) := by simp only [liftBase, map_natCast]
    _ = reduceBase (e := e) u := by rw [← map_natCast (reduceBase (e := e)) u.val, hu]

/-- The point with base digit `u` and summation digit `k` in the full modulus. -/
def fiberPoint (u : ZMod M) (k : ZMod N) : R :=
  digitValue u k

/-- The quadratic condition on a base digit in the smaller modulus. -/
def IsStationary (a : R) (b : Rˣ) (u : U) : Prop :=
  reduceLow a * reduceBase (e := e) (u : ZMod M) ^ 2 = reduceLow (b : R)

instance (a : R) (b : Rˣ) (u : U) : Decidable (IsStationary a b u) := by
  unfold IsStationary
  infer_instance

/-- The unit base digits whose fibers survive. -/
def stationaryResidues (a : R) (b : Rˣ) : Finset U :=
  Finset.univ.filter (IsStationary a b)

private theorem liftBase_isUnit (he : 2 ≤ e) (u : U) :
    IsUnit (liftBase (u : ZMod M) : R) := by
  have h := digitValue_isUnit (p := p) (m := e - e / 2) (e := e) (n := e / 2)
    (by omega) (by omega) u (0 : ZMod N)
  simpa only [digitValue, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero, liftBase] using h

omit [Fact p.Prime] in
private theorem step_sq_zero (k : ZMod N) :
    (((M : ℕ) : R) * (k.val : R)) ^ 2 = 0 := by
  have hdiv : p ^ e ∣ M ^ 2 := by
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)
  have hstep : ((M : ℕ) : R) ^ 2 = 0 := by
    rw [← Nat.cast_pow]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hdiv
  rw [mul_pow, hstep, zero_mul]

private theorem stdAddChar_mul_step (w : R) :
    ZMod.stdAddChar (((M : ℕ) : R) * w) = ZMod.stdAddChar (reduceLow w) := by
  obtain ⟨j, rfl⟩ := ZMod.natCast_zmod_surjective w
  rw [map_natCast, ← Nat.cast_mul, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    ZMod.toCircle_natCast, ZMod.toCircle_natCast]
  congr 1
  have hM : ((M : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hN : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  rw [split_modulus (p := p) (e := e)]
  simp only [Nat.cast_mul]
  field_simp [hM, hN]

private theorem phase_fiberPoint (he : 2 ≤ e) (a : R) (b : Rˣ) (u : U) (k : ZMod N) :
    phase a (b : R) (fiberPoint (u : ZMod M) k) =
      phase a (b : R) (liftBase (u : ZMod M)) *
        ZMod.stdAddChar (k * reduceLow (a - (b : R) * (liftBase (u : ZMod M) : R)⁻¹ ^ 2)) := by
  let z : R := liftBase (u : ZMod M)
  let w : R := (k.val : R)
  have hphase :
      a * (z + ((M : ℕ) : R) * w) + (b : R) * (z + ((M : ℕ) : R) * w)⁻¹ =
        (a * z + (b : R) * z⁻¹) + ((M : ℕ) : R) * (w * (a - (b : R) * z⁻¹ ^ 2)) := by
    rw [inv_add_of_sq_zero _ _ (liftBase_isUnit he u) (step_sq_zero k)]
    ring
  change ZMod.stdAddChar
      (a * (z + ((M : ℕ) : R) * w) + (b : R) * (z + ((M : ℕ) : R) * w)⁻¹) =
    ZMod.stdAddChar (a * z + (b : R) * z⁻¹) *
      ZMod.stdAddChar (k * reduceLow (a - (b : R) * z⁻¹ ^ 2))
  have hw : reduceLow w = k := by
    dsimp only [w]
    rw [map_natCast, ZMod.natCast_zmod_val]
  rw [hphase, AddChar.map_add_eq_mul, stdAddChar_mul_step, map_mul, hw]

private theorem slope_zero_iff (he : 2 ≤ e) (a : R) (b : Rˣ) (u : U) :
    reduceLow (a - (b : R) * (liftBase (u : ZMod M) : R)⁻¹ ^ 2) = 0 ↔
      IsStationary a b u := by
  let z : R := liftBase (u : ZMod M)
  let f : R →+* ZMod N := reduceLow
  have hu := liftBase_isUnit he u
  have hinv : f z * f z⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit z hu, map_one]
  have hunit : IsUnit (f z ^ 2) := IsUnit.pow 2 (hu.map f)
  have hmul :
      f (a - (b : R) * z⁻¹ ^ 2) * f z ^ 2 = f a * f z ^ 2 - f (b : R) := by
    calc
      _ = f a * f z ^ 2 - f (b : R) * (f z * f z⁻¹) ^ 2 := by
        simp only [map_sub, map_mul, map_pow]
        ring
      _ = _ := by rw [hinv]; simp
  unfold IsStationary
  rw [← reduceLow_liftBase (u : ZMod M)]
  change f (a - (b : R) * z⁻¹ ^ 2) = 0 ↔ f a * f z ^ 2 = f (b : R)
  constructor
  · intro h
    apply sub_eq_zero.mp
    rw [← hmul, h, zero_mul]
  · intro h
    apply hunit.mul_right_cancel
    rw [hmul, h, sub_self, zero_mul]

/-- Each fiber either contributes its full size times the base phase or vanishes. -/
theorem fiber_sum_eq (he : 2 ≤ e) (a : R) (b : Rˣ) (u : U) :
    (∑ k : ZMod N, phase a (b : R) (fiberPoint (u : ZMod M) k)) =
      if IsStationary a b u then ((N : ℕ) : ℂ) * phase a (b : R) (liftBase (u : ZMod M))
      else 0 := by
  simp_rw [phase_fiberPoint he a b u]
  rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N),
    ZMod.card]
  by_cases h : IsStationary a b u
  · simp [h, (slope_zero_iff he a b u).2 h, mul_comm]
  · have hzero := (not_congr (slope_zero_iff he a b u)).2 h
    rw [ite_eq_right hzero, ite_eq_right h, Nat.cast_zero, mul_zero]

/-- Reindex the original sum over units and retain precisely the stationary fibers. -/
theorem kloosterman_eq_stationary_sum (he : 2 ≤ e) (a : R) (b : Rˣ) :
    kloosterman a b = ((N : ℕ) : ℂ) *
      ∑ u ∈ stationaryResidues a b, phase a (b : R) (liftBase (u : ZMod M)) := by
  have hm : 0 < e - e / 2 := by omega
  have he' : 0 < e := by omega
  let digits : U × ZMod N ≃ Rˣ :=
    digitUnitEquiv hm he' (split_exponent e)
  have hsum :
      kloosterman a b = ∑ u : U, ∑ k : ZMod N,
        phase a (b : R) (fiberPoint (u : ZMod M) k) := by
    unfold kloosterman
    rw [← (digits.sum_comp (fun x : Rˣ => phase a (b : R) (x : R))),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun k _ => ?_
    exact congrArg (phase a (b : R)) (coe_digitUnit hm he' u k)
  rw [hsum, Finset.mul_sum, stationaryResidues, Finset.sum_filter]
  exact Finset.sum_congr rfl fun u _ => fiber_sum_eq he a b u

/-- The triangle inequality bounds the norm by the size of a fiber times
the number of stationary base digits. -/
theorem norm_kloosterman_le_card_stationary (he : 2 ≤ e) (a : R) (b : Rˣ) :
    ‖kloosterman a b‖ ≤ ((N : ℕ) : ℝ) * (stationaryResidues a b).card := by
  rw [kloosterman_eq_stationary_sum he a b, norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (Nat.cast_nonneg _)
  simp only [phase, ZMod.stdAddChar_apply, Circle.norm_coe, Finset.sum_const,
    Nat.smul_one_eq_cast, le_refl]

/-- The roots of the stationary congruence among units modulo `p^(e/2)`. -/
def stationaryRoots (a : R) (b : Rˣ) : Finset (ZMod N)ˣ :=
  Finset.univ.filter fun v => reduceLow a * (v : ZMod N) ^ 2 = reduceLow (b : R)

private theorem reduceBase_digitUnit (hn : 0 < e / 2) (hm : 0 < e - e / 2)
    (v : (ZMod N)ˣ) (k : ZMod (p ^ (e - e / 2 - e / 2))) :
    reduceBase (e := e) (digitUnit hn hm v k : ZMod M) = (v : ZMod N) := by
  rw [coe_digitUnit]
  simp only [digitValue, map_add, map_mul, map_natCast, ZMod.natCast_self,
    zero_mul, add_zero, ZMod.natCast_zmod_val]

/-- Each root modulo `p^(e/2)` has one base digit lift for even `e`
and `p` base digit lifts for odd `e`. -/
theorem card_stationaryResidues_eq (he : 2 ≤ e) (a : R) (b : Rˣ) :
    (stationaryResidues a b).card =
      p ^ (e - e / 2 - e / 2) * (stationaryRoots a b).card := by
  have hn : 0 < e / 2 := by omega
  have hm : 0 < e - e / 2 := by omega
  have hsplit : e - e / 2 = e / 2 + (e - e / 2 - e / 2) := by omega
  let digits : (ZMod N)ˣ × ZMod (p ^ (e - e / 2 - e / 2)) ≃ U :=
    digitUnitEquiv hn hm hsplit
  calc
    _ = ∑ u : U, if IsStationary a b u then (1 : ℕ) else 0 := by
      rw [← Finset.sum_filter]
      simp [stationaryResidues]
    _ = ∑ v : (ZMod N)ˣ, ∑ _k : ZMod (p ^ (e - e / 2 - e / 2)),
        if reduceLow a * (v : ZMod N) ^ 2 = reduceLow (b : R) then (1 : ℕ) else 0 := by
      rw [← digits.sum_comp (fun u => if IsStationary a b u then (1 : ℕ) else 0),
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k _ => ?_
      change (if IsStationary a b (digitUnit hn hm v k) then (1 : ℕ) else 0) = _
      have hv : IsStationary a b (digitUnit hn hm v k) ↔
          reduceLow a * (v : ZMod N) ^ 2 = reduceLow (b : R) := by
        unfold IsStationary
        rw [reduceBase_digitUnit hn hm]
      by_cases h : reduceLow a * (v : ZMod N) ^ 2 = reduceLow (b : R) <;> simp [hv, h]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.sum_filter]
      simp [stationaryRoots]

/-- The norm is bounded by `p^(ceil(e/2))` times the number of smaller-modulus roots. -/
theorem norm_kloosterman_le_card_roots (he : 2 ≤ e) (a : R) (b : Rˣ) :
    ‖kloosterman a b‖ ≤ ((M : ℕ) : ℝ) * (stationaryRoots a b).card := by
  have hsum : e / 2 + (e - e / 2 - e / 2) = e - e / 2 := by omega
  calc
    _ ≤ ((N : ℕ) : ℝ) * (stationaryResidues a b).card := norm_kloosterman_le_card_stationary he a b
    _ = _ := by
      rw [card_stationaryResidues_eq he a b, Nat.cast_mul, ← mul_assoc,
        ← Nat.cast_mul, ← pow_add, hsum]

/-- A nonunit first coefficient has no stationary fiber when the second is a unit. -/
theorem kloosterman_eq_zero_of_not_isUnit (he : 2 ≤ e) (a : R) (b : Rˣ) (ha : ¬ IsUnit a) :
    kloosterman a b = 0 := by
  have hno (u : U) : ¬ IsStationary a b u := by
    intro hu
    let f : R →+* ZMod N := reduceLow
    change f a * reduceBase (e := e) (u : ZMod M) ^ 2 = f (b : R) at hu
    have hb : IsUnit (f (b : R)) := b.isUnit.map f
    rw [← hu] at hb
    have ha' : IsUnit (f a) := isUnit_of_mul_isUnit_left hb
    obtain ⟨j, rfl⟩ := ZMod.natCast_zmod_surjective a
    have hlow : 0 < e / 2 := by omega
    rw [map_natCast, ZMod.isUnit_natCast_iff_not_dvd_pow Fact.out hlow] at ha'
    exact ha ((ZMod.isUnit_natCast_iff_not_dvd_pow Fact.out (by omega : 0 < e)).2 ha')
  have hfilter : stationaryResidues a b = ∅ := by simp [stationaryResidues, hno]
  rw [kloosterman_eq_stationary_sum he a b, hfilter, Finset.sum_empty, mul_zero]

end Stationary

end D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase
