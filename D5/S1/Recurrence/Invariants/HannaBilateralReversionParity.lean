/- GID: D5/S1/Recurrence/Invariants/HannaBilateralReversionParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaBilateralReversionParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Paired bilateral summands and integral reversion prove Hanna A379202 parity. -/

/-
denominator_zero: proof_shape: bind-only; consumers: pair_map, literal_negative
pair_order: proof_shape: bind-only; consumers: regular_window
regular_window: proof_shape: bind-only; consumers: regular_subst
T_zero: proof_shape: bind-only; consumers: B_mod_two, rationalT_zero, B_subst_fixed
negative_fold: proof_shape: bind-only; consumers: literal_negative
subst_inverse: proof_shape: bind-only; consumers: pair_subst, B_subst_fixed
pair_subst: proof_shape: bind-only; consumers: regular_subst
pair_map: proof_shape: bind-only; consumers: regular_map
regular_map: proof_shape: bind-only; consumers: T_mod_two, T_subst
pair_mod_two: proof_shape: bind-only; consumers: regular_mod_two
regular_mod_two: proof_shape: bind-only; consumers: T_mod_two
T_mod_two: proof_shape: bind-only; consumers: B_mod_two
regular_subst: proof_shape: bind-only; consumers: T_subst
B_zero: proof_shape: bind-only; consumers: reversion, rationalB_zero
B_one: proof_shape: bind-only; consumers: B_unit, integralA_one, rationalB_one
B_unit: proof_shape: bind-only; consumers: integralA, integralA_one
integralA_zero: proof_shape: bind-only; consumers: integralA_mod_two, rationalA_zero, rational_reversion
integralA_one: proof_shape: bind-only; consumers: rationalA_one
reversion: proof_shape: bind-only; consumers: integralA_mod_two, rational_reversion
B_mod_two: proof_shape: bind-only; consumers: integralA_mod_two
integralA_mod_two: proof_shape: bind-only; consumers: integralA_even
window_split: proof_shape: bind-only; consumers: normalized_sum
coe_inverse: proof_shape: bind-only; consumers: literal_negative
coe_negative_coeff: proof_shape: bind-only; consumers: outside_window, normalized_sum
literal_positive: proof_shape: bind-only; consumers: outside_window, normalized_sum
literal_negative: proof_shape: bind-only; consumers: outside_window, normalized_sum
inverse_leading: proof_shape: bind-only; consumers: normalized_sum
positive_order: proof_shape: bind-only; consumers: outside_window, normalized_sum
negative_order: proof_shape: bind-only; consumers: outside_window, normalized_sum
outside_window: proof_shape: bind-only; consumers: literal_finite_window
literal_finite_window: proof_shape: bind-only; consumers: normalized_sum
normalized_sum: proof_shape: bind-only; consumers: bilateral_normalization
bilateral_normalization: proof_shape: bind-only; consumers: isGF_fixed
X_laurent_inverse: proof_shape: bind-only; consumers: isGF_fixed
isGF_fixed: proof_shape: bind-only; consumers: rationalA_isGF, solution_unique
rationalT_zero: proof_shape: bind-only; consumers: B_subst_fixed
rationalB_zero: proof_shape: bind-only; consumers: solution_unique
rationalB_one: proof_shape: bind-only; consumers: solution_unique
T_subst: proof_shape: bind-only; consumers: B_subst_fixed
B_subst_fixed: proof_shape: bind-only; consumers: rationalA_isGF, solution_unique
rationalA_zero: proof_shape: bind-only; consumers: rationalA_isGF, solution_unique
rationalA_one: proof_shape: bind-only; consumers: rationalA_isGF
rational_reversion: proof_shape: bind-only; consumers: rationalA_isGF, solution_unique
rationalA_isGF: proof_shape: bind-only; consumers: result
solution_unique: proof_shape: bind-only; consumers: result
integralA_even: proof_shape: bind-only; consumers: result
result: proof_shape: bind-only; consumers: external settlement
escape_witness: none
admission_basis: open-problem-resolution (#18876; Proved)
Direct frozen dependencies:
  D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.agree_subst;
  D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.map_inverse;
  D5/S1/Recurrence/Bilateral/BilateralProductModFour.ofSeries_inverse;
  D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.inverse_one
    (existing dev owner; escape audit: https://github.com/the-omega-institute/trureturing/issues/19167).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19114
The public definitions state the OEIS equation with Laurent integer powers and
its coefficientwise bilateral sum. The proof pairs k with -k-2 and constructs
an integral compositional inverse before identifying every rational solution.
-/

import D5.S1.Recurrence.Bilateral.BilateralProductModFour
import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import D5.S1.Recurrence.Residue.ContinuedFractionOddSquare
import D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.CharP.Two

/-! Pairing opposite Laurent indices and integral compositional reversion. -/

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaBilateralReversionParity

open PowerSeries

/-- The summand `A(x)^n * (A(x)^n + 2)^(n+1)` of OEIS A379202, in the field of Laurent series. -/
noncomputable def term (A : PowerSeries ℚ) (n : ℤ) : LaurentSeries ℚ :=
  (A : LaurentSeries ℚ) ^ n * ((A : LaurentSeries ℚ) ^ n + 2) ^ (n + 1)

/-- `Sum_{n=-oo..+oo} A(x)^n * (A(x)^n + 2)^(n+1)`, coefficientwise: the coefficient of `x^(j-1)` is the sum of
the coefficients of `x^(j-1)` in the summands `n` with `|n| ≤ j + 2`. For `A = x + …` the summand `n ≥ 0` has
order `n` and the summand `n = -m` has order `m^2 - 2m`, so no other summand contributes. -/
noncomputable def bilateralSum (A : PowerSeries ℚ) : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) (1 : ℚ) *
    HahnSeries.ofPowerSeries ℤ ℚ
      (mk fun j => ∑ n ∈ Finset.Icc (-(j : ℤ) - 2) ((j : ℤ) + 2), (term A n).coeff ((j : ℤ) - 1))

/-- OEIS A379202: "G.f. A(x) satisfies 1/x = Sum_{n=-oo..+oo} A(x)^n * (A(x)^n + 2)^(n+1)", with
A(x) = x + 4*x^2 + ... (offset 1). -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    ((X : PowerSeries ℚ) : LaurentSeries ℚ)⁻¹ = bilateralSum A

/-- OEIS A379202 (P. D. Hanna), conjecture: "a(n) is even for n > 1". The terms are integers. -/
def claim : Prop :=
  (∃ A, IsGF A) ∧ ∀ A, IsGF A → ∀ n : ℕ, 1 < n → ∃ z : ℤ, coeff n A = z ∧ Even z

end D5.S1.Recurrence.Invariants.HannaBilateralReversionParity

namespace D5.S1.Recurrence.Invariants.HannaBilateralReversionParity
open PowerSeries

section General
variable {R : Type*} [CommRing R]

private noncomputable def positive (A : PowerSeries R) (k : ℕ) : PowerSeries R :=
  A ^ k * (A ^ k + 2) ^ (k + 1)
private noncomputable def negative (A : PowerSeries R) (k : ℕ) : PowerSeries R :=
  A ^ (k * (k + 2)) * invOfUnit (1 + 2 * A ^ (k + 2)) 1 ^ (k + 1)
private noncomputable def pair (A : PowerSeries R) (k : ℕ) : PowerSeries R :=
  positive A k + negative A k
private noncomputable def regularSum (A : PowerSeries R) : PowerSeries R :=
  mk fun d => ∑ k ∈ Finset.range (d + 1), coeff d (pair A k)
private noncomputable def T : PowerSeries ℤ := 1 + X * (regularSum (X : PowerSeries ℤ))

private theorem denominator_zero (A : PowerSeries R) (hA : constantCoeff A = 0) (k : ℕ) :
    constantCoeff (1 + 2 * A ^ (k + 2)) = 1 := by simp [hA]

private theorem pair_order (A : PowerSeries R) (hA : constantCoeff A = 0) (k : ℕ) :
    X ^ k ∣ pair A k := by
  have hp : (X : PowerSeries R) ^ k ∣ A ^ k := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hA) k
  have hn : (X : PowerSeries R) ^ k ∣ A ^ (k * (k + 2)) :=
    (pow_dvd_pow X (by nlinarith : k ≤ k * (k + 2))).trans
      (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hA) _)
  exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_left hn _)

private theorem regular_window (A : PowerSeries R) (hA : constantCoeff A = 0)
    (d K : ℕ) (h : d ≤ K) :
    coeff d (regularSum A) = ∑ k ∈ Finset.range (K + 1), coeff d (pair A k) := by
  simp only [regularSum, coeff_mk]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hnot
  exact X_pow_dvd_iff.mp (pair_order A hA k) d (by simp only [Finset.mem_range] at hnot; omega)

private theorem T_zero : constantCoeff T = 1 := by simp [T]

private theorem negative_fold {F : Type*} [Field F] (a : F) (ha : a ≠ 0) (k : ℕ) :
    a ^ (-((k + 2 : ℕ) : ℤ)) *
      (a ^ (-((k + 2 : ℕ) : ℤ)) + 2) ^ (1 - ((k + 2 : ℕ) : ℤ)) =
    a ^ (k * (k + 2)) * (1 + 2 * a ^ (k + 2))⁻¹ ^ (k + 1) := by
  have hf : a ^ (-((k + 2 : ℕ) : ℤ)) + 2 =
      a ^ (-((k + 2 : ℕ) : ℤ)) * (1 + 2 * a ^ (k + 2)) := by
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [hf, mul_zpow]
  rw [← mul_assoc, ← zpow_mul, ← zpow_add₀ ha]
  have he : -((k + 2 : ℕ) : ℤ) + -((k + 2 : ℕ) : ℤ) *
      (1 - ((k + 2 : ℕ) : ℤ)) = ((k * (k + 2) : ℕ) : ℤ) := by push_cast; ring
  have he' : (1 - ((k + 2 : ℕ) : ℤ)) = -((k + 1 : ℕ) : ℤ) :=
    (Int.neg_eq_comm.mp rfl).symm
  rw [he, he', zpow_natCast, zpow_neg, zpow_natCast, inv_pow]


private theorem subst_inverse (A F : PowerSeries R) (hA : constantCoeff A = 0)
    (hF : constantCoeff F = 1) :
    (invOfUnit F 1).subst A = invOfUnit (F.subst A) 1 := by
  have hs : HasSubst A := .of_constantCoeff_zero hA
  have hz : constantCoeff (F.subst A) = 1 := by
    change MvPowerSeries.constantCoeff (F.subst A) = 1
    simpa only [Algebra.algebraMap_self, RingHom.id_apply, hF] using
      constantCoeff_subst_of_constantCoeff_zero hA F
  apply (isUnit_iff_constantCoeff.mpr (hz ▸ isUnit_one)).mul_left_cancel
  rw [mul_invOfUnit _ 1 hz, ← subst_mul hs, mul_invOfUnit _ 1 hF]
  rw [← coe_substAlgHom hs, map_one]

private theorem pair_subst (A : PowerSeries R) (hA : constantCoeff A = 0) (k : ℕ) :
    (pair (X : PowerSeries R) k).subst A = pair A k := by
  have hs : HasSubst A := .of_constantCoeff_zero hA
  have hn : (invOfUnit (1 + 2 * (X : PowerSeries R) ^ (k + 2)) 1).subst A =
      invOfUnit (1 + 2 * A ^ (k + 2)) 1 := by
    rw [subst_inverse A _ hA (by simp)]
    congr 1
    rw [← coe_substAlgHom hs]
    simp only [map_add, map_one, map_mul, map_ofNat, map_pow, substAlgHom_X]
  unfold pair positive negative
  simp only [subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, hn]
  rw [← coe_substAlgHom hs]
  simp only [map_ofNat]

private theorem pair_map {S : Type*} [CommRing S] (f : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 0) (k : ℕ) :
    (pair A k).map f = pair (A.map f) k := by
  unfold pair positive negative
  simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour.map_inverse f _ (denominator_zero A hA k)]
  simp only [map_add, map_one, map_mul, map_ofNat, map_pow]

private theorem regular_map {S : Type*} [CommRing S] (f : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 0) :
    (regularSum A).map f = regularSum (A.map f) := by
  ext d
  simp only [coeff_map, regularSum, coeff_mk, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← coeff_map, pair_map f A hA]

private theorem pair_mod_two (A : PowerSeries (ZMod 2)) (k : ℕ) : pair A k = 0 := by
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, map_zero]
  have hinv : invOfUnit (1 : PowerSeries (ZMod 2)) 1 = 1 := by
    exact D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.inverse_one
  unfold pair positive negative
  rw [htwo, add_zero, zero_mul, add_zero, hinv, one_pow, mul_one,
    ← pow_succ', ← pow_mul]
  have he : k * (k + 1 + 1) = k * (k + 2) := rfl
  rw [he]
  have hz : ∀ b : PowerSeries (ZMod 2), b + b = 0 := by
    intro b
    ext d
    simpa only [map_add, map_zero] using CharTwo.add_self_eq_zero (coeff d b)
  exact hz _

private theorem regular_mod_two (A : PowerSeries (ZMod 2)) : regularSum A = 0 := by
  ext d
  simp [regularSum, pair_mod_two]

private theorem T_mod_two : T.map (Int.castRingHom (ZMod 2)) = 1 := by
  simp only [T, map_add, map_one, map_mul, map_X]
  rw [show (regularSum (X : PowerSeries ℤ)).map (Int.castRingHom (ZMod 2)) = 0 by
    rw [regular_map _ X (by simp), map_X, regular_mod_two]]
  simp


private theorem regular_subst (A : PowerSeries R) (hA : constantCoeff A = 0) :
    (regularSum (X : PowerSeries R)).subst A = regularSum A := by
  ext d
  have hw : ∀ e < d + 1, coeff e (regularSum (X : PowerSeries R)) =
      coeff e (∑ k ∈ Finset.range (d + 1), pair X k) := by
    intro e he
    rw [regular_window _ (by simp) e d (by omega), map_sum]
  have hs := D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.agree_subst
    hA hA hw (fun _ _ => rfl) d (by omega)
  rw [regular_window A hA d d le_rfl]
  refine hs.trans ?_
  have h : HasSubst A := .of_constantCoeff_zero hA
  rw [← coe_substAlgHom h, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [coe_substAlgHom] using congrArg (coeff d) (pair_subst A hA k)

private noncomputable def B : PowerSeries ℤ := X * invOfUnit T 1
private theorem B_zero : constantCoeff B = 0 := by simp [B]
private theorem B_one : coeff 1 B = 1 := by
  simp [B, constantCoeff_invOfUnit]
private theorem B_unit : IsUnit (coeff 1 B) := B_one ▸ isUnit_one
private noncomputable def integralA : PowerSeries ℤ := B.substInvOfIsUnit B_unit
private theorem integralA_zero : constantCoeff integralA = 0 := constantCoeff_substInvOfIsUnit _ _
private theorem integralA_one : coeff 1 integralA = 1 := by
  rw [integralA, coeff_one_substInvOfIsUnit]
  have hu : B_unit.unit = 1 := by apply Units.ext; simpa using B_one
  rw [hu]; rfl
private theorem reversion : B.subst integralA = X := subst_substInvOfIsUnit_right _ B_zero _

private theorem B_mod_two : B.map (Int.castRingHom (ZMod 2)) = X := by
  rw [B, map_mul, map_X,
    D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour.map_inverse _ _ T_zero,
    T_mod_two]
  have hi : invOfUnit (1 : PowerSeries (ZMod 2)) 1 = 1 := by
    exact D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.inverse_one
  rw [hi, mul_one]

private theorem integralA_mod_two : integralA.map (Int.castRingHom (ZMod 2)) = X := by
  have he := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) reversion
  have hm : PowerSeries.map (Int.castRingHom (ZMod 2)) (B.subst integralA) =
      (B.map (Int.castRingHom (ZMod 2))).subst (integralA.map (Int.castRingHom (ZMod 2))) :=
    map_subst (.of_constantCoeff_zero integralA_zero) _
  rw [hm, map_X, B_mod_two] at he
  have hz : constantCoeff (integralA.map (Int.castRingHom (ZMod 2))) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      integralA_zero, map_zero]
  rwa [subst_X (.of_constantCoeff_zero hz)] at he

private theorem window_split {M : Type*} [AddCommGroup M] (f : ℤ → M) (r : ℕ) :
    (∑ n ∈ Finset.Icc (-((r + 1 : ℕ) : ℤ)) ((r + 1 : ℕ) : ℤ), f n) =
      f (-1) + (∑ k ∈ Finset.range (r + 2), f (k : ℤ)) +
        ∑ k ∈ Finset.range r, f (-((k + 2 : ℕ) : ℤ)) := by
  induction r with
  | zero =>
    have he : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := Finset.val_inj.mp rfl
    simp [he, Finset.sum_range_succ]
  | succ r ih =>
    rw [show ((r + 1 + 1 : ℕ) : ℤ) = ((r + 1 : ℕ) : ℤ) + 1 by omega,
      Finset.sum_Icc_succ_eq_add_endpoints, ih]
    have hp : (∑ k ∈ Finset.range (r + 1 + 2), f (k : ℤ)) =
        (∑ k ∈ Finset.range (r + 2), f (k : ℤ)) + f ((r + 2 : ℕ) : ℤ) := by
      exact Finset.sum_range_succ (fun k => f (k : ℤ)) (r + 2)
    have hn : (∑ k ∈ Finset.range (r + 1), f (-((k + 2 : ℕ) : ℤ))) =
        (∑ k ∈ Finset.range r, f (-((k + 2 : ℕ) : ℤ))) + f (-((r + 2 : ℕ) : ℤ)) :=
      Finset.sum_range_succ _ _
    rw [hp, hn, show ((r + 1 : ℕ) : ℤ) + 1 = ((r + 2 : ℕ) : ℤ) by omega]
    abel



end General

private theorem coe_inverse (F : PowerSeries ℚ) (hF : constantCoeff F = 1) :
    (HahnSeries.ofPowerSeries ℤ ℚ) (invOfUnit F 1) = ((HahnSeries.ofPowerSeries ℤ ℚ) F)⁻¹ := by
  rw [PowerSeries.invOfUnit_eq' F 1 hF]
  exact D5.S1.Recurrence.Bilateral.BilateralProductModFour.ofSeries_inverse F
    (by simpa only [hF] using (one_ne_zero : (1 : ℚ) ≠ 0))

private theorem coe_negative_coeff (F : PowerSeries ℚ) (e : ℤ) (he : e < 0) :
    ((HahnSeries.ofPowerSeries ℤ ℚ) F).coeff e = 0 := by
  simpa only [ite_eq_left he] using (PowerSeries.coeff_coe (f := F) e)

private theorem literal_positive (A : PowerSeries ℚ) (k : ℕ) :
    term A (k : ℤ) = (HahnSeries.ofPowerSeries ℤ ℚ) (positive A k) := by
  have he : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := Int.ofNat_add_one_out k
  simp only [term, he, zpow_natCast, positive, map_mul, map_pow,
    map_add, map_ofNat]

private theorem literal_negative (A : PowerSeries ℚ) (hA : constantCoeff A = 0)
    (ha : (A : LaurentSeries ℚ) ≠ 0) (k : ℕ) :
    term A (-((k + 2 : ℕ) : ℤ)) = (HahnSeries.ofPowerSeries ℤ ℚ) (negative A k) := by
  have he : -((k + 2 : ℕ) : ℤ) + 1 = 1 - ((k + 2 : ℕ) : ℤ) := neg_add_eq_sub _ _
  rw [term, he, negative_fold _ ha]
  simp only [negative, map_mul, map_pow, coe_inverse _ (denominator_zero A hA k)]
  simp only [map_add, map_one, map_mul, map_ofNat, map_pow]

private theorem inverse_leading (u : PowerSeries ℚ) (hu : constantCoeff u = 1) :
    ((X * u : PowerSeries ℚ) : LaurentSeries ℚ)⁻¹ =
      HahnSeries.single (-1 : ℤ) 1 * (HahnSeries.ofPowerSeries ℤ ℚ) (invOfUnit u 1) := by
  apply inv_eq_of_mul_eq_one_left
  change (_ * (HahnSeries.ofPowerSeries ℤ ℚ) (invOfUnit u 1)) * (HahnSeries.ofPowerSeries ℤ ℚ) (X * u) = 1
  rw [map_mul]
  have hx : (HahnSeries.ofPowerSeries ℤ ℚ) X * HahnSeries.single (-1 : ℤ) 1 = 1 := by
    simp [HahnSeries.single_mul_single]
  have hu' : (HahnSeries.ofPowerSeries ℤ ℚ) (invOfUnit u 1) * (HahnSeries.ofPowerSeries ℤ ℚ) u = 1 := by
    rw [← map_mul, invOfUnit_mul _ 1 hu, map_one]
  calc
    _ = ((HahnSeries.ofPowerSeries ℤ ℚ) X * HahnSeries.single (-1 : ℤ) 1) *
        ((HahnSeries.ofPowerSeries ℤ ℚ) (invOfUnit u 1) * (HahnSeries.ofPowerSeries ℤ ℚ) u) := by ring
    _ = 1 := by rw [hx, hu']; ring

private theorem positive_order (A : PowerSeries ℚ) (hA : constantCoeff A = 0) (k : ℕ) :
    X ^ k ∣ positive A k :=
  dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hA) k) _

private theorem negative_order (A : PowerSeries ℚ) (hA : constantCoeff A = 0) (k : ℕ) :
    X ^ k ∣ negative A k := by
  apply dvd_mul_of_dvd_left
  apply (pow_dvd_pow X (show k ≤ k * (k + 2) by nlinarith)).trans
  exact pow_dvd_pow_of_dvd (X_dvd_iff.mpr hA) _

private theorem outside_window (u : PowerSeries ℚ) (hu : constantCoeff u = 1)
    (j : ℕ) (n : ℤ) (hn : n < -(j : ℤ) - 2 ∨ (j : ℤ) + 2 < n) :
    (term (X * u) n).coeff ((j : ℤ) - 1) = 0 := by
  have hA : constantCoeff (X * u) = 0 := by simp
  have ha : ((X * u : PowerSeries ℚ) : LaurentSeries ℚ) ≠ 0 := by
    intro hz
    have he : X * u = (0 : PowerSeries ℚ) :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ) (by simpa using hz)
    have h1 := congrArg (coeff 1) he
    simp [hu] at h1
  by_cases hp : 0 ≤ n
  · let k := n.toNat
    have hk : (k : ℤ) = n := Int.toNat_of_nonneg hp
    rw [← hk, literal_positive]
    cases j with
    | zero => exact coe_negative_coeff _ _ (by norm_num)
    | succ d =>
      rw [show ((d + 1 : ℕ) : ℤ) - 1 = (d : ℤ) from Int.sub_eq_iff_eq_add.mpr rfl,
        HahnSeries.ofPowerSeries_apply_coeff]
      exact X_pow_dvd_iff.mp (positive_order (X * u) hA k) d (by omega)
  · have hneg : n ≤ -2 := by omega
    let k := (-n - 2).toNat
    have hk : n = -((k + 2 : ℕ) : ℤ) := by
      have ht : ((-n - 2).toNat : ℤ) = -n - 2 := Int.toNat_of_nonneg (by omega)
      dsimp [k]
      omega
    rw [hk, literal_negative (X * u) hA ha]
    cases j with
    | zero => exact coe_negative_coeff _ _ (by norm_num)
    | succ d =>
      rw [show ((d + 1 : ℕ) : ℤ) - 1 = (d : ℤ) from Int.sub_eq_iff_eq_add.mpr rfl,
        HahnSeries.ofPowerSeries_apply_coeff]
      exact X_pow_dvd_iff.mp (negative_order (X * u) hA k) d (by omega)

private theorem literal_finite_window (u : PowerSeries ℚ) (hu : constantCoeff u = 1)
    (j K : ℕ) (hK : j + 2 ≤ K) :
    (∑ n ∈ Finset.Icc (-(j : ℤ) - 2) ((j : ℤ) + 2),
      (term (X * u) n).coeff ((j : ℤ) - 1)) =
    ∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (term (X * u) n).coeff ((j : ℤ) - 1) := by
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn hnot
    apply outside_window u hu j n
    simp only [Finset.mem_Icc] at hnot
    omega

private theorem normalized_sum (u : PowerSeries ℚ) (hu : constantCoeff u = 1) :
    (mk fun j => ∑ n ∈ Finset.Icc (-(j : ℤ) - 2) ((j : ℤ) + 2),
      (term (X * u) n).coeff ((j : ℤ) - 1)) =
      invOfUnit u 1 + X * regularSum (X * u) := by
  let A : PowerSeries ℚ := X * u
  have hA : constantCoeff A = 0 := by simp [A]
  have ha : (A : LaurentSeries ℚ) ≠ 0 := by
    intro hz
    have he : A = 0 := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ) (by simpa using hz)
    have h1 := congrArg (coeff 1) he
    simp [A, hu] at h1
  have hi (j : ℕ) : (term A (-1)).coeff ((j : ℤ) - 1) = coeff j (invOfUnit u 1) := by
    simp only [term, Int.reduceNeg, neg_add_cancel, zpow_zero, mul_one, zpow_neg_one]
    rw [show (A : LaurentSeries ℚ)⁻¹ = _ from inverse_leading u hu,
      HahnSeries.coeff_single_mul]
    rw [show (j : ℤ) - 1 - -1 = (j : ℤ) from Int.sub_eq_iff_eq_add.mpr rfl, one_mul]
    exact LaurentSeries.coeff_coe_powerSeries _ j
  ext j
  rw [coeff_mk, map_add]
  change (∑ n ∈ Finset.Icc (-(j : ℤ) - 2) ((j : ℤ) + 2),
    (term A n).coeff ((j : ℤ) - 1)) = _
  rw [literal_finite_window u hu j (j + 3) (by omega),
    show j + 3 = j + 2 + 1 by omega,
    window_split (fun n => (term A n).coeff ((j : ℤ) - 1)) (j + 2), hi]
  simp_rw [literal_positive, literal_negative A hA ha]
  cases j with
  | zero =>
    simp only [Nat.cast_zero, zero_sub, coeff_zero_X_mul, add_zero]
    have hp : ∀ k, ((HahnSeries.ofPowerSeries ℤ ℚ) (positive A k)).coeff (-1) = 0 :=
      fun k => coe_negative_coeff _ _ (by omega)
    have hn : ∀ k, ((HahnSeries.ofPowerSeries ℤ ℚ) (negative A k)).coeff (-1) = 0 :=
      fun k => coe_negative_coeff _ _ (by omega)
    simp [hp, hn]
  | succ d =>
    rw [coeff_succ_X_mul]
    have he : ((d + 1 : ℕ) : ℤ) - 1 = (d : ℤ) := Int.sub_eq_iff_eq_add.mpr rfl
    simp only [he, HahnSeries.ofPowerSeries_apply_coeff]
    have hp : (∑ k ∈ Finset.range (d + 1 + 2 + 2), coeff d (positive A k)) =
        ∑ k ∈ Finset.range (d + 1), coeff d (positive A k) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hnot
      apply X_pow_dvd_iff.mp (positive_order A hA k) d
      simp only [Finset.mem_range] at hnot
      omega
    have hn : (∑ k ∈ Finset.range (d + 1 + 2), coeff d (negative A k)) =
        ∑ k ∈ Finset.range (d + 1), coeff d (negative A k) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hnot
      apply X_pow_dvd_iff.mp (negative_order A hA k) d
      simp only [Finset.mem_range] at hnot
      omega
    rw [hp, hn]
    simp only [regularSum, coeff_mk, pair, map_add, Finset.sum_add_distrib]
    abel

private theorem bilateral_normalization (u : PowerSeries ℚ) (hu : constantCoeff u = 1) :
    bilateralSum (X * u) = HahnSeries.single (-1 : ℤ) 1 *
      (HahnSeries.ofPowerSeries ℤ ℚ) (invOfUnit u 1 + X * regularSum (X * u)) := by
  rw [bilateralSum, normalized_sum u hu]


private theorem X_laurent_inverse : ((X : PowerSeries ℚ) : LaurentSeries ℚ)⁻¹ =
    HahnSeries.single (-1 : ℤ) 1 := by
  simpa only [PowerSeries.coe_X, inv_one] using
    (HahnSeries.inv_single (1 : ℤ) (1 : ℚ))

private theorem isGF_fixed (A : PowerSeries ℚ) (h0 : constantCoeff A = 0) (h1 : coeff 1 A = 1) :
    IsGF A ↔ A = X * (1 + A * regularSum A) := by
  obtain ⟨u, rfl⟩ := X_dvd_iff.mpr h0
  have hu : constantCoeff u = 1 := by simpa using h1
  have hv : invOfUnit u 1 * u = 1 := invOfUnit_mul _ 1 hu
  have hs : (HahnSeries.single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) ≠ 0 := by simp
  have he : IsGF (X * u) ↔ invOfUnit u 1 + X * regularSum (X * u) = 1 := by
    change (constantCoeff (X * u) = 0 ∧ coeff 1 (X * u) = 1 ∧ _) ↔ _
    rw [and_iff_right (by simp), and_iff_right h1,
      X_laurent_inverse, bilateral_normalization u hu]
    constructor
    · intro h
      apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ))
      apply mul_left_cancel₀ hs
      simpa only [map_one, mul_one] using h.symm
    · intro h
      rw [h, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
  rw [he]
  constructor
  · intro hn
    have hu' : u = 1 + X * u * regularSum (X * u) := by
      linear_combination hv - u * hn
    calc
      X * u = X * (1 + X * u * regularSum (X * u)) := congrArg (fun v => X * v) hu'
      _ = X * (1 + (X * u) * regularSum (X * u)) := by ring
  · intro hn
    have hu' : u = 1 + (X * u) * regularSum (X * u) :=
      mul_left_cancel₀ (X_ne_zero (R := ℚ)) hn
    linear_combination (1 - X * regularSum (X * u)) * hv - invOfUnit u 1 * hu'


private theorem rationalT_zero : constantCoeff (T.map (Int.castRingHom ℚ)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
    T_zero, map_one]
private theorem rationalB_zero : constantCoeff (B.map (Int.castRingHom ℚ)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
    B_zero, map_zero]
private theorem rationalB_one : coeff 1 (B.map (Int.castRingHom ℚ)) = 1 := by simp [B_one]

private theorem T_subst (A : PowerSeries ℚ) (hA : constantCoeff A = 0) :
    (T.map (Int.castRingHom ℚ)).subst A = 1 + A * regularSum A := by
  have hs : HasSubst A := .of_constantCoeff_zero hA
  have hh : (regularSum (X : PowerSeries ℤ)).map (Int.castRingHom ℚ) = regularSum (X : PowerSeries ℚ) := by
    rw [regular_map _ X (by simp), map_X]
  simp only [T, map_add, map_one, map_mul, map_X, hh]
  rw [subst_add hs, subst_mul hs, subst_X hs, regular_subst A hA,
    ← coe_substAlgHom hs, map_one]

private theorem B_subst_fixed (A : PowerSeries ℚ) (hA : constantCoeff A = 0) :
    (B.map (Int.castRingHom ℚ)).subst A = X ↔ A = X * (1 + A * regularSum A) := by
  have hs : HasSubst A := .of_constantCoeff_zero hA
  have hb : (B.map (Int.castRingHom ℚ)) = X * invOfUnit (T.map (Int.castRingHom ℚ)) 1 := by
    rw [B, map_mul, map_X,
      D5.S1.Recurrence.Residue.QuotientThetaCompositionModFour.map_inverse _ _ T_zero]
  rw [hb, subst_mul hs, subst_X hs, subst_inverse A (T.map (Int.castRingHom ℚ)) hA rationalT_zero,
    T_subst A hA]
  have ht : constantCoeff (1 + A * regularSum A) = 1 := by simp [hA]
  have hv : invOfUnit (1 + A * regularSum A) 1 * (1 + A * regularSum A) = 1 :=
    invOfUnit_mul _ 1 ht
  constructor
  · intro he
    calc
      A = A * (invOfUnit (1 + A * regularSum A) 1 * (1 + A * regularSum A)) := by rw [hv, mul_one]
      _ = X * (1 + A * regularSum A) := by rw [← mul_assoc, he]
  · intro he
    calc
      A * invOfUnit (1 + A * regularSum A) 1 =
          (X * (1 + A * regularSum A)) * invOfUnit (1 + A * regularSum A) 1 :=
        congrArg (fun a => a * invOfUnit (1 + A * regularSum A) 1) he
      _ = X * (invOfUnit (1 + A * regularSum A) 1 * (1 + A * regularSum A)) := by ring
      _ = X := by rw [hv, mul_one]

private theorem rationalA_zero : constantCoeff (integralA.map (Int.castRingHom ℚ)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
    integralA_zero, map_zero]
private theorem rationalA_one : coeff 1 (integralA.map (Int.castRingHom ℚ)) = 1 := by simp [integralA_one]

private theorem rational_reversion : (B.map (Int.castRingHom ℚ)).subst (integralA.map (Int.castRingHom ℚ)) = X := by
  have he := congrArg (PowerSeries.map (Int.castRingHom ℚ)) reversion
  have hm : PowerSeries.map (Int.castRingHom ℚ) (B.subst integralA) =
      (B.map (Int.castRingHom ℚ)).subst (integralA.map (Int.castRingHom ℚ)) := map_subst (.of_constantCoeff_zero integralA_zero) _
  rw [hm, map_X] at he
  exact he

private theorem rationalA_isGF : IsGF (integralA.map (Int.castRingHom ℚ)) :=
  (isGF_fixed (integralA.map (Int.castRingHom ℚ)) rationalA_zero rationalA_one).mpr
    ((B_subst_fixed (integralA.map (Int.castRingHom ℚ)) rationalA_zero).mp rational_reversion)

private theorem solution_unique (A : PowerSeries ℚ) (hA : IsGF A) : A = (integralA.map (Int.castRingHom ℚ)) := by
  have he := (B_subst_fixed A hA.1).mpr ((isGF_fixed A hA.1 hA.2.1).mp hA)
  have hunit : IsUnit (coeff 1 (B.map (Int.castRingHom ℚ))) := rationalB_one ▸ isUnit_one
  exact (eq_substInvOfIsUnit_of_subst_eq_X (B.map (Int.castRingHom ℚ)) rationalB_zero hunit
    (.of_constantCoeff_zero hA.1) he).trans
    (eq_substInvOfIsUnit_of_subst_eq_X (B.map (Int.castRingHom ℚ)) rationalB_zero hunit
      (.of_constantCoeff_zero rationalA_zero) rational_reversion).symm

private theorem integralA_even (n : ℕ) (hn : 1 < n) : Even (coeff n integralA) := by
  have he := congrArg (coeff n) integralA_mod_two
  have hz : ((coeff n integralA : ℤ) : ZMod 2) = 0 := by
    simpa [coeff_map, coeff_X, show n ≠ 1 from Nat.ne_of_gt hn] using he
  exact ZMod.intCast_eq_zero_iff_even.mp hz

theorem result : D5.S1.Recurrence.Invariants.HannaBilateralReversionParity.claim := by
  refine ⟨⟨(integralA.map (Int.castRingHom ℚ)), rationalA_isGF⟩, ?_⟩
  intro A hA n hn
  rw [solution_unique A hA]
  exact ⟨coeff n integralA, by simp [coeff_map], integralA_even n hn⟩

end D5.S1.Recurrence.Invariants.HannaBilateralReversionParity
