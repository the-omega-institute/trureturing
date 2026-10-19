/- GID: D5/S1/Recurrence/Invariants/HannaSquareCompositionModFour
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaSquareCompositionModFour
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Contracting integral series and a second binary digit settle Hanna's A372527. -/

/-
result:
  proof_shape: content (coefficient stabilization constructs the integral solution).
  escape_witness: none (the module settles an external named open problem).
  admission_basis: open-problem-resolution (#18859; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19133
Private theorem proof_shape and consumers:
  argument_zero: bind-only; consumer: denominator_zero.
  denominator_zero: bind-only; consumer: step_mul.
  step_zero: bind-only; consumer: approximation_zero.
  step_mul: bind-only; consumer: normalized_unique.
  argument_agree: bind-only; consumer: denominator_agree.
  denominator_agree: bind-only; consumer: step_agree.
  step_agree: bind-only; consumer: normalized_unique.
  normalized_unique: content; consumer: integral_unique.
  approximation_zero: bind-only; consumer: approximation_stable.
  approximation_stable: content; consumer: normalized_agree.
  normalized_agree: content; consumer: normalized_fixed.
  normalized_zero: bind-only; consumer: normalized_fixed.
  normalized_fixed: content; consumer: integral_equation.
  normalize_solution: bind-only; consumer: integral_unique.
  integral_unique: content; consumer: mod_four_solution.
  map_integral: bind-only; consumer: exists_integral_solution.
  integral_equation: content; consumer: exists_integral_solution.
  rational_integral_iff: bind-only; consumer: exists_integral_solution.
  exists_integral_solution: content; consumer: result.
  doubling_val: bind-only; consumer: doubleLift_even.
  doubleLift_X: bind-only; consumer: second_digit_equation.
  doubleLift_subst: bind-only; consumer: second_digit_equation.
  doubleLift_even: bind-only; consumer: doubleLift_annihilate.
  doubleLift_annihilate: bind-only; consumer: residue_equation.
  second_digit_equation: bind-only; consumer: residue_equation.
  residue_zero: bind-only; consumer: residue_equation.
  residue_equation: bind-only; consumer: mod_four_solution.
  mod_four_solution: content; consumer: result.
  residue_coefficient: bind-only; consumer: result.
Direct frozen dependencies:
  UnitReversionSquareParity: Agree, agree_iff, agree_pow, agree_mul, agree_X,
  subst_inner_agree, subst_outer_agree, subst_constant.
  CubicFifteenSubstitutionParity: powerTwoSeries, prime_power_subst,
  power_two_zero, thue_series_equation.
  AlternatingDyadicReversionModFour: four_zero.
  NegativePowerDiagonalModPrime: inverse_difference.
The rational equation and claim retain the expressions in #18859. The
coefficient-prefix and power-of-two constructions use their existing owners.
The additive coefficient transport uses PowerSeries.mk and AddMonoidHom.compLeft;
the coefficient homomorphism uses ZMod.lift.
The second congruence applies to n > 1, since the source data have a(1) = 1.
-/

import D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.AlternatingDyadicReversionModFour

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaSquareCompositionModFour

open PowerSeries

/-- OEIS A372527: "Expansion of g.f. A(x) satisfying A( A(x)^2 ) = x*A(x)/(1 - 2*A(x))", with
A(x) = x + 2*x^2 + ... (offset 1). -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    PowerSeries.subst (A ^ 2) A = X * A * (1 - 2 * A)⁻¹

/-- OEIS A372527 (P. D. Hanna), conjecture: "a(2^k + 1) == 2 (mod 4) for k >= 0, and a(n) == 0 (mod 4)
for n > 0 when n is not of the form 2^k + 1", where a(n) = [x^n] A(x). The second clause is stated for
n > 1: a(1) = 1. The terms are integers. -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A →
      (∀ k : ℕ, ∃ m : ℤ, coeff (2 ^ k + 1) A = m ∧ m ≡ 2 [ZMOD 4]) ∧
        ∀ n : ℕ, 1 < n → (¬ ∃ k : ℕ, n = 2 ^ k + 1) → ∃ m : ℤ, coeff n A = m ∧ m ≡ 0 [ZMOD 4]

end D5.S1.Recurrence.Invariants.HannaSquareCompositionModFour

open PowerSeries
namespace D5.S1.Recurrence.Invariants.HannaSquareCompositionModFour
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity

section Normalized
variable {R : Type*} [CommRing R]

private noncomputable def argument (b : PowerSeries R) : PowerSeries R := X ^ 2 * b ^ 2
private noncomputable def denominator (b : PowerSeries R) : PowerSeries R :=
  (1 - 2 * X * b) * b.subst (argument b)
private noncomputable def step (b : PowerSeries R) : PowerSeries R := invOfUnit (denominator b) 1

private theorem argument_zero (b : PowerSeries R) : constantCoeff (argument b) = 0 := by
  simp [argument]

private theorem denominator_zero {b : PowerSeries R} (hb : constantCoeff b = 1) :
    constantCoeff (denominator b) = 1 := by
  simp [denominator, subst_constant _ _ (argument_zero b), hb]

private theorem step_zero (b : PowerSeries R) : constantCoeff (step b) = 1 := by
  simp [step, constantCoeff_invOfUnit]

private theorem step_mul {b : PowerSeries R} (hb : constantCoeff b = 1) :
    step b * denominator b = 1 :=
  invOfUnit_mul _ _ (denominator_zero hb)

private theorem argument_agree {d : ℕ} {b c : PowerSeries R} (h : Agree d b c) :
    Agree (d + 2) (argument b) (argument c) := by
  simpa [argument, pow_two, mul_assoc] using agree_X (agree_X (agree_pow h 2))

private theorem denominator_agree {d : ℕ} {b c : PowerSeries R}
    (hd : 1 ≤ d) (h : Agree d b c) :
    Agree (d + 1) (denominator b) (denominator c) := by
  apply agree_mul
  · intro n hn
    have hh := agree_mul (show Agree (d + 1) (2 : PowerSeries R) 2 from fun _ _ => rfl) (agree_X h)
    simpa only [mul_assoc, map_sub] using congrArg (fun t : R => coeff n 1 - t) (hh n hn)
  · have hi := subst_inner_agree (argument_agree h) b (argument_zero b) (argument_zero c)
    have ho := subst_outer_agree h (show X ^ 2 ∣ argument c from ⟨c ^ 2, rfl⟩)
    intro n hn
    exact (hi n (by omega)).trans (ho n (by omega))

private theorem step_agree {d : ℕ} {b c : PowerSeries R}
    (hb : constantCoeff b = 1) (hc : constantCoeff c = 1)
    (hd : 1 ≤ d) (h : Agree d b c) : Agree (d + 1) (step b) (step c) := by
  apply (agree_iff _ _ _).mpr
  have hdv := (agree_iff _ _ _).mp (denominator_agree hd h)
  have he : step b - step c = (denominator c - denominator b) * (step b * step c) := by
    calc
      step b - step c = (denominator b - denominator c) * (-(step b * step c)) := by
        simpa only [step] using
          D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime.inverse_difference
            (denominator b) (denominator c) (denominator_zero hb) (denominator_zero hc)
      _ = (denominator c - denominator b) * (step b * step c) := by ring
  rw [he]
  have hdv' : (X : PowerSeries R) ^ (d + 1) ∣ denominator c - denominator b := by
    simpa only [neg_sub] using dvd_neg.mpr hdv
  exact dvd_mul_of_dvd_left hdv' _

private theorem normalized_unique {b c : PowerSeries R}
    (hb : constantCoeff b = 1) (hc : constantCoeff c = 1)
    (he : b * denominator b = 1) (hf : c * denominator c = 1) : b = c := by
  have hfb : b = step b := by
    exact left_inv_eq_right_inv he (by simpa only [mul_comm] using step_mul hb)
  have hfc : c = step c := by
    exact left_inv_eq_right_inv hf (by simpa only [mul_comm] using step_mul hc)
  have hall : ∀ d, Agree (d + 1) b c := by
    intro d
    induction d with
    | zero =>
      intro n hn
      have hn0 : n = 0 := Nat.lt_one_iff.mp hn
      subst n
      simp only [coeff_zero_eq_constantCoeff, hb, hc]
    | succ d ih => simpa only [← hfb, ← hfc] using step_agree hb hc (by omega : 1 ≤ d + 1) ih
  ext n
  exact hall n n (by omega)

private theorem approximation_zero (j : ℕ) : constantCoeff (((step (R := R))^[j]) 1) = 1 := by
  cases j <;> simp [Function.iterate_succ_apply', step_zero]

private theorem approximation_stable {d j : ℕ} (hj : d ≤ j) :
    Agree (d + 1) (((step (R := R))^[d]) 1) (((step (R := R))^[j]) 1) := by
  induction d generalizing j with
  | zero =>
    intro n hn
    have hn0 : n = 0 := Nat.lt_one_iff.mp hn
    subst n
    simp [coeff_zero_eq_constantCoeff, approximation_zero]
  | succ d ih =>
    cases j with
    | zero => omega
    | succ j =>
      simpa only [Function.iterate_succ_apply'] using
        step_agree (approximation_zero d) (approximation_zero j) (by omega) (ih (by omega))

private noncomputable def normalizedSeries : PowerSeries ℤ :=
  mk fun n => coeff n (((step (R := ℤ))^[n]) 1)

private theorem normalized_agree (d : ℕ) :
    Agree (d + 1) normalizedSeries (((step (R := ℤ))^[d]) 1) := by
  intro n hn
  simpa only [normalizedSeries, coeff_mk] using
    approximation_stable (R := ℤ) (by omega : n ≤ d) n (by omega)

private theorem normalized_zero : constantCoeff normalizedSeries = 1 := by
  simpa [coeff_zero_eq_constantCoeff, approximation_zero] using normalized_agree 0 0 (by omega)

private theorem normalized_fixed : normalizedSeries * denominator normalizedSeries = 1 := by
  have hf : normalizedSeries = step normalizedSeries := by
    ext n
    have h1 := normalized_agree (n + 1) n (by omega)
    have h2 := step_agree normalized_zero (approximation_zero n)
      (by omega : 1 ≤ n + 1) (normalized_agree n) n (by omega)
    exact (h1.trans (congrArg (coeff n) (Function.iterate_succ_apply' step n 1))).trans h2.symm
  calc
    normalizedSeries * denominator normalizedSeries = step normalizedSeries * denominator normalizedSeries :=
      congrArg (fun t => t * denominator normalizedSeries) hf
    _ = 1 := step_mul normalized_zero

end Normalized
end D5.S1.Recurrence.Invariants.HannaSquareCompositionModFour

namespace D5.S1.Recurrence.Invariants.HannaSquareCompositionModFour
open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity

section Bridge
variable {R : Type*} [CommRing R]

private def IsIntegralGF (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ coeff 1 f = 1 ∧ f.subst (f ^ 2) * (1 - 2 * f) = X * f

private theorem normalize_solution {f : PowerSeries R} (hf : IsIntegralGF f) :
    ∃ b : PowerSeries R, f = X * b ∧ constantCoeff b = 1 ∧ b * denominator b = 1 := by
  obtain ⟨b, he⟩ := X_dvd_iff.mpr hf.1
  have hb : constantCoeff b = 1 := by simpa [he] using hf.2.1
  have hu : IsUnit b := isUnit_iff_constantCoeff.mpr (by rw [hb]; exact isUnit_one)
  refine ⟨b, he, hb, ?_⟩
  have hs : HasSubst ((X * b) ^ 2) := .of_constantCoeff_zero (show constantCoeff ((X * b) ^ 2) = 0 by simp)
  have harg : (X * b) ^ 2 = argument b := mul_pow X b 2
  have ht : X ^ 2 * (b * (b * denominator b)) = X ^ 2 * b := by
    calc
      X ^ 2 * (b * (b * denominator b)) =
          (X * b).subst ((X * b) ^ 2) * (1 - 2 * (X * b)) := by
        rw [subst_mul hs, subst_X hs, harg]
        dsimp [denominator, argument]
        ring
      _ = X * (X * b) := by simpa only [he] using hf.2.2
      _ = X ^ 2 * b := by ring
  apply hu.mul_left_cancel
  simpa only [mul_one] using X_pow_mul_cancel ht

private theorem integral_unique {f g : PowerSeries R}
    (hf : IsIntegralGF f) (hg : IsIntegralGF g) : f = g := by
  obtain ⟨b, rfl, hb, he⟩ := normalize_solution hf
  obtain ⟨c, rfl, hc, hh⟩ := normalize_solution hg
  rw [normalized_unique hb hc he hh]

private theorem map_integral {S : Type*} [CommRing S] (hom : R →+* S)
    {f : PowerSeries R} (hf : IsIntegralGF f) : IsIntegralGF (f.map hom) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hf.1, map_zero]
  · rw [coeff_map, hf.2.1, map_one]
  · have he := congrArg (PowerSeries.map hom) hf.2.2
    have hs : HasSubst (f ^ 2) := .of_constantCoeff_zero (show constantCoeff (f ^ 2) = 0 by simp [hf.1])
    have hh : PowerSeries.map hom (f.subst (f ^ 2)) = (PowerSeries.map hom f).subst (PowerSeries.map hom (f ^ 2)) := map_subst hs _
    simp only [map_mul, map_sub, map_one, map_ofNat, map_X] at he
    rw [hh] at he
    simpa only [map_pow] using he

end Bridge

private noncomputable def integralSeries : PowerSeries ℤ := X * normalizedSeries

private theorem integral_equation : IsIntegralGF integralSeries := by
  refine ⟨by simp [integralSeries], by simp [integralSeries, normalized_zero], ?_⟩
  have hs : HasSubst ((X * normalizedSeries) ^ 2) := .of_constantCoeff_zero (show constantCoeff ((X * normalizedSeries) ^ 2) = 0 by simp)
  have hi : (X * normalizedSeries) ^ 2 = argument normalizedSeries := mul_pow X normalizedSeries 2
  simp only [integralSeries]
  rw [subst_mul hs, subst_X hs, hi]
  have hn := normalized_fixed
  dsimp [denominator, argument] at hn ⊢
  linear_combination (X ^ 2 * normalizedSeries) * hn

private theorem rational_integral_iff {f : PowerSeries ℚ} : IsGF f ↔ IsIntegralGF f := by
  constructor
  · rintro ⟨h0, h1, he⟩
    refine ⟨h0, h1, ?_⟩
    rw [he, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp [h0]), mul_one]
  · rintro ⟨h0, h1, he⟩
    refine ⟨h0, h1, ?_⟩
    have hm := congrArg (fun t => t * (1 - 2 * f)⁻¹) he
    simpa only [mul_assoc, PowerSeries.mul_inv_cancel (1 - 2 * f) (by simp [h0]), mul_one] using hm

private theorem exists_integral_solution :
    IsGF (integralSeries.map (Int.castRingHom ℚ)) ∧
      ∀ f : PowerSeries ℚ, IsGF f → f = integralSeries.map (Int.castRingHom ℚ) := by
  have hi := map_integral (Int.castRingHom ℚ) integral_equation
  exact ⟨rational_integral_iff.mpr hi, fun f hf => integral_unique (rational_integral_iff.mp hf) hi⟩

end D5.S1.Recurrence.Invariants.HannaSquareCompositionModFour

namespace D5.S1.Recurrence.Invariants.HannaSquareCompositionModFour
attribute [local instance] Classical.propDecidable
open PowerSeries
open D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity

private noncomputable def doubling : ZMod 2 →+ ZMod 4 :=
  ZMod.lift 2 ⟨(AddMonoidHom.mulLeft (2 : ZMod 4)).comp (Int.castAddHom (ZMod 4)),
    by decide⟩

private theorem doubling_val (z : ZMod 2) : doubling z = 2 * (z.val : ZMod 4) := by
  exact ZMod.valMinAbs_inj.mp rfl

private theorem doubleLift_X : (mk ((doubling.compLeft ℕ) (fun n => coeff n (X : PowerSeries (ZMod 2)))) : PowerSeries (ZMod 4)) = 2 * X := by
  ext n
  simp only [coeff_mk, AddMonoidHom.compLeft_apply, Function.comp_apply, doubling_val, coeff_X, coeff_ofNat_mul]
  split_ifs <;> decide

private theorem doubleLift_subst (f : PowerSeries (ZMod 2)) :
    (mk ((doubling.compLeft ℕ) (fun n => coeff n (f.subst (X ^ 2)))) : PowerSeries (ZMod 4)) = ((mk ((doubling.compLeft ℕ) (fun n => coeff n f)) : PowerSeries (ZMod 4))).subst (X ^ 2) := by
  ext n
  simp only [coeff_mk, AddMonoidHom.compLeft_apply, Function.comp_apply, doubling_val, coeff_subst_X_pow (by decide : 2 ≠ 0),
    Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs <;> simp

private theorem doubleLift_even (f : PowerSeries (ZMod 2)) :
    ∃ g : PowerSeries (ZMod 4), (mk ((doubling.compLeft ℕ) (fun n => coeff n f)) : PowerSeries (ZMod 4)) = 2 * g := by
  refine ⟨mk (fun n => ((coeff n f).val : ZMod 4)), ?_⟩
  ext n
  simp [coeff_mk, AddMonoidHom.compLeft_apply, Function.comp_apply, doubling_val, coeff_ofNat_mul]

private theorem doubleLift_annihilate (f : PowerSeries (ZMod 2)) :
    2 * (mk ((doubling.compLeft ℕ) (fun n => coeff n f)) : PowerSeries (ZMod 4)) = 0 ∧ (mk ((doubling.compLeft ℕ) (fun n => coeff n f)) : PowerSeries (ZMod 4)) ^ 2 = 0 := by
  obtain ⟨g, hg⟩ := doubleLift_even f
  rw [hg]
  constructor
  · linear_combination g * AlternatingDyadicReversionModFour.four_zero
  · linear_combination g ^ 2 * AlternatingDyadicReversionModFour.four_zero

-- The doubled version of C(X^2) = X*C + X^3 after factoring C = X*S.
private theorem second_digit_equation :
    ((mk ((doubling.compLeft ℕ) (fun n => coeff n powerTwoSeries)) : PowerSeries (ZMod 4))).subst (X ^ 2) = (mk ((doubling.compLeft ℕ) (fun n => coeff n powerTwoSeries)) : PowerSeries (ZMod 4)) - 2 * X := by
  have he := thue_series_equation.1
  rw [prime_power_subst 2] at he
  have hm :
      (mk ((doubling.compLeft ℕ) (fun n => coeff n powerTwoSeries)) : PowerSeries (ZMod 4)) =
        (mk ((doubling.compLeft ℕ) (fun n => coeff n (X : PowerSeries (ZMod 2)))) : PowerSeries (ZMod 4)) +
        (mk ((doubling.compLeft ℕ) (fun n => coeff n (powerTwoSeries.subst (X ^ 2)))) : PowerSeries (ZMod 4)) := by
    calc
      _ = mk ((doubling.compLeft ℕ) (fun n => coeff n (X + powerTwoSeries.subst (X ^ 2)))) :=
        congrArg (fun f : PowerSeries (ZMod 2) => mk ((doubling.compLeft ℕ) (fun n => coeff n f))) he
      _ = _ := by ext n; simp [AddMonoidHom.compLeft]
  rw [doubleLift_X, doubleLift_subst] at hm
  linear_combination -hm

private noncomputable def residueSeries : PowerSeries (ZMod 4) := X * (1 + (mk ((doubling.compLeft ℕ) (fun n => coeff n powerTwoSeries)) : PowerSeries (ZMod 4)))

private theorem residue_zero : constantCoeff ((mk ((doubling.compLeft ℕ) (fun n => coeff n powerTwoSeries)) : PowerSeries (ZMod 4))) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_mk, AddMonoidHom.compLeft_apply, Function.comp_apply, doubling_val, coeff_zero_eq_constantCoeff, power_two_zero]
  decide

private theorem residue_equation : IsIntegralGF residueSeries := by
  let d : PowerSeries (ZMod 4) := (mk ((doubling.compLeft ℕ) (fun n => coeff n powerTwoSeries)) : PowerSeries (ZMod 4))
  have h2 : 2 * d = 0 := (doubleLift_annihilate powerTwoSeries).1
  have hsquare : d ^ 2 = 0 := (doubleLift_annihilate powerTwoSeries).2
  have ha : residueSeries ^ 2 = X ^ 2 := by
    dsimp [residueSeries]
    change (X * (1 + d)) ^ 2 = X ^ 2
    linear_combination X ^ 2 * hsquare + X ^ 2 * h2
  have hsub : HasSubst ((X : PowerSeries (ZMod 4)) ^ 2) := .X_pow (by decide)
  have hone : subst (X ^ 2 : PowerSeries (ZMod 4)) (1 : PowerSeries (ZMod 4)) = 1 := by
    rw [← coe_substAlgHom hsub, map_one]
  refine ⟨by simp [residueSeries], by
      rw [residueSeries, coeff_succ_X_mul, map_add, coeff_zero_eq_constantCoeff, map_one, residue_zero, add_zero], ?_⟩
  rw [ha]
  have he : d.subst (X ^ 2) = d - 2 * X := second_digit_equation
  dsimp [residueSeries]
  change (X * (1 + d)).subst (X ^ 2) * (1 - 2 * (X * (1 + d))) = X * (X * (1 + d))
  rw [subst_mul hsub, subst_X hsub, subst_add hsub, hone, he]
  linear_combination (2 * X ^ 4 - 2 * X ^ 3 - X ^ 3 * d) * h2 +
    (X ^ 4 - X ^ 3) * AlternatingDyadicReversionModFour.four_zero


private theorem mod_four_solution :
    integralSeries.map (Int.castRingHom (ZMod 4)) = residueSeries :=
  integral_unique (map_integral _ integral_equation) residue_equation

private theorem residue_coefficient (n : ℕ) (hn : 1 < n) :
    coeff n residueSeries = if ∃ k : ℕ, n = 2 ^ k + 1 then 2 else 0 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : m ≠ 0 := by omega
  rw [residueSeries, coeff_succ_X_mul, map_add, coeff_one, ite_eq_right hm, zero_add,
    coeff_mk, AddMonoidHom.compLeft_apply, Function.comp_apply, doubling_val]
  simp only [powerTwoSeries, coeff_mk]
  have hh : (∃ k : ℕ, m = 2 ^ k) ↔ ∃ k : ℕ, m + 1 = 2 ^ k + 1 := by
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by omega⟩
  simp only [Nat.succ_eq_add_one, ← hh]
  split_ifs <;> decide

theorem result : claim := by
  refine ⟨⟨integralSeries.map (Int.castRingHom ℚ), exists_integral_solution.1⟩, ?_⟩
  intro A hA
  have he := exists_integral_solution.2 A hA
  subst A
  have hc (n : ℕ) (hn : 1 < n) :
      ((coeff n integralSeries : ℤ) : ZMod 4) = if ∃ k : ℕ, n = 2 ^ k + 1 then 2 else 0 := by
    have hh := congrArg (coeff n) mod_four_solution
    simpa only [coeff_map, Int.coe_castRingHom] using hh.trans (residue_coefficient n hn)
  constructor
  · intro k
    refine ⟨coeff (2 ^ k + 1) integralSeries, by simp, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ 4).mp
    simpa only [Int.cast_ofNat, ite_eq_left (show ∃ j, 2 ^ k + 1 = 2 ^ j + 1 from ⟨k, rfl⟩)] using
      hc (2 ^ k + 1) (by have hp := Nat.one_le_pow k 2 (by decide); omega)
  · intro n hn hnot
    refine ⟨coeff n integralSeries, by simp, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ 4).mp
    simpa only [Int.cast_zero, ite_eq_right hnot] using hc n hn

end D5.S1.Recurrence.Invariants.HannaSquareCompositionModFour
