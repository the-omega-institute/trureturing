/- GID: D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral construction and geometric reduction prove Hanna mod-three coefficients. -/

/-
proof_shape: step_zero: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integralT, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integralT_spec, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.normalized_unique.
proof_shape: step_agree: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integralT, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integralT_spec, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.normalized_unique.
proof_shape: integralT_spec: content; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integral_equation.
proof_shape: normalized_unique: content; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.equation_unique.
proof_shape: normalized_iff: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integral_equation, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.equation_unique.
proof_shape: original_iff: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integral_equation, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.equation_unique.
proof_shape: integral_equation: content; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integral_mod_three, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.rational_isGF.
proof_shape: equation_unique: content; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integral_mod_three, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.result.
proof_shape: map_equation: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integral_mod_three, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.rational_isGF.
proof_shape: isGF_iff: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.rational_isGF, D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.result.
proof_shape: geometric_equation: bind-only; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.integral_mod_three.
proof_shape: integral_mod_three: content; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.result.
proof_shape: rational_isGF: content; consumers: D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree.result.
proof_shape: result: content; consumers: settling result.
escape_witness: none
admission_basis: open-problem-resolution (#18851; Proved)
Direct frozen dependencies: existing power-series suppliers at their original declaration addresses;
declaration identities and the elaborated dependency closure are reported in the handover.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19089.
Unbounded existence, uniqueness, and coefficient identities; no finite-instance computation.
The source predicates IsGF and claim retain their literal expressions.
-/

import D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import Mathlib.RingTheory.LaurentSeries

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree

open PowerSeries

/-- OEIS A377100: "G.f. A(x) satisfies A(x) = A(x^3)/A(x^2) + A(x)^2", with A(x) = x + x^2 + ...
(offset 1). The quotient is taken in the field of Laurent series. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    (A : LaurentSeries ℚ) =
      (PowerSeries.subst (X ^ 3 : PowerSeries ℚ) A : LaurentSeries ℚ) /
          (PowerSeries.subst (X ^ 2 : PowerSeries ℚ) A : LaurentSeries ℚ) +
        (A : LaurentSeries ℚ) ^ 2

/-- OEIS A377100 (P. D. Hanna), conjecture: "a(n) == 1 (mod 3) for n >= 1", where a(n) = [x^n] A(x).
The terms are integers. -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, coeff n A = m ∧ m ≡ 1 [ZMOD 3]

end D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree

namespace D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree
open D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction D5.S1.Recurrence.Invariants.UnitReversionSquareParity D5.S1.Recurrence.Invariants.ScaledReversionCongruence
open PowerSeries
variable {R : Type*} [CommRing R]

private noncomputable def step (b : PowerSeries R) : PowerSeries R :=
  b.subst (X ^ 3) * invOfUnit (b.subst (X ^ 2)) 1 + X * b ^ 2

private theorem step_zero {b : PowerSeries R} (hb : constantCoeff b = 1) :
    constantCoeff (step b) = 1 := by
  simp [step, hb]

private theorem step_agree {d : ℕ} (hd : 1 ≤ d) {b c : PowerSeries R}
    (hb : constantCoeff b = 1) (hc : constantCoeff c = 1) (h : Agree d b c) :
    Agree (d + 1) (step b) (step c) := by
  have hs2 := subst_outer_agree h (show (X : PowerSeries R) ^ 2 ∣ X ^ 2 from dvd_rfl)
  have hs3 := subst_outer_agree h (show (X : PowerSeries R) ^ 2 ∣ X ^ 3 from
    ⟨X, by ring⟩)
  have hb2 : constantCoeff (b.subst ((X : PowerSeries R) ^ 2)) = 1 := by simpa using hb
  have hc2 : constantCoeff (c.subst ((X : PowerSeries R) ^ 2)) = 1 := by simpa using hc
  have hi := D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_inv hb2 hc2 hs2
  have hp := agree_mul hs3 hi
  have hx := agree_X (agree_pow h 2)
  intro n hn
  simp only [step, map_add, hp n (by omega), hx n hn]

private noncomputable def integralT : PowerSeries ℤ :=
  Classical.choose (exists_unique_fixed (step (R := ℤ)) (fun _ h => step_zero h)
    (fun hd hb hc h => step_agree hd hb hc h))

private theorem integralT_spec : constantCoeff integralT = 1 ∧ integralT = step integralT := by
  have hs := Classical.choose_spec (exists_unique_fixed (step (R := ℤ)) (fun _ h => step_zero h)
    (fun hd hb hc h => step_agree hd hb hc h))
  exact ⟨hs.1, hs.2.1⟩

private theorem normalized_unique {b c : PowerSeries R}
    (hb : constantCoeff b = 1) (hc : constantCoeff c = 1)
    (hbe : b = step b) (hce : c = step c) : b = c := by
  obtain ⟨f, hf, hfe, hu⟩ := exists_unique_fixed (step (R := R))
    (fun _ h => step_zero h) (fun hd hb hc h => step_agree hd hb hc h)
  exact (hu b hb hbe).trans (hu c hc hce).symm

private theorem normalized_iff (b : PowerSeries R) (hb : constantCoeff b = 1) :
    b = step b ↔ b * b.subst (X ^ 2) = b.subst (X ^ 3) + X * b ^ 2 * b.subst (X ^ 2) := by
  have hs : constantCoeff (b.subst ((X : PowerSeries R) ^ 2)) = 1 := by simpa using hb
  have hi := invOfUnit_mul (b.subst (X ^ 2)) 1 hs
  have hu : IsUnit (b.subst (X ^ 2)) := isUnit_iff_constantCoeff.mpr (hs ▸ isUnit_one)
  constructor
  · intro he
    calc
      b * b.subst (X ^ 2) = step b * b.subst (X ^ 2) := congrArg (fun t => t * b.subst (X ^ 2)) he
      _ = _ := by dsimp [step]; linear_combination b.subst (X ^ 3) * hi
  · intro he
    apply hu.mul_right_cancel
    dsimp [step]
    linear_combination he - b.subst (X ^ 3) * hi

private theorem original_iff (b : PowerSeries R) :
    (X * b) * (X * b).subst (X ^ 2) = (X * b).subst (X ^ 3) +
      (X * b) ^ 2 * (X * b).subst (X ^ 2) ↔
    b * b.subst (X ^ 2) = b.subst (X ^ 3) + X * b ^ 2 * b.subst (X ^ 2) := by
  have s2 : HasSubst ((X : PowerSeries R) ^ 2) := .X_pow (by decide)
  have s3 : HasSubst ((X : PowerSeries R) ^ 3) := .X_pow (by decide)
  rw [subst_mul s2, subst_X s2, subst_mul s3, subst_X s3]
  constructor
  · intro he
    apply X_pow_mul_injective (k := 3)
    linear_combination he
  · intro he
    linear_combination X ^ 3 * he

private noncomputable def integralA : PowerSeries ℤ := X * integralT

private theorem integral_equation : constantCoeff integralA = 0 ∧ coeff 1 integralA = 1 ∧
    integralA * integralA.subst (X ^ 2) = integralA.subst (X ^ 3) +
      integralA ^ 2 * integralA.subst (X ^ 2) := by
  refine ⟨by simp [integralA], by simpa [integralA] using integralT_spec.1, ?_⟩
  exact (original_iff integralT).mpr ((normalized_iff integralT integralT_spec.1).mp integralT_spec.2)

end D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree

namespace D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree
open D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction D5.S1.Recurrence.Invariants.UnitReversionSquareParity D5.S1.Recurrence.Invariants.ScaledReversionCongruence PowerSeries

private def Equation {R : Type*} [CommRing R] (f : PowerSeries R) : Prop :=
  f * f.subst (X ^ 2) = f.subst (X ^ 3) + f ^ 2 * f.subst (X ^ 2)

private theorem equation_unique {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (he : Equation f) (he' : Equation g) : f = g := by
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr hf
  obtain ⟨c, rfl⟩ := X_dvd_iff.mpr hg
  have hb : constantCoeff b = 1 := by simpa using hf1
  have hc : constantCoeff c = 1 := by simpa using hg1
  have heq := normalized_unique hb hc
    ((normalized_iff b hb).mpr ((original_iff b).mp he))
    ((normalized_iff c hc).mpr ((original_iff c).mp he'))
  rw [heq]

private theorem map_equation {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) {f : PowerSeries R} (hf : Equation f) : Equation (f.map hom) := by
  have he := congrArg (PowerSeries.map hom) hf
  simpa only [Equation, map_add, map_mul, map_pow,
    map_subst_pow hom f 2 (by decide), map_subst_pow hom f 3 (by decide)] using he

private theorem isGF_iff (f : PowerSeries ℚ) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1) :
    IsGF f ↔ Equation f := by
  let b : PowerSeries ℚ := f.subst ((X : PowerSeries ℚ) ^ 2)
  let c : PowerSeries ℚ := f.subst ((X : PowerSeries ℚ) ^ 3)
  let ι : PowerSeries ℚ →+* LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ
  have hb : b ≠ 0 := by
    intro hz
    have h := congrArg (coeff 2) hz
    simp [b, coeff_subst_X_pow (by decide : 2 ≠ 0), h1] at h
  have hib : ι b ≠ 0 := by
    intro hz
    exact hb (HahnSeries.ofPowerSeries_injective (hz.trans (map_zero ι).symm))
  constructor
  · intro he
    have heq : ι f = ι c / ι b + (ι f) ^ 2 := he.2.2
    have hc : ι f * ι b = ι c + (ι f) ^ 2 * ι b := by
      calc
        ι f * ι b = (ι c / ι b + (ι f) ^ 2) * ι b :=
          congrArg (fun z : LaurentSeries ℚ => z * ι b) heq
        _ = _ := by rw [add_mul, div_mul_cancel₀ _ hib]
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ))
    change ι (f * b) = ι (c + f ^ 2 * b)
    simpa only [map_mul, map_add, map_pow] using hc
  · intro he
    have hc : ι f * ι b = ι c + (ι f) ^ 2 * ι b := by
      have hh := congrArg ι he
      simpa only [map_mul, map_add, map_pow] using hh
    have heq : ι f = ι c / ι b + (ι f) ^ 2 := by
      apply sub_eq_iff_eq_add.mp
      apply (eq_div_iff hib).mpr
      linear_combination hc
    exact ⟨h0, h1, heq⟩

private theorem geometric_equation : Equation (geometric : PowerSeries (ZMod 3)) := by
  let f : PowerSeries (ZMod 3) := geometric
  let d : PowerSeries (ZMod 3) := 1 - X
  let u := f.subst ((X : PowerSeries (ZMod 3)) ^ 2)
  let v := f.subst ((X : PowerSeries (ZMod 3)) ^ 3)
  have hf : f * d = X := geometric_mul
  have hu : u * (1 - X ^ 2) = X ^ 2 := geometric_subst_mul 2 (by decide)
  have hv : v * (1 - X ^ 3) = X ^ 3 := geometric_subst_mul 3 (by decide)
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    rw [← map_ofNat C 3, show (3 : ZMod 3) = 0 by decide, map_zero]
  have hd3 : d ^ 3 = 1 - X ^ 3 := by
    dsimp [d]
    linear_combination (-X + X ^ 2) * h3
  have hid : IsUnit d := isUnit_iff_constantCoeff.mpr (by simp [d])
  have hi2 : IsUnit (1 - (X : PowerSeries (ZMod 3)) ^ 2) :=
    isUnit_iff_constantCoeff.mpr (by simp)
  change f * u = v + f ^ 2 * u
  apply (hid.pow 2 |>.mul hi2).mul_right_cancel
  change (f * u) * (d ^ 2 * (1 - X ^ 2)) = (v + f ^ 2 * u) * (d ^ 2 * (1 - X ^ 2))
  have hden : d ^ 2 * (1 - X ^ 2) = (1 - X ^ 3) * (1 + X) := by
    calc
      d ^ 2 * (1 - X ^ 2) = d ^ 3 * (1 + X) := by dsimp [d]; ring
      _ = _ := by rw [hd3]
  linear_combination u * (1 - X ^ 2) * (d - f * d - X) * hf +
    (X * d - X ^ 2) * hu - (1 + X) * hv - v * hden - X ^ 4 * h3

private theorem integral_mod_three : integralA.map (Int.castRingHom (ZMod 3)) = geometric := by
  have h0 : constantCoeff (integralA.map (Int.castRingHom (ZMod 3))) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, integral_equation.1, map_zero]
  have h1 : coeff 1 (integralA.map (Int.castRingHom (ZMod 3))) = 1 := by simp [integral_equation.2.1]
  exact equation_unique h0 geometric_zero h1 geometric_one
    (map_equation _ integral_equation.2.2) geometric_equation


private theorem rational_isGF : IsGF (integralA.map (Int.castRingHom ℚ)) := by
  have h0 : constantCoeff (integralA.map (Int.castRingHom ℚ)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [coeff_zero_eq_constantCoeff, integral_equation.1]
  have h1 : coeff 1 (integralA.map (Int.castRingHom ℚ)) = 1 := by simp [integral_equation.2.1]
  exact (isGF_iff _ h0 h1).mpr (map_equation _ integral_equation.2.2)

theorem result : claim := by
  refine ⟨⟨(integralA.map (Int.castRingHom ℚ)), rational_isGF⟩, ?_⟩
  intro f hf n hn
  have heq : f = (integralA.map (Int.castRingHom ℚ)) := equation_unique hf.1 rational_isGF.1 hf.2.1 rational_isGF.2.1
    ((isGF_iff f hf.1 hf.2.1).mp hf) ((isGF_iff _ rational_isGF.1 rational_isGF.2.1).mp rational_isGF)
  refine ⟨coeff n integralA, ?_, ?_⟩
  · rw [heq]
    simp
  · apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    have h := congrArg (coeff n) integral_mod_three
    simpa only [coeff_map, Int.coe_castRingHom, Int.cast_one, geometric_coeff n hn] using h

end D5.S1.Recurrence.Invariants.HannaCubeSquareQuotientModThree
