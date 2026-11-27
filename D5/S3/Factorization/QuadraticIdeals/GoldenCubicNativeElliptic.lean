/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The native Lucas cubic is the actual two-division field and block depth is CM contact order. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeForwardSplitting
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
open Polynomial D5.S1.Scale GoldenCubicNativeCyclic

def model {R : Type*} [CommRing R] (l d : R) : WeierstrassCurve.Affine R :=
  ⟨0, 0, 0, d^2*(-3*(l^2+3)), d^3*(2*(l^2+3)*l)⟩

theorem model_discriminant {R : Type*} [CommRing R] (l d : R) :
    (model l d).Δ = d^6*(72*(l^2+3))^2 := by
  simp [model, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem model_c4 {R : Type*} [CommRing R] (l d : R) :
    (model l d).c₄ = 144*d^2*(l^2+3) := by
  simp [model, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem model_discriminant_ne {F : Type*} [Field F] [CharZero F] (l : ℤ) {d : F}
    (hd : d ≠ 0) : (model (l:F) d).Δ ≠ 0 := by
  have hb : (l:F)^2+3 ≠ 0 := by exact_mod_cast (show l^2+3 ≠ 0 by positivity)
  rw [model_discriminant]
  exact mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ (mul_ne_zero (by norm_num) hb))

instance modelElliptic {F : Type*} [Field F] [CharZero F] (l : ℤ) {d : F}
    [hd : NeZero d] : (model (l:F) d).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (model_discriminant_ne l hd.out)⟩

theorem model_j (l : ℤ) :
    (model (l:ℚ) 1).j = 1728+(24*(l:ℚ))^2 := by
  have hb : (l:ℚ)^2+3 ≠ 0 := by positivity
  rw [WeierstrassCurve.j_eq, model_discriminant, model_c4]
  field_simp
  ring

/-- The exact coordinate set uses the group law on actual nonsingular points. -/
noncomputable def twoX {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) : Set F := by
  classical
  exact {x | ∃ y, ∃ h : W.Nonsingular x y,
    WeierstrassCurve.Affine.Point.some x y h +
      WeierstrassCurve.Affine.Point.some x y h = 0}

theorem twoX_iff {F : Type*} [Field F] [CharZero F] (l : ℤ) (x : F) :
    x ∈ twoX (model (l:F) 1) ↔ equation (l:F) x = 0 := by
  classical
  change (∃ y, ∃ h : (model (l:F) 1).Nonsingular x y,
    WeierstrassCurve.Affine.Point.some x y h +
      WeierstrassCurve.Affine.Point.some x y h = 0) ↔ _
  rw [← WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_iff
    (NeZero.mk (by norm_num : (2:F) ≠ 0)) (model_discriminant_ne l (by norm_num)) x,
    IsRoot.def, WeierstrassCurve.eval_toPoly_twoTorsionPolynomial]
  have h :
      4*x^3 + (model (l:F) 1).b₂*x^2 + 2*(model (l:F) 1).b₄*x +
        (model (l:F) 1).b₆ = 4*equation (l:F) x := by
    simp [model, equation, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    ring
  rw [h, mul_eq_zero, or_iff_right (by norm_num : (4:F) ≠ 0)]

theorem two_torsion_y_zero {F : Type*} [Field F] [CharZero F]
    (l : ℤ) (x y : F) (h : (model (l:F) 1).Nonsingular x y)
    (hd : letI := Classical.decEq F
      WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h = 0) : y = 0 := by
  classical
  by_contra hy
  have hn : y ≠ (model (l:F) 1).negY x y := by
    simp only [WeierstrassCurve.Affine.negY, model, zero_mul, sub_zero]
    intro H
    apply hy
    linear_combination (1/2 : F) * H
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hn] at hd
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ hd

/-- Over any characteristic-zero extension of the rationals, the root set of
the already constructed native cubic is the actual set of nonzero 2-torsion
abscissas. The ordinate of each such point is zero. -/
theorem rootSet_eq_twoX {F : Type*} [Field F] [CharZero F] [Algebra ℚ F] (l : ℤ) :
    ((cubic (l:ℚ)).toPoly).rootSet F = twoX (model (l:F) 1) := by
  ext x
  rw [twoX_iff, Polynomial.mem_rootSet]
  refine and_iff_right ?_ |>.trans ?_
  · exact (Cubic.monic_of_a_eq_one (by rfl)).ne_zero
  · have h : aeval x (cubic (l:ℚ)).toPoly = equation (l:F) x := by
      simp [cubic, Cubic.toPoly, equation, sub_eq_add_neg]
    rw [h]

theorem native_two_division (j : ℕ) (hj : 1 ≤ j) :
    let l := goldenLucas (3^j)
    let p := (cubic (l:ℚ)).toPoly
    let K := p.SplittingField
    Module.finrank ℚ K = 3 ∧ IsCyclic p.Gal ∧
      IntermediateField.adjoin ℚ (twoX (model (l:K) 1)) = ⊤ := by
  dsimp only
  exact ⟨(native_cyclic_field j hj).1, (native_cyclic_field j hj).2, by
    rw [← rootSet_eq_twoX]
    exact (isSplittingField_iff_intermediateField.mp
      (Polynomial.IsSplittingField.splittingField _)).2⟩

theorem shifted_values {R : Type*} [CommRing R] (l : R) :
    equation l (l-1) = 8 ∧ equation l (l+1) = -8 := by
  constructor <;> simp [equation] <;> ring

theorem twisted_equation (l d x y : ℚ) :
    (model l d).Equation (d*x) y ↔ y^2 = d^3*equation l x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [model, equation]
  constructor <;> intro h <;> linear_combination h

theorem twist_points (l : ℤ) :
    (model (l:ℚ) 2).Nonsingular (2*((l:ℚ)-1)) 8 ∧
      (model (l:ℚ) (-2)).Nonsingular (-2*((l:ℚ)+1)) 8 := by
  constructor
  · apply (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (model_discriminant_ne l (by norm_num : (2:ℚ) ≠ 0))).mp
    rw [twisted_equation, (shifted_values (l:ℚ)).1]
    norm_num
  · apply (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (model_discriminant_ne l (by norm_num : (-2:ℚ) ≠ 0))).mp
    rw [twisted_equation, (shifted_values (l:ℚ)).2]
    norm_num

theorem twist_slopes (l : ℤ) :
    (model (l:ℚ) 2).slope (2*((l:ℚ)-1)) (2*((l:ℚ)-1)) 8 8 = -3*((l:ℚ)+1)/2 ∧
      (model (l:ℚ) (-2)).slope (-2*((l:ℚ)+1)) (-2*((l:ℚ)+1)) 8 8 = 3*((l:ℚ)-1)/2 := by
  constructor <;>
    norm_num [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY, model] <;> ring

/-- Three further explicit sections, two on the same variable twist. -/
theorem variable_twist_points (l : ℤ) (hl : l ≠ 0) :
    (model (l:ℚ) (6*(l:ℚ))).Nonsingular (-12*(l:ℚ)^2) (72*(l:ℚ)^2) ∧
    (model (l:ℚ) (-3*(l:ℚ))).Nonsingular (-3*(l:ℚ)^2) (9*(l:ℚ)^2) ∧
    (model (l:ℚ) (6*(l:ℚ))).Nonsingular (4*(l:ℚ)^2) (8*(l:ℚ)^3) := by
  have hlq : (l:ℚ) ≠ 0 := by exact_mod_cast hl
  have hp : (6:ℚ)*(l:ℚ) ≠ 0 := mul_ne_zero (by norm_num) hlq
  have hm : (-3:ℚ)*(l:ℚ) ≠ 0 := mul_ne_zero (by norm_num) hlq
  refine ⟨?_, ?_, ?_⟩
  · apply (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (model_discriminant_ne l hp)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [model]
    ring
  · apply (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (model_discriminant_ne l hm)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [model]
    ring
  · apply (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (model_discriminant_ne l hp)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [model]
    ring

/-- The whole reduced elliptic curve stabilizes, not just its 2-torsion. -/
theorem earlier_prime_good_reduction {p i j : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hi : 1 ≤ i) (hij : i < j)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    ((model (goldenLucas (3^j)) (1:ℤ)).map (Int.castRingHom (ZMod p)) =
      model (0:ZMod p) 1) ∧ (model (0:ZMod p) 1).Δ ≠ 0 := by
  have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hB
  have hb' : ((goldenLucas (3 ^ i) : ZMod p)^2 + 3) = 0 := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using hb
  have hl := GoldenCubicNativeForwardSplitting.later_lucas_vanishes i j hi hij hb'
  refine ⟨?_, ?_⟩
  · simp [model, WeierstrassCurve.map, hl]
  · have hcast (q : ℕ) (hq₀ : 0 < q) (hq : q < p) : (q:ZMod p) ≠ 0 := by
      intro H
      exact (Nat.not_dvd_of_pos_of_lt hq₀ hq) ((ZMod.natCast_eq_zero_iff q p).mp H)
    have h₂ := hcast 2 (by decide) (by omega)
    have h₃ := hcast 3 (by decide) hp
    rw [model_discriminant]
    norm_num only [zero_pow, zero_add, one_pow, one_mul]
    rw [show (46656:ZMod p) = (2^3*3^3)^2 by norm_num]
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ h₂) (pow_ne_zero _ h₃))

private theorem native_next (j : ℕ) (hj : 1 ≤ j) :
    goldenLucas (3^(j+1)) = goldenLucas (3^j) * (goldenLucas (3^j)^2+3) :=
  (golden_cubic_lucas_block j hj).2.2.2.2.2

theorem native_later_lucas_depth {p i j : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hi : 1 ≤ i) (hij : i < j)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    padicValInt p (goldenLucas (3^j)) =
      padicValInt p (goldenLucas (3^i)^2+3) := by
  have hn (n : ℕ) (hn : 1 ≤ n) : goldenLucas (3^n) ≠ 0 := by
    have hm := (native_lucas_mod n hn).1
    omega
  have hcast3 : (3:ZMod p) ≠ 0 := by
    intro H
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) hp)
      ((ZMod.natCast_eq_zero_iff 3 p).mp H)
  have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hB
  have hb' : ((goldenLucas (3^i):ZMod p)^2+3) = 0 := by
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using hb
  have hfirst : ¬ (p:ℤ) ∣ goldenLucas (3^i) := by
    intro H
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr H
    exact hcast3 (by simpa [h] using hb')
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, j = i+1+a := ⟨j-(i+1), by omega⟩
  induction a with
  | zero =>
    rw [Nat.add_zero, native_next i hi, padicValInt.mul (hn _ hi) (by positivity),
      padicValInt.eq_zero_of_not_dvd hfirst, zero_add]
  | succ a ih =>
    change padicValInt p (goldenLucas (3^((i+1+a)+1))) = _
    have hl := GoldenCubicNativeForwardSplitting.later_lucas_vanishes i (i+1+a)
      hi (by omega) hb'
    have hnext : ¬ (p:ℤ) ∣ goldenLucas (3^(i+1+a))^2+3 := by
      intro H
      have ht := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr H
      exact hcast3 (by simpa [hl] using ht)
    rw [native_next _ (by omega), padicValInt.mul (hn _ (by omega)) (by positivity),
      padicValInt.eq_zero_of_not_dvd hnext, add_zero, ih (by omega)]

/-- The exact depth of contact with the CM j-invariant in every later curve
recovers twice the valuation of the earlier block. -/
theorem native_elliptic_cm_contact {p i j : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hi : 1 ≤ i) (hij : i < j)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    padicValRat p ((model (goldenLucas (3^j):ℚ) 1).j - 1728) =
      2 * (padicValInt p (goldenLucas (3^i)^2+3) : ℤ) := by
  rw [model_j, add_sub_cancel_left, padicValRat.pow,
    padicValRat.mul (by norm_num) ?_, padicValRat.of_int,
    native_later_lucas_depth hp hi hij hB]
  · have hp' : p.Prime := Fact.out
    have hv : ¬ p ∣ 24 := by
      intro H
      have h := hp'.dvd_mul.mp (show p ∣ 2^3*3 by simpa using H)
      exact h.elim
        (fun h₂ => (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p))
          (hp'.dvd_of_dvd_pow h₂))
        (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) hp)
    have hz : padicValRat p (24 : ℚ) = 0 := by
      change padicValRat p ((24:ℕ):ℚ) = 0
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hv]
      rfl
    rw [hz, zero_add]
    rfl
  · have hm := (native_lucas_mod j (by omega)).1
    exact_mod_cast (show goldenLucas (3^j) ≠ 0 by omega)

/-- A square divisor of an earlier block is equivalent to fourth-order
contact with the CM j-invariant on every specified later curve. -/
theorem native_wss_iff_cm_contact {p i j : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hi : 1 ≤ i) (hij : i < j)
    (hB : (p:ℤ) ∣ goldenLucas (3^i)^2+3) :
    (p:ℤ)^2 ∣ goldenLucas (3^i)^2+3 ↔
      4 ≤ padicValRat p ((model (goldenLucas (3^j):ℚ) 1).j - 1728) := by
  rw [native_elliptic_cm_contact hp hi hij hB,
    padicValInt_dvd_iff 2 _, or_iff_right (by positivity)]
  omega

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
