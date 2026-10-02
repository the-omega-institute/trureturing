/- GID: D5/S3/Factorization/Mordell/PointVariableChange
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/PointVariableChange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lit/tauceti2026canonicalheight]
   utility: none
   digest: An admissible change of Weierstrass variables induces an additive equivalence of elliptic point groups. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in
Library/ArithUnits/tauceti2026canonicalheight.md.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-!
# Point groups under a change of Weierstrass variables

Adapted from TauCeti/AlgebraicGeometry/EllipticCurve/Affine/{Formula,Point}/VariableChange.lean
(Apache-2.0), themselves adapted from ImperialCollegeLondon/FLT,
FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean at bc2fe8ff7396
(Apache-2.0; original authors Michael Stoll and Claude).

An admissible variable change acts on nonsingular points and preserves their group law.
-/

public section

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F]

/-- The affine point-group equivalence induced by an admissible change of variables. -/
@[expose] def equivVariableChange (W : WeierstrassCurve F) (C : VariableChange F)
    [W.IsElliptic] : (C • W).toAffine.Point ≃+ W.toAffine.Point := by
  have ha₁ (V : WeierstrassCurve F) (D : VariableChange F) :
      (D.u : F) * (D • V).a₁ = V.a₁ + 2 * D.s := by
    simp only [variableChange_a₁, Units.mul_inv_cancel_left]
  have ha₂ (V : WeierstrassCurve F) (D : VariableChange F) :
      (D.u : F) ^ 2 * (D • V).a₂ = V.a₂ - D.s * V.a₁ + 3 * D.r - D.s ^ 2 := by
    simp only [variableChange_a₂, ← Units.val_pow_eq_pow_val, inv_pow,
      Units.mul_inv_cancel_left]
  have ha₃ (V : WeierstrassCurve F) (D : VariableChange F) :
      (D.u : F) ^ 3 * (D • V).a₃ = V.a₃ + D.r * V.a₁ + 2 * D.t := by
    simp only [variableChange_a₃, ← Units.val_pow_eq_pow_val, inv_pow,
      Units.mul_inv_cancel_left]
  have ha₄ (V : WeierstrassCurve F) (D : VariableChange F) :
      (D.u : F) ^ 4 * (D • V).a₄ = V.a₄ - D.s * V.a₃ + 2 * D.r * V.a₂
        - (D.t + D.r * D.s) * V.a₁ + 3 * D.r ^ 2 - 2 * D.s * D.t := by
    simp only [variableChange_a₄, ← Units.val_pow_eq_pow_val, inv_pow,
      Units.mul_inv_cancel_left]
  have ha₆ (V : WeierstrassCurve F) (D : VariableChange F) :
      (D.u : F) ^ 6 * (D • V).a₆ = V.a₆ + D.r * V.a₄ + D.r ^ 2 * V.a₂ + D.r ^ 3
        - D.t * V.a₃ - D.t ^ 2 - D.r * D.t * V.a₁ := by
    simp only [variableChange_a₆, ← Units.val_pow_eq_pow_val, inv_pow,
      Units.mul_inv_cancel_left]
  have hnegY (V : WeierstrassCurve F) (D : VariableChange F) (x y : F) :
      V.toAffine.negY ((D.u : F) ^ 2 * x + D.r)
          ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)
        = (D.u : F) ^ 3 * (D • V).toAffine.negY x y
          + (D.u : F) ^ 2 * D.s * x + D.t := by
    simp only [WeierstrassCurve.Affine.negY]
    linear_combination (D.u : F) ^ 2 * x * ha₁ V D + ha₃ V D
  have haddX (V : WeierstrassCurve F) (D : VariableChange F) (x₁ x₂ ℓ : F) :
      V.toAffine.addX ((D.u : F) ^ 2 * x₁ + D.r) ((D.u : F) ^ 2 * x₂ + D.r)
          ((D.u : F) * ℓ + D.s)
        = (D.u : F) ^ 2 * (D • V).toAffine.addX x₁ x₂ ℓ + D.r := by
    simp only [WeierstrassCurve.Affine.addX]
    linear_combination (-(D.u : F) * ℓ) * ha₁ V D + ha₂ V D
  have hnegAddY (V : WeierstrassCurve F) (D : VariableChange F)
      (x₁ x₂ y₁ ℓ : F) :
      V.toAffine.negAddY ((D.u : F) ^ 2 * x₁ + D.r) ((D.u : F) ^ 2 * x₂ + D.r)
          ((D.u : F) ^ 3 * y₁ + (D.u : F) ^ 2 * D.s * x₁ + D.t)
          ((D.u : F) * ℓ + D.s)
        = (D.u : F) ^ 3 * (D • V).toAffine.negAddY x₁ x₂ y₁ ℓ
          + (D.u : F) ^ 2 * D.s * (D • V).toAffine.addX x₁ x₂ ℓ + D.t := by
    simp only [WeierstrassCurve.Affine.negAddY, haddX]
    ring
  have haddY (V : WeierstrassCurve F) (D : VariableChange F)
      (x₁ x₂ y₁ ℓ : F) :
      V.toAffine.addY ((D.u : F) ^ 2 * x₁ + D.r) ((D.u : F) ^ 2 * x₂ + D.r)
          ((D.u : F) ^ 3 * y₁ + (D.u : F) ^ 2 * D.s * x₁ + D.t)
          ((D.u : F) * ℓ + D.s)
        = (D.u : F) ^ 3 * (D • V).toAffine.addY x₁ x₂ y₁ ℓ
          + (D.u : F) ^ 2 * D.s * (D • V).toAffine.addX x₁ x₂ ℓ + D.t := by
    simp only [WeierstrassCurve.Affine.addY, hnegAddY, haddX, hnegY]
  have hequation (V : WeierstrassCurve F) (D : VariableChange F) (x y : F) :
      V.toAffine.Equation ((D.u : F) ^ 2 * x + D.r)
          ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)
        ↔ (D • V).toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff', WeierstrassCurve.Affine.equation_iff']
    refine Iff.trans ?_ (D.u.isUnit.pow 6).mul_right_eq_zero
    constructor
    · intro h
      linear_combination h + (D.u : F) ^ 5 * x * y * ha₁ V D
        - (D.u : F) ^ 4 * x ^ 2 * ha₂ V D
        + (D.u : F) ^ 3 * y * ha₃ V D
        - (D.u : F) ^ 2 * x * ha₄ V D - ha₆ V D
    · intro h
      linear_combination h - (D.u : F) ^ 5 * x * y * ha₁ V D
        + (D.u : F) ^ 4 * x ^ 2 * ha₂ V D
        - (D.u : F) ^ 3 * y * ha₃ V D
        + (D.u : F) ^ 2 * x * ha₄ V D + ha₆ V D
  have hpolyY (V : WeierstrassCurve F) (D : VariableChange F) (x y : F) :
      V.toAffine.polynomialY.evalEval ((D.u : F) ^ 2 * x + D.r)
          ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)
        = (D.u : F) ^ 3 * (D • V).toAffine.polynomialY.evalEval x y := by
    simp only [WeierstrassCurve.Affine.evalEval_polynomialY]
    linear_combination (-(D.u : F) ^ 2 * x) * ha₁ V D - ha₃ V D
  have hpolyX (V : WeierstrassCurve F) (D : VariableChange F) (x y : F) :
      V.toAffine.polynomialX.evalEval ((D.u : F) ^ 2 * x + D.r)
          ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)
        = (D.u : F) ^ 4 * (D • V).toAffine.polynomialX.evalEval x y
          - D.s * ((D.u : F) ^ 3 * (D • V).toAffine.polynomialY.evalEval x y) := by
    simp only [WeierstrassCurve.Affine.evalEval_polynomialX,
      WeierstrassCurve.Affine.evalEval_polynomialY]
    linear_combination (-(D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x) * ha₁ V D
      + (2 * (D.u : F) ^ 2 * x) * ha₂ V D + D.s * ha₃ V D + ha₄ V D
  have hnonsingular (V : WeierstrassCurve F) (D : VariableChange F) (x y : F) :
      V.toAffine.Nonsingular ((D.u : F) ^ 2 * x + D.r)
          ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)
        ↔ (D • V).toAffine.Nonsingular x y := by
    rw [WeierstrassCurve.Affine.Nonsingular,
      WeierstrassCurve.Affine.Nonsingular, hequation]
    refine and_congr_right fun _ ↦ ?_
    rw [hpolyX, hpolyY, ← not_and_or, ← not_and_or]
    refine not_congr ⟨fun ⟨h1, h2⟩ ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
    · have hB := (D.u.isUnit.pow 3).mul_right_eq_zero.mp h2
      rw [hB, mul_zero, mul_zero, sub_zero] at h1
      exact ⟨(D.u.isUnit.pow 4).mul_right_eq_zero.mp h1, hB⟩
    · exact ⟨by rw [h1, h2]; ring, by rw [h2]; ring⟩
  have hslopeTangent (V : WeierstrassCurve F) (D : VariableChange F)
      {x y : F} (hy : y ≠ (D • V).toAffine.negY x y) :
      V.toAffine.slope ((D.u : F) ^ 2 * x + D.r) ((D.u : F) ^ 2 * x + D.r)
          ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)
          ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)
        = (D.u : F) * (D • V).toAffine.slope x x y y + D.s := by
    have hu : (D.u : F) ≠ 0 := D.u.ne_zero
    have hY : (D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t
        ≠ V.toAffine.negY ((D.u : F) ^ 2 * x + D.r)
            ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t) := by
      rw [hnegY]
      exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    rw [V.toAffine.slope_of_Y_ne rfl hY, (D • V).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hY) (sub_ne_zero.mpr hy)]
    simp [WeierstrassCurve.Affine.negY, variableChange_a₁, variableChange_a₂,
      variableChange_a₃, variableChange_a₄]
    field
  have hslopeChord (V : WeierstrassCurve F) (D : VariableChange F)
      {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
      V.toAffine.slope ((D.u : F) ^ 2 * x₁ + D.r) ((D.u : F) ^ 2 * x₂ + D.r)
          ((D.u : F) ^ 3 * y₁ + (D.u : F) ^ 2 * D.s * x₁ + D.t)
          ((D.u : F) ^ 3 * y₂ + (D.u : F) ^ 2 * D.s * x₂ + D.t)
        = (D.u : F) * (D • V).toAffine.slope x₁ x₂ y₁ y₂ + D.s := by
    have hu : (D.u : F) ≠ 0 := D.u.ne_zero
    have hX : (D.u : F) ^ 2 * x₁ + D.r ≠ (D.u : F) ^ 2 * x₂ + D.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [V.toAffine.slope_of_X_ne hX, (D • V).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hX
    have h2 := sub_ne_zero.mpr hx
    field
  have hslope (V : WeierstrassCurve F) (D : VariableChange F)
      {x₁ x₂ y₁ y₂ : F} (h₁ : (D • V).toAffine.Equation x₁ y₁)
      (h₂ : (D • V).toAffine.Equation x₂ y₂)
      (hxy : ¬(x₁ = x₂ ∧ y₁ = (D • V).toAffine.negY x₂ y₂)) :
      V.toAffine.slope ((D.u : F) ^ 2 * x₁ + D.r) ((D.u : F) ^ 2 * x₂ + D.r)
          ((D.u : F) ^ 3 * y₁ + (D.u : F) ^ 2 * D.s * x₁ + D.t)
          ((D.u : F) ^ 3 * y₂ + (D.u : F) ^ 2 * D.s * x₂ + D.t)
        = (D.u : F) * (D • V).toAffine.slope x₁ x₂ y₁ y₂ + D.s := by
    rcases eq_or_ne x₁ x₂ with rfl | hx
    · have hy : y₁ ≠ (D • V).toAffine.negY x₁ y₂ :=
        fun h ↦ hxy ⟨rfl, h⟩
      obtain rfl := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ rfl hy
      exact hslopeTangent V D hy
    · exact hslopeChord V D hx
  have hnegYne {x₁ x₂ y₁ y₂ : F}
      (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
      ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
        (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t =
          W.toAffine.negY ((C.u : F) ^ 2 * x₂ + C.r)
            ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
    rintro ⟨hX, hY⟩
    have hx : x₁ = x₂ := (C.u.isUnit.pow 2).mul_left_cancel (by linear_combination hX)
    subst hx
    rw [hnegY W C] at hY
    exact hxy ⟨rfl, (C.u.isUnit.pow 3).mul_left_cancel (by linear_combination hY)⟩
  let mapFun (V : WeierstrassCurve F) (D : VariableChange F) :
      (D • V).toAffine.Point → V.toAffine.Point
    | .zero => .zero
    | .some x y h => .some ((D.u : F) ^ 2 * x + D.r)
        ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)
        ((hnonsingular V D x y).mpr h)
  have mapFun_zero (V : WeierstrassCurve F) (D : VariableChange F) :
      mapFun V D 0 = 0 := rfl
  have mapFun_some (V : WeierstrassCurve F) (D : VariableChange F)
      {x y : F} (h : (D • V).toAffine.Nonsingular x y) :
      mapFun V D (.some x y h) =
        .some ((D.u : F) ^ 2 * x + D.r)
          ((D.u : F) ^ 3 * y + (D.u : F) ^ 2 * D.s * x + D.t)
          ((hnonsingular V D x y).mpr h) := rfl
  have mapFun_injective : Function.Injective (mapFun W C) := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
    · rfl
    · simp [mapFun] at h
    · simp [mapFun] at h
    · simp only [mapFun] at h
      injection h with hX hY
      have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
      simp only [some.injEq]
      exact ⟨hx,
        mul_left_cancel₀ (pow_ne_zero 3 hu)
          (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx)⟩
  have mapFun_add (P Q : (C • W).toAffine.Point) :
      mapFun W C (P + Q) = mapFun W C P + mapFun W C Q := by
    cases P with
    | zero => cases Q <;> rfl
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero => rfl
      | some x₂ y₂ h₂ =>
        simp only [mapFun_some]
        have e₁ : (C • W).toAffine.Equation x₁ y₁ := equation_iff_nonsingular.mpr h₁
        have e₂ : (C • W).toAffine.Equation x₂ y₂ := equation_iff_nonsingular.mpr h₂
        by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
        · rw [add_of_Y_eq hxy.1 hxy.2]
          change 0 = _
          refine (add_of_Y_eq ?_ ?_).symm
          · rw [hxy.1]
          · rw [hnegY W C, hxy.2, hxy.1]
        · rw [add_some hxy]
          simp only [mapFun]
          rw [add_some (hnegYne hxy)]
          simp only [hslope W C e₁ e₂ hxy, haddX, haddY]
  have cast_some {V V' : WeierstrassCurve F} (h : V = V')
      {x y : F} (hns : V.toAffine.Nonsingular x y) :
      AddEquiv.cast (M := fun U : WeierstrassCurve F ↦ U.toAffine.Point) h (.some x y hns)
        = .some x y (h ▸ hns) := by
    subst h
    rfl
  have hright : ∀ P, mapFun W C
      (mapFun (C • W) C⁻¹
        (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
          (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · have hz : (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm) 0 = 0 := _root_.map_zero _
      exact congrArg (fun Q => mapFun W C (mapFun (C • W) C⁻¹ Q)) hz
    · rw [cast_some]
      simp only [mapFun]
      simp only [some.injEq]
      refine ⟨?_, ?_⟩ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  exact
    { toFun := mapFun W C
      invFun := fun P ↦ mapFun (C • W) C⁻¹
        (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
          (inv_smul_smul C W).symm P)
      left_inv := Function.RightInverse.leftInverse_of_injective hright mapFun_injective
      right_inv := hright
      map_add' := mapFun_add }

end WeierstrassCurve.Affine.Point

end
