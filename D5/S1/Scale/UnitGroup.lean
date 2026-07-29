/- GID: D5/S1/Scale/UnitGroup
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden integer unit group is isomorphic to the free phi-power part times the sign torsion. -/

import D5.S1.Scale.Units
import Mathlib.Algebra.Ring.BooleanRing

namespace D5.S1.Scale

open D5.S0.Carrier

private theorem embedding_phiUnit_zpow (n : ℤ) :
    embedding (((phiUnit ^ n : GoldenIntˣ) : GoldenInt)) =
      Real.goldenRatio ^ n := by
  simpa [phiUnitZPowMul] using embedding_phiUnitZPowMul n (1 : GoldenInt)

private theorem logScale_neg (x : GoldenInt) : logScale (-x) = logScale x := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [logScale_ne_zero (neg_ne_zero.mpr hx), logScale_ne_zero hx,
      map_neg, abs_neg]

private theorem logScale_signedPhiPower (s : Bool) (n : ℤ) :
    logScale (signedPhiPower s n) = some n := by
  have hone : (1 : GoldenInt) ≠ 0 := by
    intro h
    have := congr_arg embedding h
    norm_num at this
  have hscale_one : logScale (1 : GoldenInt) = some 0 := by
    rw [logScale_ne_zero hone]
    norm_num [embedding_apply, Real.logb]
  have h := logScale_phiUnit_zpow_mul n hone
  cases s <;>
    simpa [signedPhiPower, phiUnitZPowMul, logScale_neg, hscale_one] using h

/-- The sign and exponent in a signed integral power of `phi` are unique. -/
theorem signedPhiPower_unique {s₁ s₂ : Bool} {n₁ n₂ : ℤ}
    (h : signedPhiPower s₁ n₁ = signedPhiPower s₂ n₂) :
    s₁ = s₂ ∧ n₁ = n₂ := by
  have hn : n₁ = n₂ := by
    have := congr_arg logScale h
    simpa [logScale_signedPhiPower] using this
  subst n₂
  refine ⟨?_, rfl⟩
  cases s₁ <;> cases s₂
  · rfl
  · have hemb := congr_arg embedding h
    change embedding (((phiUnit ^ n₁ : GoldenIntˣ) : GoldenInt)) =
      embedding (-((phiUnit ^ n₁ : GoldenIntˣ) : GoldenInt)) at hemb
    rw [map_neg, embedding_phiUnit_zpow] at hemb
    have hpos : 0 < Real.goldenRatio ^ n₁ :=
      zpow_pos Real.goldenRatio_pos n₁
    linarith
  · have hemb := congr_arg embedding h
    change embedding (-((phiUnit ^ n₁ : GoldenIntˣ) : GoldenInt)) =
      embedding (((phiUnit ^ n₁ : GoldenIntˣ) : GoldenInt)) at hemb
    rw [map_neg, embedding_phiUnit_zpow] at hemb
    have hpos : 0 < Real.goldenRatio ^ n₁ :=
      zpow_pos Real.goldenRatio_pos n₁
    linarith
  · rfl

/-- Signed powers multiply by adding exponents and taking xor of their signs. -/
theorem signedPhiPower_mul (s₁ s₂ : Bool) (n₁ n₂ : ℤ) :
    signedPhiPower s₁ n₁ * signedPhiPower s₂ n₂ =
      signedPhiPower (s₁ + s₂) (n₁ + n₂) := by
  cases s₁ <;> cases s₂ <;>
    simp [signedPhiPower, Bool.add_eq_xor, zpow_add]

private def boolAddEquivZModTwo : Bool ≃+ ZMod 2 where
  toFun b := b.toNat
  invFun z := decide (z.val = 1)
  left_inv b := by cases b <;> decide
  right_inv z := by fin_cases z <;> decide
  map_add' a b := by cases a <;> cases b <;> decide

private noncomputable def signedPhiPowerUnit (s : Bool) (n : ℤ) : GoldenIntˣ :=
  (signedPhiPower_isUnit s n).unit

@[simp] private theorem coe_signedPhiPowerUnit (s : Bool) (n : ℤ) :
    (signedPhiPowerUnit s n : GoldenInt) = signedPhiPower s n :=
  IsUnit.unit_spec _

private noncomputable def signedPhiPowerHom :
    Multiplicative ℤ × Multiplicative Bool →* GoldenIntˣ where
  toFun p := signedPhiPowerUnit p.2.toAdd p.1.toAdd
  map_one' := by
    apply Units.ext
    simp [signedPhiPower]
  map_mul' p q := by
    apply Units.ext
    simpa using
      (signedPhiPower_mul p.2.toAdd q.2.toAdd p.1.toAdd q.1.toAdd).symm

private theorem signedPhiPowerHom_bijective :
    Function.Bijective signedPhiPowerHom := by
  constructor
  · rintro ⟨n₁, s₁⟩ ⟨n₂, s₂⟩ h
    have hval := congr_arg (fun u : GoldenIntˣ => (u : GoldenInt)) h
    have hs := signedPhiPower_unique hval
    exact Prod.ext hs.2 hs.1
  · intro u
    have hu : IsUnit (u : GoldenInt) := u.isUnit
    rcases (golden_units_eq_signed_phi_pow (u : GoldenInt)).mp hu with ⟨s, n, h⟩
    refine ⟨(Multiplicative.ofAdd n, Multiplicative.ofAdd s), ?_⟩
    apply Units.ext
    change signedPhiPower s n = (u : GoldenInt)
    exact h.symm

private noncomputable def signedPhiPowerParamEquiv :
    Multiplicative ℤ × Multiplicative Bool ≃* GoldenIntˣ :=
  MulEquiv.ofBijective signedPhiPowerHom signedPhiPowerHom_bijective

/-- The unit group of the golden integers is infinite cyclic up to its sign torsion. -/
noncomputable def goldenUnitsMulEquiv :
    GoldenIntˣ ≃* Multiplicative ℤ × Multiplicative (ZMod 2) :=
  signedPhiPowerParamEquiv.symm.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) boolAddEquivZModTwo.toMultiplicative)

/-- The inverse equivalence reconstructs the unit represented by a sign and exponent. -/
@[simp] theorem goldenUnitsMulEquiv_symm_apply (s : Bool) (n : ℤ) :
    goldenUnitsMulEquiv.symm
      (Multiplicative.ofAdd n, Multiplicative.ofAdd (s.toNat : ZMod 2)) =
        (signedPhiPower_isUnit s n).unit := by
  cases s <;> rfl

end D5.S1.Scale
