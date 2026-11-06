/- GID: D5/S3/Arith/CharacterSums/SalieSum
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/SalieSum
   mirror-E: none(waiver:arithmetic-character-identity)
   anchors: []
   utility: none
   digest: Quadratic-character reciprocal phases are controlled by a quadratic root fiber. -/

import D5.S3.Arith.CharacterSums.GaussSumSubgroupOrbit
import D5.S3.Arith.FiniteFieldQuadraticCharacterSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Salié sums and quadratic stationary fibers

For an odd finite field, the quadratic character turns the reciprocal phase
`a * x + b / x` into a sum over the quadratic fiber `y^2 = 4 * a * b`.
The boundary formula with `b = 0` is included first; the exact reciprocal
phase evaluation and its square-root consequence use the same character and
Gauss-sum bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.SalieSum

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/- The integer-valued quadratic character transported to the complex plane. -/
noncomputable def quadraticCharacterComplex : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

noncomputable def salieSum (ψ : AddChar F ℂ) (a b : F) : ℂ :=
  ∑ x : F, quadraticCharacterComplex x * ψ (a * x + b * x⁻¹)

noncomputable def quadraticGaussSum (ψ : AddChar F ℂ) : ℂ :=
  gaussSum quadraticCharacterComplex ψ

noncomputable def quadraticRootPhase (ψ : AddChar F ℂ) (a b : F) : ℂ :=
  ∑ y ∈ ({y : F | y ^ 2 = 4 * a * b}.toFinset), ψ y

@[simp] theorem quadraticCharacterComplex_apply (x : F) :
    quadraticCharacterComplex x = (quadraticChar F x : ℂ) := by
  rfl

theorem quadraticRootFiber_card (hF : ringChar F ≠ 2) (a b : F) :
    (({y : F | y ^ 2 = 4 * a * b}.toFinset).card : ℤ) =
      quadraticChar F (4 * a * b) + 1 := by
  simpa using (quadraticChar_card_sqrts hF (4 * a * b))

theorem quadraticRootPhase_eq_zero_of_not_isSquare
    (ψ : AddChar F ℂ) (a b : F) (h : ¬IsSquare (4 * a * b)) :
    quadraticRootPhase ψ a b = 0 := by
  classical
  have hempty : ({y : F | y ^ 2 = 4 * a * b}.toFinset) = ∅ := by
    apply Set.toFinset_eq_empty.mpr
    ext y
    constructor
    · intro hy
      exact False.elim (h ((isSquare_iff_exists_sq _).mpr ⟨y, hy.symm⟩))
    · intro hy
      exact False.elim (by simpa using hy)
  simp [quadraticRootPhase, hempty]

theorem quadraticPhase_sum_eq (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (t : Fˣ) :
    (∑ x : F, ψ ((t : F) * x ^ 2)) =
      (quadraticCharacterComplex (t : F))⁻¹ * quadraticGaussSum ψ := by
  have hψsum : (∑ z : F, ψ ((t : F) * z)) = 0 := by
    calc
      (∑ z : F, ψ ((t : F) * z)) = ∑ z : F, ψ z := by
        exact Fintype.sum_bijective _ t.mulLeft_bijective _ _ (fun z ↦ rfl)
      _ = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  calc
    (∑ x : F, ψ ((t : F) * x ^ 2)) =
        ∑ z : F, (Fintype.card {x : F // x ^ 2 = z} : ℂ) * ψ ((t : F) * z) := by
      simpa using (Fintype.sum_fiberwise' (fun x : F ↦ x ^ 2)
        (fun z : F ↦ ψ ((t : F) * z))).symm
    _ = ∑ z : F, (quadraticCharacterComplex z + 1) * ψ ((t : F) * z) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hcardN : Fintype.card {x : F // x ^ 2 = z} =
          ({x : F | x ^ 2 = z}.toFinset).card := by
        simpa only [Fintype.card_subtype, Set.toFinset_ofPred]
      have hcardZ : (Fintype.card {x : F // x ^ 2 = z} : ℤ) =
          quadraticChar F z + 1 := by
        rw [hcardN]
        exact quadraticChar_card_sqrts hF z
      have hcardC : (Fintype.card {x : F // x ^ 2 = z} : ℂ) =
          quadraticCharacterComplex z + 1 := by
        simpa [quadraticCharacterComplex_apply] using
          congrArg (Int.castRingHom ℂ) hcardZ
      rw [hcardC]
    _ = (∑ z : F, quadraticCharacterComplex z * ψ ((t : F) * z)) +
        ∑ z : F, ψ ((t : F) * z) := by
      simp_rw [add_mul, one_mul]
      rw [Finset.sum_add_distrib]
    _ = ∑ z : F, quadraticCharacterComplex z * ψ ((t : F) * z) := by
      rw [hψsum, add_zero]
    _ = gaussSum quadraticCharacterComplex (ψ.mulShift t) := by
      simp only [gaussSum, AddChar.mulShift_apply]
    _ = (quadraticCharacterComplex (t : F))⁻¹ * quadraticGaussSum ψ := by
      rw [gaussSum_mulShift_eq]
      rw [MulChar.inv_apply_eq_inv']
      rfl

theorem salieSum_zero_right (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (a : F) :
    salieSum ψ a 0 =
      if a = 0 then 0 else
        (quadraticCharacterComplex a)⁻¹ * quadraticGaussSum ψ := by
  classical
  by_cases ha : a = 0
  · have hχ : quadraticCharacterComplex ≠ 1 :=
      (MulChar.ringHomComp_ne_one_iff
        (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℂ))).mpr
        (quadraticChar_ne_one hF)
    rw [if_pos ha]
    simp only [salieSum, ha, zero_mul, zero_add, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  · let u : Fˣ := Units.mk0 a ha
    rw [if_neg ha]
    have hsum : salieSum ψ a 0 = gaussSum quadraticCharacterComplex (ψ.mulShift u) := by
      unfold salieSum gaussSum
      apply Finset.sum_congr rfl
      intro x hx
      rw [AddChar.mulShift_apply]
      simp [u, Units.val_mk0]
    rw [hsum, gaussSum_mulShift_eq]
    have hu : quadraticCharacterComplex⁻¹ (u : F) =
        (quadraticCharacterComplex a)⁻¹ := by
      rw [MulChar.inv_apply_eq_inv']
      congr 1
    rw [hu]
    rfl

end
end D5.S3.Arith.CharacterSums.SalieSum
