/- GID: D5/S3/Arith/CharacterSums/SalieSum
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/SalieSum
   mirror-E: none(waiver:arithmetic-character-identity)
   anchors: []
   utility: none
   digest: Quadratic-character reciprocal phases are controlled by a quadratic root fiber. -/

module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
public import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Salié sums and quadratic stationary fibers

For an odd finite field, the quadratic character turns the reciprocal phase
`a * x + b / x` into a sum over the quadratic fiber `y^2 = 4 * a * b`.
Additive orthogonality and completion of the square identify this fiber with
the reciprocal phase sum. The character is the multiplicative-translation
eigencharacter in the Gauss-sum shift law.
-/

@[expose] public section

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

private theorem quadraticCharacterComplex_isQuadratic :
    (quadraticCharacterComplex (F := F)).IsQuadratic :=
  (quadraticChar_isQuadratic F).comp (Int.castRingHom ℂ)

private theorem quadraticCharacterComplex_ne_one (hF : ringChar F ≠ 2) :
    quadraticCharacterComplex (F := F) ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff
    (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℂ))).mpr
    (quadraticChar_ne_one hF)

private theorem quadraticCharacterComplex_inv (x : F) :
    (quadraticCharacterComplex x)⁻¹ = quadraticCharacterComplex x := by
  rw [← MulChar.inv_apply_eq_inv', quadraticCharacterComplex_isQuadratic.inv]

private theorem quadraticCharacterComplex_sq {x : F} (hx : x ≠ 0) :
    quadraticCharacterComplex x ^ 2 = 1 := by
  simpa using congrArg (Int.castRingHom ℂ) (quadraticChar_sq_one hx)

/-- Completing the square evaluates a quadratic phase with linear coefficient one. -/
theorem quadraticLinearPhase_sum_eq (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (t : Fˣ) :
    (∑ y : F, ψ ((t : F) * y ^ 2 + y)) =
      (quadraticCharacterComplex (t : F))⁻¹ * quadraticGaussSum ψ *
        ψ (-(4 * (t : F))⁻¹) := by
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hfour : (4 : F) ≠ 0 := by
    simpa only [show (4 : F) = 2 * 2 by ring] using mul_ne_zero htwo htwo
  have hcomplete (y : F) :
      (t : F) * y ^ 2 + y =
        (t : F) * (y + (2 * (t : F))⁻¹) ^ 2 + -(4 * (t : F))⁻¹ := by
    field_simp [htwo, hfour, t.ne_zero]
    <;> ring
  calc
    _ = ∑ y : F, ψ ((t : F) * (y + (2 * (t : F))⁻¹) ^ 2) *
        ψ (-(4 * (t : F))⁻¹) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hcomplete, AddChar.map_add_eq_mul]
    _ = (∑ y : F, ψ ((t : F) * y ^ 2)) * ψ (-(4 * (t : F))⁻¹) := by
      rw [Finset.sum_mul]
      exact Fintype.sum_equiv (Equiv.addRight (2 * (t : F))⁻¹) _ _ (fun _ ↦ rfl)
    _ = _ := by rw [quadraticPhase_sum_eq hF ψ hψ t]

/-- Additive orthogonality expresses the stationary root fiber as a quadratic Fourier sum. -/
theorem quadraticRootPhase_fourier (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (a b : F) :
    (Fintype.card F : ℂ) * quadraticRootPhase ψ a b =
      ∑ t : F, ψ (-(4 * a * b) * t) * (∑ y : F, ψ (t * y ^ 2 + y)) := by
  classical
  symm
  calc
    _ = ∑ y : F, ψ y * ∑ t : F, ψ (t * (y ^ 2 - 4 * a * b)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro t _
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ y : F, if y ^ 2 = 4 * a * b then ψ y * (Fintype.card F : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [AddChar.sum_mulShift _ (AddChar.IsPrimitive.of_ne_one hψ)]
      simp only [sub_eq_zero, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero]
    _ = _ := by
      simp only [quadraticRootPhase, Set.toFinset_ofPred, Finset.sum_filter]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> ring

theorem salieSum_zero_right (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (a : F) :
    salieSum ψ a 0 =
      if a = 0 then 0 else
        quadraticCharacterComplex a * quadraticGaussSum ψ := by
  classical
  by_cases ha : a = 0
  · rw [if_pos ha]
    simp only [salieSum, ha, zero_mul, zero_add, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one (quadraticCharacterComplex_ne_one hF)
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
    rw [hu, quadraticCharacterComplex_inv]
    rfl

end
end D5.S3.Arith.CharacterSums.SalieSum
