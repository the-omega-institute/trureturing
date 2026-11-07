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
# Salié sums and quadratic root fibers

For an odd finite field, the quadratic character turns the reciprocal phase
`a * x + b / x` into a sum over the quadratic fiber `y^2 = 4 * a * b`.
Additive orthogonality and completion of the square identify this fiber with
the reciprocal phase sum. The character is the multiplicative-translation
eigencharacter in the Gauss-sum shift law.

When `a * b ≠ 0`, the substitution `y = 2 * a * x` identifies this
quadratic root fiber with `a * x ^ 2 = b` on the units, the stationary
equation for the reciprocal phase. When `a = 0` and `b ≠ 0`, the
quadratic root fiber is `{0}`, but the phase has no stationary point on
the units. The exact evaluation includes this singular boundary.
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
      simp at hy
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
        simp only [Fintype.card_subtype, Set.toFinset_ofPred]
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
private theorem quadraticLinearPhase_sum_eq (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
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
    ring
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

/-- Additive orthogonality expresses the quadratic root fiber as a quadratic Fourier sum. -/
private theorem quadraticRootPhase_fourier (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (a b : F) :
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
  · rw [ite_eq_left ha]
    simp only [salieSum, ha, zero_mul, zero_add, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one (quadraticCharacterComplex_ne_one hF)
  · let u : Fˣ := Units.mk0 a ha
    rw [ite_eq_right ha]
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

private theorem salieSum_fourier (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (a b : F) (hb : b ≠ 0) :
    (Fintype.card F : ℂ) * quadraticRootPhase ψ a b =
      quadraticCharacterComplex (-b) * quadraticGaussSum ψ * salieSum ψ a b := by
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hfour : (4 : F) ≠ 0 := by
    simpa only [show (4 : F) = 2 * 2 by ring] using mul_ne_zero htwo htwo
  have hχfour : quadraticCharacterComplex (4 : F) = 1 := by
    rw [quadraticCharacterComplex_apply, show (4 : F) = 2 ^ 2 by ring,
      quadraticChar_sq_one' htwo, Int.cast_one]
  have hχshift (t : F) :
      quadraticCharacterComplex (-(4 * b) * t) =
        quadraticCharacterComplex (-b) * quadraticCharacterComplex t := by
    rw [show -(4 * b) * t = 4 * ((-b) * t) by ring, map_mul, hχfour, one_mul,
      map_mul]
  have hcoef (t : F) :
      quadraticCharacterComplex (-b) * quadraticCharacterComplex (-(4 * b) * t) =
        quadraticCharacterComplex t := by
    rw [hχshift, ← mul_assoc, ← pow_two,
      quadraticCharacterComplex_sq (neg_ne_zero.mpr hb), one_mul]
  have hterm (t : F) :
      ψ (-(4 * a * b) * t) * (∑ y : F, ψ (t * y ^ 2 + y)) =
        quadraticCharacterComplex (-b) * quadraticGaussSum ψ *
          (quadraticCharacterComplex (-(4 * b) * t) *
            ψ (a * (-(4 * b) * t) + b * (-(4 * b) * t)⁻¹)) := by
    by_cases ht : t = 0
    · subst t
      simp [AddChar.sum_eq_zero_of_ne_one hψ, MulChar.map_zero]
    · have hphase : -(4 * a * b) * t + -(4 * t)⁻¹ =
          a * (-(4 * b) * t) + b * (-(4 * b) * t)⁻¹ := by
        field_simp [hfour, hb, ht]
      have hQ := quadraticLinearPhase_sum_eq hF ψ hψ (Units.mk0 t ht)
      simp only [Units.val_mk0] at hQ
      rw [hQ, quadraticCharacterComplex_inv]
      calc
        _ = quadraticCharacterComplex t * quadraticGaussSum ψ *
            ψ (-(4 * a * b) * t + -(4 * t)⁻¹) := by
          rw [AddChar.map_add_eq_mul]
          ring
        _ = _ := by
          rw [hphase, ← hcoef t]
          ring
  rw [quadraticRootPhase_fourier ψ hψ, salieSum, Finset.mul_sum]
  simp_rw [hterm]
  exact Fintype.sum_bijective (fun t : F ↦ -(4 * b) * t)
    (Units.mk0 (-(4 * b)) (neg_ne_zero.mpr (mul_ne_zero hfour hb))).mulLeft_bijective
    _ _ (fun _ ↦ rfl)

private theorem quadraticGaussSum_sq (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) :
    quadraticGaussSum ψ ^ 2 = quadraticCharacterComplex (-1 : F) * Fintype.card F :=
  gaussSum_sq (quadraticCharacterComplex_ne_one hF)
    quadraticCharacterComplex_isQuadratic (AddChar.IsPrimitive.of_ne_one hψ)

/-- Exact Salié evaluation, including `a = 0`, over every odd finite field. -/
theorem salieSum_eq (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (a b : F) (hb : b ≠ 0) :
    salieSum ψ a b =
      quadraticCharacterComplex b * quadraticGaussSum ψ * quadraticRootPhase ψ a b := by
  have hG : quadraticGaussSum ψ ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (quadraticCharacterComplex_ne_one hF) (AddChar.IsPrimitive.of_ne_one hψ)
  have hχb : quadraticCharacterComplex (-b) ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hb))
  apply mul_left_cancel₀ (mul_ne_zero hχb hG)
  calc
    _ = (Fintype.card F : ℂ) * quadraticRootPhase ψ a b :=
      (salieSum_fourier hF ψ hψ a b hb).symm
    _ = _ := by
      rw [show -b = (-1 : F) * b by ring, map_mul]
      symm
      calc
        _ = quadraticCharacterComplex b ^ 2 *
            (quadraticCharacterComplex (-1 : F) * quadraticGaussSum ψ ^ 2) *
              quadraticRootPhase ψ a b := by ring
        _ = quadraticCharacterComplex b ^ 2 * quadraticCharacterComplex (-1 : F) ^ 2 *
            (Fintype.card F : ℂ) * quadraticRootPhase ψ a b := by
          rw [quadraticGaussSum_sq hF ψ hψ]
          ring
        _ = _ := by
          rw [quadraticCharacterComplex_sq (x := (-1 : F)) (neg_ne_zero.mpr one_ne_zero),
            quadraticCharacterComplex_sq hb]
          ring

/-- A nonsquare product has an empty quadratic root fiber, so the sum vanishes. -/
theorem salieSum_eq_zero_of_not_isSquare (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (a b : F) (hb : b ≠ 0) (hab : ¬IsSquare (a * b)) :
    salieSum ψ a b = 0 := by
  have hroot : ¬IsSquare (4 * a * b) := by
    intro h
    obtain ⟨y, hy⟩ := (isSquare_iff_exists_sq _).mp h
    apply hab
    refine (isSquare_iff_exists_sq _).mpr ⟨y / 2, ?_⟩
    field_simp [Ring.two_ne_zero hF]
    calc
      a * b * 2 ^ 2 = 4 * a * b := by ring
      _ = y ^ 2 := hy
  rw [salieSum_eq hF ψ hψ a b hb,
    quadraticRootPhase_eq_zero_of_not_isSquare ψ a b hroot, mul_zero]

private theorem quadraticCharacterComplex_norm {x : F} (hx : x ≠ 0) :
    ‖quadraticCharacterComplex x‖ = 1 := by
  have h := congrArg norm (quadraticCharacterComplex_sq hx)
  simp only [norm_pow, norm_one] at h
  have hn := norm_nonneg (quadraticCharacterComplex x)
  nlinarith

private theorem quadraticGaussSum_norm (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) :
    ‖quadraticGaussSum ψ‖ = Real.sqrt (Fintype.card F) := by
  have hg : ‖quadraticGaussSum ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    have h := congrArg norm (quadraticGaussSum_sq hF ψ hψ)
    simpa only [norm_pow, norm_mul,
      quadraticCharacterComplex_norm (F := F) (neg_ne_zero.mpr one_ne_zero), one_mul,
      Complex.norm_natCast] using h
  exact ((Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) (norm_nonneg _)).mpr hg.symm).symm

private theorem quadraticRootPhase_norm_le (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (a b : F) : ‖quadraticRootPhase ψ a b‖ ≤ 2 := by
  have hχ : quadraticChar F (4 * a * b) ≤ 1 := by
    rcases (quadraticChar_isQuadratic F) (4 * a * b) with h | h | h <;> omega
  have hc : ({y : F | y ^ 2 = 4 * a * b}.toFinset).card ≤ 2 := by
    have h := quadraticRootFiber_card hF a b
    omega
  calc
    _ ≤ ∑ y ∈ ({y : F | y ^ 2 = 4 * a * b}.toFinset), ‖ψ y‖ := norm_sum_le _ _
    _ = (({y : F | y ^ 2 = 4 * a * b}.toFinset).card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast hc

/-- Uniform square-root cancellation, also including the boundary `b = 0`. -/
theorem salieSum_norm_le (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (a b : F) :
    ‖salieSum ψ a b‖ ≤ 2 * Real.sqrt (Fintype.card F) := by
  by_cases hb : b = 0
  · subst b
    rw [salieSum_zero_right hF ψ a]
    split_ifs with ha
    · simp only [norm_zero]
      positivity
    · rw [norm_mul, quadraticCharacterComplex_norm ha, one_mul,
        quadraticGaussSum_norm hF ψ hψ]
      have h := Real.sqrt_nonneg (Fintype.card F : ℝ)
      linarith
  · by_cases hab : IsSquare (a * b)
    · rw [salieSum_eq hF ψ hψ a b hb, norm_mul, norm_mul,
        quadraticCharacterComplex_norm hb, one_mul, quadraticGaussSum_norm hF ψ hψ]
      calc
        _ ≤ Real.sqrt (Fintype.card F) * 2 :=
          mul_le_mul_of_nonneg_left (quadraticRootPhase_norm_le hF ψ a b)
            (Real.sqrt_nonneg _)
        _ = _ := by ring
    · rw [salieSum_eq_zero_of_not_isSquare hF ψ hψ a b hb hab, norm_zero]
      positivity

end
end D5.S3.Arith.CharacterSums.SalieSum
