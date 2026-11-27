import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContractionReciprocity

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear paritySign)
open LatticeActualGeneratorLocality (epsilon_skew)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open ThirdTwistedContraction (reciprocityPhase)

local notation "ζ" => zeta

/-- The leading-coefficient phase of the rational contraction at the native root
exchanges the charges in the native order-three multiplier. -/
theorem c_mul_reciprocityPhase (D : LatticeData) (g : Charge D ≃+ Charge D)
    (h3 : ∀ a, g (g (g a)) = a)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (a b : Charge D) :
    c D g a b * reciprocityPhase D g ζ a b = c D g b a := by
  let e₀ := bilinear D a b
  let e₁ := bilinear D (g a) b
  let e₂ := bilinear D (g (g a)) b
  have hpairOne : bilinear D (g b) a = bilinear D (g (g a)) b := by
    rw [bilinear_symmetric D (g b) a]
    simpa only [h3 a] using hg (g (g a)) b
  have hpairTwo : bilinear D (g (g b)) a = bilinear D (g a) b := by
    rw [bilinear_symmetric D (g (g b)) a]
    simpa only [h3 b] using (hg a (g (g b))).symm

  have hζ : IsPrimitiveRoot (ζ : ℂ) 3 := IsPrimitiveRoot.coe_units_iff.mpr zeta_primitive
  let sign : ℂˣ := Units.mk0 (-1) (by norm_num)
  let three : ℂˣ := Units.mk0 3 (by norm_num)
  let factor₁ : ℂˣ := Units.mk0 (1 - (ζ : ℂ)) (sub_ne_zero.mpr (hζ.ne_one (by decide)).symm)
  let factor₂ : ℂˣ := Units.mk0 (1 - (ζ : ℂ) ^ 2)
    (sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt (by decide : (2 : ℕ) ≠ 0) (by decide)).symm)
  have hfactorOne : factor₁ * (sign * ζ ^ (2 : ℕ)) = factor₂ := by
    apply Units.ext
    change (1 - (ζ : ℂ)) * ((-1 : ℂ) * (ζ : ℂ) ^ 2) = 1 - (ζ : ℂ) ^ 2
    calc
      _ = (ζ : ℂ) ^ 3 - (ζ : ℂ) ^ 2 := by ring
      _ = _ := by rw [hζ.pow_eq_one]
  have hfactorTwo : factor₂ * (sign * ζ) = factor₁ := by
    apply Units.ext
    change (1 - (ζ : ℂ) ^ 2) * ((-1 : ℂ) * (ζ : ℂ)) = 1 - (ζ : ℂ)
    calc
      _ = (ζ : ℂ) ^ 3 - (ζ : ℂ) := by ring
      _ = _ := by rw [hζ.pow_eq_one]

  have hB (x y : Charge D) : B D g x y = three ^ (-bilinear D x y) *
      factor₁ ^ bilinear D (g x) y * factor₂ ^ bilinear D (g (g x)) y := by
    unfold B
    rfl
  have hforward : B D g a b = three ^ (-e₀) * factor₁ ^ e₁ * factor₂ ^ e₂ := hB a b
  have hswap : B D g b a = three ^ (-e₀) * factor₂ ^ e₁ * factor₁ ^ e₂ := by
    rw [hB b a, bilinear_symmetric D b a, hpairOne, hpairTwo]
    change three ^ (-e₀) * factor₁ ^ e₂ * factor₂ ^ e₁ = _
    ac_rfl
  have hphase : reciprocityPhase D g ζ a b =
      sign ^ e₀ * (sign * ζ) ^ e₁ * (sign * ζ ^ (2 : ℕ)) ^ e₂ := by
    simp only [reciprocityPhase, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
      mul_one, Function.iterate_succ_apply', Function.iterate_zero_apply, pow_zero, pow_one,
      sign, e₀, e₁, e₂]
  have hphaseB : reciprocityPhase D g ζ a b * B D g b a = sign ^ e₀ * B D g a b := by
    rw [hphase, hswap, hforward]
    calc
      _ = sign ^ e₀ * (three ^ (-e₀) * (factor₂ ^ e₁ * (sign * ζ) ^ e₁) *
          (factor₁ ^ e₂ * (sign * ζ ^ (2 : ℕ)) ^ e₂)) := by ac_rfl
      _ = _ := by
        rw [← mul_zpow factor₂ (sign * ζ) e₁, hfactorTwo,
          ← mul_zpow factor₁ (sign * ζ ^ (2 : ℕ)) e₂, hfactorOne]

  have hepsilon : epsilonUnit D a b = sign ^ e₀ * epsilonUnit D b a := by
    apply Units.ext
    simpa only [Units.val_mul, coe_epsilonUnit, Units.val_zpow_eq_zpow_val, Units.val_mk0,
      sign, e₀, neg_one_zpow_eq_ite, paritySign] using epsilon_skew D a b
  have hsignSquare : sign ^ (2 : ℤ) = 1 := by
    apply Units.ext
    change ((sign ^ (2 : ℤ) : ℂˣ) : ℂ) = 1
    rw [Units.val_zpow_eq_zpow_val]
    change (-1 : ℂ) ^ (2 : ℤ) = 1
    norm_num
  have hsign : sign ^ e₀ * sign ^ e₀ = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul, hsignSquare, one_zpow]

  simp only [c, ← div_eq_mul_inv, div_mul_eq_mul_div]
  apply div_eq_div_iff_mul_eq_mul.mpr
  rw [mul_assoc, hphaseB, hepsilon]
  calc
    _ = (sign ^ e₀ * sign ^ e₀) * (epsilonUnit D b a * B D g a b) := by ac_rfl
    _ = _ := by rw [hsign, one_mul]

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle
