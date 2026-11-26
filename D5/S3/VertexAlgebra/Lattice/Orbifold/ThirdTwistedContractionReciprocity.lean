/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational reciprocity and Bakalov–Kac phase cancellation for the order-three lattice contraction. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeAction
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Ring

/-!
The rational form of the order-three contraction of Bakalov–Kac,
*Twisted Modules over Lattice Vertex Algebras*, arXiv:math/0402315v3,
Lemma 4.2, in the cover coordinate `t = (w / z)^(1/3)`.
Reversing the cover ratio and the ordered charges introduces the orbit-norm
monomial and a scalar phase. The charge multiplier of (4.42) cancels the phase.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open ThirdTwistedChargeCocycle (pairing_shift_one pairing_shift_two)
open scoped BigOperators

noncomputable section

variable (D : LatticeData) (g : Charge D ≃+ Charge D)

/-- The rational binomial product with root parameter `u` and cover ratio `t`.
The integer powers are taken in `RatFunc ℂ`. -/
def rationalContraction (u : ℂˣ) (a b : Charge D) (t : RatFunc ℂ) : RatFunc ℂ :=
  ∏ j ∈ Finset.range 3,
    (1 - RatFunc.C (↑(u ^ j) : ℂ) * t) ^ bilinear D ((g^[j]) a) b

/-- The product of the unit leading coefficients of the three binomials,
raised to their respective integral orbit pairings. -/
def reciprocityPhase (u : ℂˣ) (a b : Charge D) : ℂˣ :=
  ∏ j ∈ Finset.range 3,
    (Units.mk0 (-1 : ℂ) (neg_ne_zero.mpr one_ne_zero) * u ^ j) ^
      bilinear D ((g^[j]) a) b

private theorem coe_reciprocityPhase (u : ℂˣ) (a b : Charge D) :
    (reciprocityPhase D g u a b : ℂ) =
      ∏ j ∈ Finset.range 3, (-(↑(u ^ j) : ℂ)) ^ bilinear D ((g^[j]) a) b := by
  simp only [reciprocityPhase, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    Units.val_mul, Units.val_mk0, neg_mul, one_mul]

private theorem sum_orbitPairing (a b : Charge D) :
    (∑ j ∈ Finset.range 3, bilinear D ((g^[j]) a) b) =
      bilinear D (ThirdTwistedChargeAction.N D g a) b := by
  rw [bilinear_symmetric D (ThirdTwistedChargeAction.N D g a) b]
  simp only [ThirdTwistedChargeAction.N_apply, bilinear_add_right, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, Function.iterate_succ_apply', Function.iterate_zero_apply,
    bilinear_symmetric D b a, bilinear_symmetric D b (g a), bilinear_symmetric D b (g (g a))]

variable (h3 : ∀ a, g (g (g a)) = a)
variable (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)

include h3 hg in
/-- Inverting the root exchanges indices one and two. By isometry and symmetry,
the exponent of index `j` for `(b, a)` is the exponent of `-j mod 3` for `(a, b)`. -/
private theorem rationalContraction_inv_root (u : ℂˣ) (hu : u ^ (3 : ℕ) = 1)
    (a b : Charge D) (t : RatFunc ℂ) :
    rationalContraction D g u⁻¹ a b t = rationalContraction D g u b a t := by
  have hpairOne : bilinear D (g b) a = bilinear D (g (g a)) b :=
    (bilinear_symmetric D (g b) a).trans (pairing_shift_one D g hg h3 a b)
  have hpairTwo : bilinear D (g (g b)) a = bilinear D (g a) b :=
    (bilinear_symmetric D (g (g b)) a).trans (pairing_shift_two D g hg h3 a b)
  have hinv : u⁻¹ = u ^ (2 : ℕ) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hu]
  have hinvSq : (u⁻¹) ^ (2 : ℕ) = u := by
    calc
      (u⁻¹) ^ (2 : ℕ) = (u ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [← hinv]
      _ = u ^ (3 + 1 : ℕ) := by rw [← pow_mul]
      _ = u := by rw [pow_succ, hu, one_mul]
  simp only [rationalContraction, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    Function.iterate_succ_apply', Function.iterate_zero_apply, pow_zero, pow_one,
    bilinear_symmetric D b a, hpairOne, hpairTwo]
  rw [hinvSq, hinv]
  ac_rfl

private theorem binomial_reciprocity (v : ℂˣ) (t : RatFunc ℂ) (ht : t ≠ 0) :
    1 - RatFunc.C (v : ℂ) * t =
      t * RatFunc.C (-(v : ℂ)) * (1 - RatFunc.C (↑(v⁻¹) : ℂ) * t⁻¹) := by
  have hv : RatFunc.C (v : ℂ) * RatFunc.C (↑(v⁻¹) : ℂ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hcancel : t * RatFunc.C (-(v : ℂ)) * (RatFunc.C (↑(v⁻¹) : ℂ) * t⁻¹) = -1 := by
    calc
      _ = -(RatFunc.C (v : ℂ) * RatFunc.C (↑(v⁻¹) : ℂ)) * (t * t⁻¹) := by
        rw [map_neg]
        ring
      _ = _ := by rw [hv, mul_inv_cancel₀ ht, mul_one]
  rw [mul_sub, mul_one, hcancel, map_neg]
  ring

include h3 hg in
/-- Exact reciprocity in `RatFunc ℂ`, with the same root convention on both
orders. The exponent of `t` is the pairing with the integral orbit norm. -/
theorem rationalContraction_reciprocity (u : ℂˣ) (hu : u ^ (3 : ℕ) = 1)
    (a b : Charge D) (t : RatFunc ℂ) (ht : t ≠ 0) :
    rationalContraction D g u a b t =
      t ^ bilinear D (ThirdTwistedChargeAction.N D g a) b *
        RatFunc.C (reciprocityPhase D g u a b : ℂ) * rationalContraction D g u b a t⁻¹ := by
  let e (j : ℕ) : ℤ := bilinear D ((g^[j]) a) b
  have hmonomial : (∏ j ∈ Finset.range 3, t ^ e j) = t ^ (∑ j ∈ Finset.range 3, e j) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, zpow_add₀ ht]
  calc
    rationalContraction D g u a b t =
        ∏ j ∈ Finset.range 3, (t ^ e j * RatFunc.C (-(↑(u ^ j) : ℂ)) ^ e j) *
          (1 - RatFunc.C (↑(u⁻¹ ^ j) : ℂ) * t⁻¹) ^ e j := by
      unfold rationalContraction
      apply Finset.prod_congr rfl
      intro j _
      rw [binomial_reciprocity (u ^ j) t ht, mul_zpow, mul_zpow, ← inv_pow u j]
    _ = t ^ (∑ j ∈ Finset.range 3, e j) * RatFunc.C (reciprocityPhase D g u a b : ℂ) *
        rationalContraction D g u⁻¹ a b t⁻¹ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hmonomial]
      simp only [coe_reciprocityPhase, map_prod, map_zpow₀, rationalContraction, e]
    _ = _ := by
      dsimp only [e]
      rw [sum_orbitPairing D g, rationalContraction_inv_root D g h3 hg u hu]

open scoped LaurentSeries RatFunc in
/-- At the indeterminate `X`, the rational product expands to the product of
the existing power-series binomial units, including their negative powers. -/
theorem rationalContraction_X_expansion (u : ℂˣ) (a b : Charge D) :
    (rationalContraction D g u a b RatFunc.X : LaurentSeries ℂ) =
      ((↑(∏ j ∈ Finset.range 3,
        binomialUnit (↑(u ^ j) : ℂ) ^ bilinear D ((g^[j]) a) b) : PowerSeries ℂ) :
          LaurentSeries ℂ) := by
  let toLaurent : (PowerSeries ℂ)ˣ →* LaurentSeries ℂ :=
    (HahnSeries.ofPowerSeries ℤ ℂ).toMonoidHom.comp (Units.coeHom (PowerSeries ℂ))
  have hC (c : ℂ) :
      algebraMap (RatFunc ℂ) (LaurentSeries ℂ) (RatFunc.C c) = HahnSeries.C c := by
    simpa only [Polynomial.coe_C, PowerSeries.coe_C, RatFunc.coePolynomial_eq_algebraMap,
      RatFunc.algebraMap_C] using (RatFunc.coe_coe (Polynomial.C c)).symm
  have hX : algebraMap (RatFunc ℂ) (LaurentSeries ℂ) RatFunc.X = HahnSeries.single 1 1 :=
    RatFunc.coe_X
  have hbinomial (c : ℂ) :
      algebraMap (RatFunc ℂ) (LaurentSeries ℂ) (1 - RatFunc.C c * RatFunc.X) =
        toLaurent (binomialUnit c) := by
    change _ = HahnSeries.ofPowerSeries ℤ ℂ (↑(binomialUnit c) : PowerSeries ℂ)
    simp only [coe_binomialUnit, map_sub, map_one, map_mul, hC, hX,
      HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X]
  change algebraMap (RatFunc ℂ) (LaurentSeries ℂ) (rationalContraction D g u a b RatFunc.X) =
    toLaurent (∏ j ∈ Finset.range 3, binomialUnit (↑(u ^ j) : ℂ) ^ bilinear D ((g^[j]) a) b)
  rw [rationalContraction, map_prod (algebraMap (RatFunc ℂ) (LaurentSeries ℂ)), map_prod toLaurent]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_zpow₀, map_zpow, hbinomial]

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear paritySign)
open LatticeActualGeneratorLocality (epsilon_skew)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open ThirdTwistedContraction (reciprocityPhase)

local notation "ζ" => zeta

/-- The leading-coefficient phase at the Bakalov–Kac root exchanges the charges
in the order-three multiplier. -/
theorem c_mul_reciprocityPhase (D : LatticeData) (g : Charge D ≃+ Charge D)
    (h3 : ∀ a, g (g (g a)) = a)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (a b : Charge D) :
    c D g a b * reciprocityPhase D g ζ a b = c D g b a := by
  let e₀ := bilinear D a b
  let e₁ := bilinear D (g a) b
  let e₂ := bilinear D (g (g a)) b
  have hpairOne : bilinear D (g b) a = bilinear D (g (g a)) b :=
    (bilinear_symmetric D (g b) a).trans (pairing_shift_one D g hg h3 a b)
  have hpairTwo : bilinear D (g (g b)) a = bilinear D (g a) b :=
    (bilinear_symmetric D (g (g b)) a).trans (pairing_shift_two D g hg h3 a b)

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

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open ThirdTwistedChargeCocycle (c zeta zeta_primitive c_mul_reciprocityPhase)

/-- Reversing the charges and the cover ratio in the cocycle-weighted rational
contraction leaves only the monomial with the integral orbit-norm exponent. -/
theorem c_mul_rationalContraction_reciprocity (D : LatticeData) (g : Charge D ≃+ Charge D)
    (h3 : ∀ a, g (g (g a)) = a)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (a b : Charge D) (t : RatFunc ℂ) (ht : t ≠ 0) :
    RatFunc.C (c D g a b : ℂ) * rationalContraction D g zeta a b t =
      t ^ bilinear D (ThirdTwistedChargeAction.N D g a) b *
        (RatFunc.C (c D g b a : ℂ) * rationalContraction D g zeta b a t⁻¹) := by
  have hphase := congrArg (fun v : ℂˣ => RatFunc.C (v : ℂ))
    (c_mul_reciprocityPhase D g h3 hg a b)
  simp only [Units.val_mul, map_mul] at hphase
  rw [rationalContraction_reciprocity D g h3 hg zeta zeta_primitive.pow_eq_one a b t ht]
  calc
    _ = t ^ bilinear D (ThirdTwistedChargeAction.N D g a) b *
        ((RatFunc.C (c D g a b : ℂ) * RatFunc.C (reciprocityPhase D g zeta a b : ℂ)) *
          rationalContraction D g zeta b a t⁻¹) := by ac_rfl
    _ = _ := by rw [hphase]

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction
