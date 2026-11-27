import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Ring

/-!
The rational order-three contraction in the cover coordinate `t = y / x`.
Taking `u = ζ⁻¹` gives the factors `1 - ζ^(-j) t`. Taking `u = ζ` gives the
rational function whose expansion is `ThirdTwistedContraction.scalar_contraction`.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
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

theorem coe_reciprocityPhase (u : ℂˣ) (a b : Charge D) :
    (reciprocityPhase D g u a b : ℂ) =
      ∏ j ∈ Finset.range 3, (-(↑(u ^ j) : ℂ)) ^ bilinear D ((g^[j]) a) b := by
  simp only [reciprocityPhase, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    Units.val_mul, Units.val_mk0, neg_mul, one_mul]

theorem sum_orbitPairing (a b : Charge D) :
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
theorem rationalContraction_inv_root (u : ℂˣ) (hu : u ^ (3 : ℕ) = 1)
    (a b : Charge D) (t : RatFunc ℂ) :
    rationalContraction D g u⁻¹ a b t = rationalContraction D g u b a t := by
  have hpairOne : bilinear D (g b) a = bilinear D (g (g a)) b := by
    rw [bilinear_symmetric D (g b) a]
    simpa only [h3 a] using hg (g (g a)) b
  have hpairTwo : bilinear D (g (g b)) a = bilinear D (g a) b := by
    rw [bilinear_symmetric D (g (g b)) a]
    simpa only [h3 b] using (hg a (g (g b))).symm
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

open P48qTwistedChargeAction (lattice g_cube g_isometry)

local notation "ζ" => ThirdTwistedChargeCocycle.zeta

/-- The native power series is the expansion at `X = 0` with root parameter `ζ`. -/
theorem rationalContraction_X_expansion_native (a b : Charge lattice) :
    (rationalContraction lattice P48qTwistedChargeAction.g ζ a b RatFunc.X : LaurentSeries ℂ) =
      ((PowerSeries.exp ℂ).subst (contractionExponent a b) : LaurentSeries ℂ) := by
  rw [scalar_contraction]
  simpa only [Units.val_pow_eq_pow_val] using
    rationalContraction_X_expansion lattice P48qTwistedChargeAction.g ζ a b

/-- Reciprocity for the factors `1 - ζ^(-j) X` in the native lattice.
Both products use the negative-index convention and the phase is explicit. -/
theorem rationalContraction_negative_reciprocity (a b : Charge lattice) :
    let g := P48qTwistedChargeAction.g
    rationalContraction lattice g ζ⁻¹ a b RatFunc.X =
      RatFunc.X ^ (∑ j ∈ Finset.range 3, bilinear lattice ((g^[j]) a) b) *
        RatFunc.C (∏ j ∈ Finset.range 3,
          (-((ζ : ℂ) ^ (-(j : ℤ)))) ^ bilinear lattice ((g^[j]) a) b) *
        rationalContraction lattice g ζ⁻¹ b a RatFunc.X⁻¹ := by
  have hζ : (ζ⁻¹ : ℂˣ) ^ (3 : ℕ) = 1 := by
    rw [inv_pow, ThirdTwistedChargeCocycle.zeta_primitive.pow_eq_one, inv_one]
  dsimp only
  have h := rationalContraction_reciprocity lattice P48qTwistedChargeAction.g g_cube g_isometry
    ζ⁻¹ hζ a b RatFunc.X RatFunc.X_ne_zero
  rw [← sum_orbitPairing lattice P48qTwistedChargeAction.g a b, coe_reciprocityPhase] at h
  simpa only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow, zpow_neg,
    zpow_natCast] using h

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction
