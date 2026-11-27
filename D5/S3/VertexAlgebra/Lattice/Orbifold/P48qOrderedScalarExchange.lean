/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderedScalarExchange
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The common rational scalar prefactor of both charged radial orders. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContractionReciprocity

/-!
The common rational prefactor of the two radial orders of the native P48q
charged fields. The forward contraction uses `y / x` and the reverse uses `x / y`.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum U U_comp_single)
open scoped BigOperators

noncomputable section

local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "N" => ThirdTwistedChargeAction.N lattice g
local notation "c₃" => ThirdTwistedChargeCocycle.c lattice g
local notation "ζ" => ThirdTwistedChargeCocycle.zeta
local notation "f" => ThirdTwistedContraction.rationalContraction lattice g ζ
local notation "phase" => ThirdTwistedContraction.reciprocityPhase lattice g ζ

/-- The exponent from contraction reciprocity is symmetric in the charges. -/
theorem normPairing_swap (a b : Charge lattice) :
    bilinear lattice (N a) b = bilinear lattice (N b) a :=
  (ThirdTwistedChargeAction.norm_pairing lattice g g_cube g_isometry a b).trans
    (bilinear_symmetric lattice a (N b))

/-- For `q_a = momentumExponent a p`, the degree after the right charge acts
is `q_a + (N a, b)`. -/
theorem momentumExponent_shift_eq_add_normPairing (a b : Charge lattice) (p : Momentum) :
    momentumExponent a (shift b p) = momentumExponent a p + bilinear lattice (N a) b := by
  have hnorm := (ThirdTwistedChargeAction.norm_pairing lattice g g_cube g_isometry a b).symm
  simp only [momentumExponent, shift_numerator, bilinear_add_right, hnorm, add_assoc]

/-- The same left degree in the sum-charge form used in `orderedChargedProduct_single`. -/
theorem momentumExponent_shift_eq_ordered_degree (a b : Charge lattice) (p : Momentum) :
    momentumExponent a (shift b p) =
      momentumExponent (a + b) p + 3 * bilinear lattice a b - momentumExponent b p := by
  have hadd : bilinear lattice (a + b) p.1 = bilinear lattice a p.1 + bilinear lattice b p.1 := by
    rw [bilinear_symmetric lattice (a + b) p.1, bilinear_add_right,
      bilinear_symmetric lattice p.1 a, bilinear_symmetric lattice p.1 b]
  have hq := ThirdTwistedChargeAction.q_polarization lattice g g_cube g_isometry a b
  rw [momentumExponent_shift_eq_add_normPairing]
  simp only [momentumExponent, hadd]
  omega

private theorem U_single_eq_chargePhase (a : Charge lattice) (p : Momentum) (z : ℂ) :
    U a (Finsupp.single p z) = Finsupp.single (shift a p) (z * chargePhase a p) := by
  have hz : Finsupp.single p z = z • Finsupp.single p (1 : ℂ) := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hz, map_smul, U_ground, Finsupp.smul_single, smul_eq_mul]

/-- The two ground-line phases give the BK multiplier and the sum-charge phase. -/
theorem chargePhase_mul_shift (a b : Charge lattice) (p : Momentum) :
    chargePhase a (shift b p) * chargePhase b p =
      (c₃ a b : ℂ) * chargePhase (a + b) p := by
  have h := U_comp_single a b p 1
  rw [U_ground b, U_single_eq_chargePhase, ThirdTwistedChargeAction.shift_add,
    U_ground (a + b), Finsupp.smul_single] at h
  simpa only [Finsupp.single_eq_same, smul_eq_mul,
    mul_comm (chargePhase b p) (chargePhase a (shift b p))] using
    congrArg (fun v : P48qTwistedChargeAction.Ground => v (shift (a + b) p)) h

open scoped LaurentSeries RatFunc in
/-- The rational contraction expands to the very binomial units used by
`orderedContraction` before substitution of the cover ratio. -/
theorem orderedRationalContraction_X (a b : Charge lattice) :
    (f a b RatFunc.X : LaurentSeries ℂ) =
      ((↑(∏ j ∈ Finset.range 3, ThirdTwistedContraction.binomialUnit
        ((ζ : ℂ) ^ j) ^ bilinear lattice ((g^[j]) a) b) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  simpa only [Units.val_pow_eq_pow_val] using
    ThirdTwistedContraction.rationalContraction_X_expansion lattice g ζ a b

/-- Exact cancellation of the cover exponents with contraction reciprocity. -/
theorem orderedRationalMonomial_exchange (a b : Charge lattice) (p : Momentum)
    (x y : RatFunc ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ (momentumExponent a p + bilinear lattice (N a) b) * y ^ momentumExponent b p *
        f a b (y / x) =
      x ^ momentumExponent a p * y ^ (momentumExponent b p + bilinear lattice (N a) b) *
        RatFunc.C (phase a b : ℂ) * f b a (x / y) := by
  let s : ℤ := bilinear lattice (N a) b
  let qa := momentumExponent a p
  let qb := momentumExponent b p
  change x ^ (qa + s) * y ^ qb * f a b (y / x) =
    x ^ qa * y ^ (qb + s) * RatFunc.C (phase a b : ℂ) * f b a (x / y)
  have hζ : ζ ^ (3 : ℕ) = 1 := ThirdTwistedChargeCocycle.zeta_primitive.pow_eq_one
  have hrec := ThirdTwistedContraction.rationalContraction_reciprocity
    lattice g g_cube g_isometry ζ hζ a b (y / x) (div_ne_zero hy hx)
  rw [inv_div] at hrec
  have hcancel : x ^ (qa + s) * y ^ qb * (y / x) ^ s = x ^ qa * y ^ (qb + s) := by
    calc
      _ = x ^ qa * (y ^ qb * ((y ^ s / x ^ s) * x ^ s)) := by
        rw [zpow_add₀ hx, div_zpow]
        suffices hmul : ∀ u v w t : RatFunc ℂ, u * v * w * t = u * (w * (t * v)) from
          hmul (x ^ qa) (x ^ s) (y ^ qb) (y ^ s / x ^ s)
        intro u v w t
        ac_rfl
      _ = _ := by rw [div_mul_cancel₀ _ (zpow_ne_zero s hx), ← zpow_add₀ hy]
  calc
    _ = (x ^ (qa + s) * y ^ qb * (y / x) ^ s) *
        RatFunc.C (phase a b : ℂ) * f b a (x / y) := by
      rw [hrec]
      ac_rfl
    _ = _ := by rw [hcancel]

/-- The entire scalar prefactor on the input momentum line, with the actual
ordered ground phases and cover degrees. -/
def orderedRationalPrefactor (a b : Charge lattice) (p : Momentum) (x y : RatFunc ℂ) : RatFunc ℂ :=
  RatFunc.C (chargePhase a (shift b p) * chargePhase b p) *
    (x ^ momentumExponent a (shift b p) * y ^ momentumExponent b p * f a b (y / x))

/-- The same prefactor with the ground scalar in its normal-ordered form. -/
theorem orderedRationalPrefactor_eq_c (a b : Charge lattice) (p : Momentum) (x y : RatFunc ℂ) :
    orderedRationalPrefactor a b p x y =
      RatFunc.C (c₃ a b : ℂ) * RatFunc.C (chargePhase (a + b) p) *
        (x ^ momentumExponent a (shift b p) * y ^ momentumExponent b p * f a b (y / x)) := by
  rw [orderedRationalPrefactor, chargePhase_mul_shift, map_mul]

/-- Both radial orders use the same rational prefactor in `RatFunc ℂ`. -/
theorem orderedRationalPrefactor_exchange (a b : Charge lattice) (p : Momentum)
    (x y : RatFunc ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    orderedRationalPrefactor a b p x y = orderedRationalPrefactor b a p y x := by
  have hc : RatFunc.C (c₃ a b : ℂ) * RatFunc.C (phase a b : ℂ) = RatFunc.C (c₃ b a : ℂ) := by
    simpa only [Units.val_mul, map_mul] using
      congrArg (fun z : ℂˣ => RatFunc.C (z : ℂ))
        (ThirdTwistedChargeCocycle.c_mul_reciprocityPhase lattice g g_cube g_isometry a b)
  rw [orderedRationalPrefactor_eq_c a b, orderedRationalPrefactor_eq_c b a,
    momentumExponent_shift_eq_add_normPairing a b p,
    momentumExponent_shift_eq_add_normPairing b a p, normPairing_swap b a, add_comm b a,
    orderedRationalMonomial_exchange a b p x y hx hy]
  calc
    _ = (RatFunc.C (c₃ a b : ℂ) * RatFunc.C (phase a b : ℂ)) *
        RatFunc.C (chargePhase (a + b) p) *
        (y ^ (momentumExponent b p + bilinear lattice (N a) b) *
          x ^ momentumExponent a p * f b a (x / y)) := by ac_rfl
    _ = _ := by rw [hc]

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
