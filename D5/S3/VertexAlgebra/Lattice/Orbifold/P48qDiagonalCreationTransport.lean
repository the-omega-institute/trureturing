/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qDiagonalCreationTransport
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrated negative signed modes transport the sum-charge creation factor. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegratedNormalMode

/-!
The negative signed modes transport the creation exponential of the sum charge
to the creation factors of the diagonal charged product. The outer variable is
`y` and the coefficient series variable is `t = (x/y)^3 - 1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice)
open P48qIntegratedNormalMode
open PowerSeries (constantCoeff exp rescale)

open private creationPolynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation
open private constantCoeff_creationSeries from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private creationSeries_add_charge mapScalarToFock coe_diagonalXOverYUnit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision
open private formalExp formalExp_add map_exp_subst from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedExponentialReordering

local notation "R" => PowerSeries Fock
local notation "Cₜ" => (PowerSeries.C : Fock →+* PowerSeries Fock)
local notation "r" => mapScalarToFock diagonalXOverY

/-- The creation exponent contributed by the integrated negative signed modes.
At degree `n + 1` the signed mode is `-((n + 1 : ℕ) : ℤ)`. -/
def diagonalNegativeCreationSeries (B : FixedDualBases) (a : Charge lattice) : PowerSeries R :=
  PowerSeries.mk fun
    | 0 => 0
    | n + 1 => mapScalarToFock (integratedNormalMode (-((n + 1 : ℕ) : ℤ))) *
        Cₜ (creationPolynomial B a n)

/-- The integrated negative modes give the change in the actual creation
exponent under `x = y (1+t)^(1/3)`. -/
theorem diagonalNegativeCreationSeries_eq_rescale_sub (B : FixedDualBases) (a : Charge lattice) :
    diagonalNegativeCreationSeries B a =
      rescale r ((creationSeries B a).map Cₜ) - (creationSeries B a).map Cₜ := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
    simp only [diagonalNegativeCreationSeries, PowerSeries.coeff_mk, map_sub,
      PowerSeries.coeff_rescale, pow_zero, one_mul, sub_self]
  | succ n =>
    let scale : ℂ := (((n + 1 : ℕ) : ℂ) / 3)
    have hmode := C_mul_integratedNormalMode (-((n + 1 : ℕ) : ℤ))
    rw [Int.cast_neg, Int.cast_natCast, neg_neg, zpow_neg, zpow_natCast, ← inv_pow,
      diagonalCoverRatioUnit, inv_inv, Units.val_pow_eq_pow_val, coe_diagonalXOverYUnit] at hmode
    have hscaled : Cₜ (algebraMap ℂ Fock scale) *
        mapScalarToFock (integratedNormalMode (-((n + 1 : ℕ) : ℤ))) = r ^ (n + 1) - 1 := by
      simpa only [map_mul, map_sub, map_pow, map_one, mapScalarToFock, PowerSeries.map_C] using
        congrArg mapScalarToFock hmode
    have hnonzero : scale ≠ 0 :=
      div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (by norm_num)
    have hcancel : Cₜ (algebraMap ℂ Fock scale) *
        Cₜ (scale⁻¹ • creationPolynomial B a n) = Cₜ (creationPolynomial B a n) := by
      rw [← map_mul, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hnonzero, one_smul]
    simp only [diagonalNegativeCreationSeries, PowerSeries.coeff_mk, map_sub,
      PowerSeries.coeff_rescale, PowerSeries.coeff_map, coeff_creationSeries_succ]
    change mapScalarToFock (integratedNormalMode (-((n + 1 : ℕ) : ℤ))) *
        Cₜ (creationPolynomial B a n) =
      r ^ (n + 1) * Cₜ (scale⁻¹ • creationPolynomial B a n) -
        Cₜ (scale⁻¹ • creationPolynomial B a n)
    rw [← sub_one_mul, ← hscaled, mul_right_comm, hcancel, mul_comm]

/-- The negative signed-mode exponential transports the native sum-charge
creation factor to the two creation factors of the diagonal product. -/
theorem diagonalCreationExponential_transport (B : FixedDualBases) (a b : Charge lattice) :
    (exp R).subst (diagonalNegativeCreationSeries B a) *
        (creationExponential B (a + b)).map Cₜ =
      rescale r ((creationExponential B a).map Cₜ) * (creationExponential B b).map Cₜ := by
  let A (c : Charge lattice) := (creationSeries B c).map Cₜ
  have hA (c : Charge lattice) : constantCoeff (A c) = 0 := by
    change constantCoeff ((creationSeries B c).map Cₜ) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_creationSeries, map_zero]
  have hS : constantCoeff (diagonalNegativeCreationSeries B a) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, diagonalNegativeCreationSeries,
      PowerSeries.coeff_mk]
  have hrescaled : constantCoeff (rescale r (A a)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
      one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hA]
  have htransport : diagonalNegativeCreationSeries B a + A (a + b) =
      rescale r (A a) + A b := by
    have hadd : A (a + b) = A a + A b := by
      simp only [A, creationSeries_add_charge, map_add]
    rw [diagonalNegativeCreationSeries_eq_rescale_sub, hadd]
    change rescale r (A a) - A a + (A a + A b) = _
    abel
  have hExp (c : Charge lattice) :
      (creationExponential B c).map Cₜ = formalExp (A c) :=
    map_exp_subst Cₜ _ (constantCoeff_creationSeries B c)
  have hrescaleExp : rescale r (formalExp (A a)) = formalExp (rescale r (A a)) := by
    simp only [formalExp, PowerSeries.rescale_eq_subst]
    exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' (hA a))
      (PowerSeries.HasSubst.smul_X' r) (exp R)
  calc
    _ = formalExp (diagonalNegativeCreationSeries B a + A (a + b)) := by
      change formalExp (diagonalNegativeCreationSeries B a) * _ = _
      rw [hExp, formalExp_add hS (hA (a + b))]
    _ = _ := by
      rw [htransport, formalExp_add hrescaled (hA b), hExp a, hExp b, hrescaleExp]

#print axioms diagonalNegativeCreationSeries
#print axioms diagonalNegativeCreationSeries_eq_rescale_sub
#print axioms diagonalCreationExponential_transport

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
