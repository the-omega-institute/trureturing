/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qDiagonalCreationDerivative
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficientwise diagonal differentiation of the native creation exponential. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qDiagonalCreationTransport

/-!
The coefficientwise derivative in the diagonal variable `t` of the native
creation exponential. The outer variable `y` is held fixed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice)
open P48qIntegratedNormalMode (integratedNormalMode)
open PowerSeries (coeff constantCoeff derivative rescale)

open private creationPolynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation
open private mapScalarToFock creationExponential_mul_charge from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision
open private formalExp constantCoeff_formalExp formalExp_mul_neg from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedExponentialReordering

local notation "R" => PowerSeries Fock
local notation "Cₜ" => (PowerSeries.C : Fock →+* R)
local notation "r" => mapScalarToFock diagonalXOverY

/-- Differentiate the coefficient series in `t` at each outer degree in `y`. -/
def diagonalCreationTDerivative (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => derivative (coeff n F)

@[simp] theorem coeff_diagonalCreationTDerivative (F : PowerSeries R) (n : ℕ) :
    coeff n (diagonalCreationTDerivative F) = derivative (coeff n F) :=
  PowerSeries.coeff_mk n _

local notation "Dₜ" => diagonalCreationTDerivative

private theorem constantCoeff_tDerivative (F : PowerSeries R) :
    constantCoeff (Dₜ F) = derivative (constantCoeff F) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_diagonalCreationTDerivative,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

private theorem tDerivative_mul (F G : PowerSeries R) :
    Dₜ (F * G) = Dₜ F * G + F * Dₜ G := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_diagonalCreationTDerivative, map_add, PowerSeries.coeff_mul, map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro ij _
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm (coeff ij.2 G), add_comm]

private theorem tDerivative_comm (F : PowerSeries R) :
    Dₜ (derivative F) = derivative (Dₜ F) := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_derivative, Derivation.leibniz, smul_eq_mul, mul_comm]

private theorem tDerivative_map_C (F : R) : Dₜ (F.map Cₜ) = 0 := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_map]

@[simp] theorem constantCoeff_diagonalNegativeCreationSeries (B : FixedDualBases)
    (a : Charge lattice) : constantCoeff (diagonalNegativeCreationSeries B a) = 0 := by
  rw [diagonalNegativeCreationSeries, PowerSeries.constantCoeff_mk]

private theorem tDerivative_negativeCreationExponential (B : FixedDualBases)
    (a : Charge lattice) :
    Dₜ (formalExp (diagonalNegativeCreationSeries B a)) =
      Dₜ (diagonalNegativeCreationSeries B a) * formalExp (diagonalNegativeCreationSeries B a) := by
  let S := diagonalNegativeCreationSeries B a
  let E := formalExp S
  let Eneg := formalExp (-S)
  have hS : constantCoeff S = 0 := constantCoeff_diagonalNegativeCreationSeries B a
  have hneg : constantCoeff (-S) = 0 := by simp [hS]
  have exp_derivative (p : PowerSeries R) (hp : constantCoeff p = 0) :
      derivative (formalExp p) = formalExp p * derivative p := by
    rw [formalExp, PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hp),
      PowerSeries.derivative_exp]
  have hE : derivative E = E * derivative S := exp_derivative S hS
  have hEneg : derivative Eneg = -(Eneg * derivative S) := by
    simpa only [map_neg, mul_neg] using exp_derivative (-S) hneg
  have hmul : E * Eneg = 1 := formalExp_mul_neg hS
  have hDE : derivative (Dₜ E) = Dₜ E * derivative S + E * derivative (Dₜ S) := by
    rw [← tDerivative_comm, hE, tDerivative_mul, tDerivative_comm]
  have hE₀ : constantCoeff E = 1 := constantCoeff_formalExp hS
  let _ : HasUniqueDiv R := .of_module_rat R
  have hquot : Dₜ E * Eneg = Dₜ S := by
    apply PowerSeries.derivative.ext
    · simp only [Derivation.leibniz, smul_eq_mul, hDE, hEneg]
      calc
        _ = (E * Eneg) * derivative (Dₜ S) := by ring
        _ = _ := by rw [hmul, one_mul]
    · simp only [map_mul, constantCoeff_tDerivative, hS, hE₀, map_zero,
        PowerSeries.derivative_one, zero_mul]
  change Dₜ E = Dₜ S * E
  rw [← hquot, mul_assoc, mul_comm Eneg E, hmul, mul_one]

/-- The two native creation factors with the first rescaled by `x/y`. -/
def nativeDiagonalCreationExponential (B : FixedDualBases) (a b : Charge lattice) :
    PowerSeries R :=
  rescale r ((creationExponential B a).map Cₜ) * (creationExponential B b).map Cₜ

/-- The logarithmic (t)-derivative of the native creation product is the
coefficientwise derivative of its integrated negative-mode exponent. -/
theorem nativeDiagonalCreationExponential_derivative (B : FixedDualBases) (a b : Charge lattice) :
    Dₜ (nativeDiagonalCreationExponential B a b) =
      Dₜ (diagonalNegativeCreationSeries B a) * nativeDiagonalCreationExponential B a b := by
  rw [nativeDiagonalCreationExponential, ← diagonalCreationExponential_transport]
  change Dₜ (formalExp (diagonalNegativeCreationSeries B a) *
      (creationExponential B (a + b)).map Cₜ) = _
  rw [tDerivative_mul, tDerivative_map_C, mul_zero, add_zero,
    tDerivative_negativeCreationExponential, mul_assoc, formalExp]

@[simp] theorem constantCoeff_diagonalNegativeCreationSeries_derivative (B : FixedDualBases)
    (a : Charge lattice) : constantCoeff (Dₜ (diagonalNegativeCreationSeries B a)) = 0 := by
  rw [constantCoeff_tDerivative, constantCoeff_diagonalNegativeCreationSeries, map_zero]

/-- At positive outer degree `s`, only the weight of signed mode `-s` is
differentiated. Its creation polynomial is constant in `t`. -/
theorem coeff_diagonalNegativeCreationSeries_derivative (B : FixedDualBases) (a : Charge lattice)
    (s : ℕ) (hs : 0 < s) :
    coeff s (Dₜ (diagonalNegativeCreationSeries B a)) =
      mapScalarToFock (derivative (integratedNormalMode (-(s : ℤ)))) *
        Cₜ (creationPolynomial B a (s - 1)) := by
  have derivative_mapScalarToFock (f : PowerSeries ℂ) :
      derivative (mapScalarToFock f) = mapScalarToFock (derivative f) := by
    apply PowerSeries.ext
    intro n
    simp only [mapScalarToFock, PowerSeries.coeff_derivative, PowerSeries.coeff_map, map_mul,
      map_add, map_natCast, map_one]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simp only [coeff_diagonalCreationTDerivative, diagonalNegativeCreationSeries,
    PowerSeries.coeff_mk, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_C,
    zero_mul, zero_add, derivative_mapScalarToFock, Nat.succ_sub_one, mul_comm]

@[simp] theorem constantCoeff_nativeDiagonalCreationExponential (B : FixedDualBases)
    (a b : Charge lattice) : constantCoeff (nativeDiagonalCreationExponential B a b) = 1 := by
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, nativeDiagonalCreationExponential,
    map_mul, PowerSeries.coeff_rescale, pow_zero, PowerSeries.coeff_map,
    coeff_zero_creationExponential, map_one, one_mul]

@[simp] theorem constantCoeff_nativeDiagonalCreationExponential_derivative (B : FixedDualBases)
    (a b : Charge lattice) : constantCoeff (Dₜ (nativeDiagonalCreationExponential B a b)) = 0 := by
  rw [constantCoeff_tDerivative, constantCoeff_nativeDiagonalCreationExponential,
    PowerSeries.derivative_one]

/-- Setting `t = 0` recovers the sum-charge creation exponential. -/
theorem nativeDiagonalCreationExponential_eval (B : FixedDualBases) (a b : Charge lattice) :
    (nativeDiagonalCreationExponential B a b).map (constantCoeff : R →+* Fock) =
      creationExponential B (a + b) := by
  have hr : constantCoeff r = 1 := by
    rw [mapScalarToFock, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_diagonalXOverY, map_one]
  rw [nativeDiagonalCreationExponential, map_mul, ← creationExponential_mul_charge]
  congr 1
  all_goals
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_rescale, map_mul, map_pow, hr,
      one_pow, PowerSeries.constantCoeff_C, one_mul]

#print axioms diagonalCreationTDerivative
#print axioms coeff_diagonalCreationTDerivative
#print axioms constantCoeff_diagonalNegativeCreationSeries
#print axioms nativeDiagonalCreationExponential
#print axioms nativeDiagonalCreationExponential_derivative
#print axioms constantCoeff_diagonalNegativeCreationSeries_derivative
#print axioms coeff_diagonalNegativeCreationSeries_derivative
#print axioms constantCoeff_nativeDiagonalCreationExponential
#print axioms constantCoeff_nativeDiagonalCreationExponential_derivative
#print axioms nativeDiagonalCreationExponential_eval

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
