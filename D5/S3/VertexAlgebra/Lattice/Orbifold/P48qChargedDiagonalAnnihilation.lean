/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedDiagonalAnnihilation
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite diagonal annihilation factor and its leading collision coefficient. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision

/-!
The finite annihilation factor of the normal-ordered charged P48q product
under `x = y (1+t)^(1/3)`. After collision regularization, its specialization
at `t = 0` gives the leading collision coefficient on every finite state.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge epsilon)
open P48qTwistedChargeAction (lattice g Momentum)
open PowerSeries (constantCoeff)
open scoped BigOperators LaurentSeries

open private translatedPolynomial_generator translateOuter_C translateOuter_X
  inverseCover coeff_mul_inverseCover coeff_ofPowerSeries_map coeff_creation_laurent from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedOrderedProduct
open private groundDiagonalRegular_eval from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision

noncomputable section

attribute [local instance 2000] HahnSeries.instAlgebra

local notation "shift" => ThirdTwistedChargeAction.shift lattice g

private def fockToSeries : Fock →ₐ[ℂ] PowerSeries Fock where
  toRingHom := PowerSeries.C
  commutes' r := by
    change PowerSeries.C (algebraMap ℂ Fock r) = algebraMap ℂ (PowerSeries Fock) r
    exact PowerSeries.algebraMap_apply.symm

private def specializeT : PowerSeries Fock →ₐ[ℂ] Fock where
  toRingHom := constantCoeff
  commutes' r := by
    change constantCoeff (PowerSeries.C (algebraMap ℂ Fock r)) = algebraMap ℂ Fock r
    exact PowerSeries.constantCoeff_C _

private theorem fockToSeries_apply (P : Fock) :
    fockToSeries P = PowerSeries.C P := rfl

private theorem specializeT_apply (S : PowerSeries Fock) :
    specializeT S = constantCoeff S := rfl

private def diagonalInverseRatio : PowerSeries Fock :=
  PowerSeries.map (algebraMap ℂ Fock) P48qTwistedHeisenberg.diagonalCoverRatio

private theorem constantCoeff_diagonalInverseRatio :
    constantCoeff diagonalInverseRatio = 1 := by
  rw [diagonalInverseRatio, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    P48qTwistedHeisenberg.diagonalCoverRatio_branch.1, map_one]

/-- Substitute `x⁻¹ = (1+t)^(-1/3) y⁻¹` in a finite polynomial whose
inner variable is `x⁻¹` and outer variable is `y⁻¹`. The output variable is
`y⁻¹`, with coefficients that are power series in `t`. The inverse
ratio is the reciprocal in `diagonalXOverY_mul_q`. -/
def diagonalInverseCoverPolynomial :
    Polynomial (Polynomial Fock) →ₐ[ℂ] Polynomial (PowerSeries Fock) :=
  Polynomial.aevalTower
    (Polynomial.aevalTower (Polynomial.CAlgHom.comp fockToSeries)
      (Polynomial.C diagonalInverseRatio * Polynomial.X))
    Polynomial.X

private theorem annihilationPairing_add_charge (B : FixedDualBases)
    (a b : Charge lattice) (j : Mode) :
    annihilationPairing B (a + b) j =
      annihilationPairing B a j + annihilationPairing B b j := by
  have h : chargeVector (a + b) = chargeVector a + chargeVector b := by
    funext i
    exact Int.cast_add (a i) (b i)
  simp only [annihilationPairing, h, LinearMap.BilinForm.add_left]

/-- After the diagonal substitution and evaluation at `t = 0`, the ordered
finite annihilation factor is the native factor for the sum charge, as a
polynomial in `y⁻¹`. -/
theorem translatedPolynomial_diagonal (B : FixedDualBases) (a b : Charge lattice) (P : Fock) :
    (diagonalInverseCoverPolynomial (translateOuter B b (translatedPolynomial B a P))).map
        (constantCoeff (R := Fock)) = translatedPolynomial B (a + b) P := by
  have h :
      (Polynomial.mapAlgHom specializeT).comp
        (diagonalInverseCoverPolynomial.comp ((translateOuter B b).comp
          (translatedPolynomial B a))) = translatedPolynomial B (a + b) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, translatedPolynomial_generator, map_sub, map_mul, map_pow,
      translateOuter_C, translateOuter_X, Polynomial.coe_mapAlgHom, Polynomial.map_C,
      Polynomial.map_X,
      AlgHom.coe_toRingHom, Polynomial.CAlgHom_apply, AlgHom.commutes, Polynomial.algebraMap_apply,
      diagonalInverseCoverPolynomial, Polynomial.aevalTower_C, Polynomial.aevalTower_X,
      fockToSeries_apply, specializeT_apply, PowerSeries.constantCoeff_C,
      constantCoeff_diagonalInverseRatio, Polynomial.C_1, one_mul, annihilationPairing_add_charge,
      map_add] <;> ring
  have hSpecialize : specializeT.toRingHom = constantCoeff (R := Fock) := rfl
  rw [← hSpecialize]
  exact DFunLike.congr_fun h P

private theorem coeff_powerSeries_mul_inverseCover {R : Type*} [CommRing R] [Algebra ℂ R]
    (S : PowerSeries R) (Q : Polynomial R) (k : ℤ) :
    (HahnSeries.ofPowerSeries ℤ R S * inverseCover ℂ Q).coeff k =
      ∑ d ∈ Q.support, (HahnSeries.ofPowerSeries ℤ R S).coeff (k + (d : ℤ)) * Q.coeff d := by
  simpa only [Polynomial.map_id, RingHom.id_apply] using
    (coeff_mul_inverseCover ℂ (RingHom.id R) (HahnSeries.ofPowerSeries ℤ R S) Q k)

private theorem constantCoeff_coeff_mul_inverseCover
    (S : PowerSeries (PowerSeries Fock)) (Q : Polynomial (PowerSeries Fock)) (k : ℤ) :
    constantCoeff ((HahnSeries.ofPowerSeries ℤ (PowerSeries Fock) S * inverseCover ℂ Q).coeff k) =
      (HahnSeries.ofPowerSeries ℤ Fock (S.map (constantCoeff (R := Fock))) *
        inverseCover ℂ (Q.map (constantCoeff (R := Fock)))).coeff k := by
  rw [coeff_powerSeries_mul_inverseCover, coeff_mul_inverseCover ℂ, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_mul, coeff_ofPowerSeries_map]

/-- The regular diagonal expansion of the normal-ordered factors on the
momentum summand `p` with Fock polynomial `P` in `orderedChargedProduct_single`.
Here `groundDiagonalRegular` supplies the scalar and creation factors with the
collision power and sum-charge momentum monomial removed. The Laurent variable
is `y` and coefficients are power series in `t`. -/
def chargedDiagonalRegular (B : FixedDualBases) (a b : Charge lattice)
    (p : Momentum) (P : Fock) : LaurentSeries (PowerSeries Fock) :=
  HahnSeries.ofPowerSeries ℤ (PowerSeries Fock) (groundDiagonalRegular B a b p) *
    inverseCover ℂ
      (diagonalInverseCoverPolynomial (translateOuter B b (translatedPolynomial B a P)))

/-- The `t = 0` coefficient on an arbitrary polynomial in one momentum summand
is the native charged field for `a+b` times the lattice cocycle. -/
theorem chargedDiagonalRegular_coeff_single (B : FixedDualBases) (a b : Charge lattice)
    (p : Momentum) (P : Fock) (k : ℤ) :
    Finsupp.single (shift (a + b) p)
      (constantCoeff ((chargedDiagonalRegular B a b p P).coeff
        (k - momentumExponent (a + b) p))) =
      epsilon lattice a b • fieldCoeff B (a + b) k (Finsupp.single p P) := by
  rw [chargedDiagonalRegular, constantCoeff_coeff_mul_inverseCover, translatedPolynomial_diagonal,
    groundDiagonalRegular_eval, fieldCoeff_single, Finsupp.smul_single, smul_smul,
    Algebra.smul_def, coeff_powerSeries_mul_inverseCover, oscillatorCoeff_apply, Finset.mul_sum]
  apply congrArg (Finsupp.single (shift (a + b) p))
  apply Finset.sum_congr rfl
  intro d _
  simp only [map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul, coeff_creation_laurent, mul_assoc]

/-- The leading diagonal coefficient of the regularized normal-ordered product
on every finite momentum/Fock state, restoring the sum-charge momentum degree
on each summand. -/
theorem chargedDiagonalRegular_coeff (B : FixedDualBases) (a b : Charge lattice)
    (v : State) (k : ℤ) :
    (∑ p ∈ v.support, Finsupp.single (shift (a + b) p)
      (constantCoeff ((chargedDiagonalRegular B a b p (v p)).coeff
        (k - momentumExponent (a + b) p)))) =
      epsilon lattice a b • ((HahnModule.of ℂ).symm (chargedField B (a + b) v)).coeff k := by
  calc
    _ = ∑ p ∈ v.support, epsilon lattice a b •
        fieldCoeff B (a + b) k (Finsupp.single p (v p)) :=
      Finset.sum_congr rfl fun p _ => chargedDiagonalRegular_coeff_single B a b p (v p) k
    _ = _ := by
      have hv : (∑ p ∈ v.support, Finsupp.single p (v p)) = v := Finsupp.sum_single v
      rw [← Finset.smul_sum, ← map_sum, hv, chargedField_coeff]

#print axioms translatedPolynomial_diagonal
#print axioms chargedDiagonalRegular_coeff_single
#print axioms chargedDiagonalRegular_coeff

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
