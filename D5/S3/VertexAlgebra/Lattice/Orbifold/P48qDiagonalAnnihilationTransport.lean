/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qDiagonalAnnihilationTransport
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrated positive signed modes transport the sum-charge annihilation factor. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalAnnihilation
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegratedNormalMode

/-!
The integrated positive signed modes transport the finite annihilation
polynomial of the sum charge to the diagonal of the ordered product. The
polynomial variable is `y⁻¹` and the coefficient series variable is
`t = (x/y)^3 - 1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice Momentum)
open P48qIntegratedNormalMode
open P48qSignedNormalWord (insertMode insertMode_apply)

open private mapScalarToFock from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision
open private translatedPolynomial_generator translateOuter_C translateOuter_X from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedOrderedProduct
open private diagonalInverseRatio fockToSeries_apply annihilationPairing_add_charge from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalAnnihilation
open private mode_positive_single from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation

local notation "R" => PowerSeries Fock
local notation "Cₜ" => (PowerSeries.C : Fock →+* PowerSeries Fock)

/-- A positive signed insertion applies the actual Fock annihilator on the
input momentum summand before the coefficient operator. -/
theorem insertMode_positiveAnnihilator_single (a : Charge lattice) (m : ℕ)
    (T : Module.End ℂ State) (p : Momentum) (P : Fock) :
    insertMode (chargeVector a, .ofNat (m + 1)) T (Finsupp.single p P) =
      T (Finsupp.single p (positiveAnnihilator fixedDualBases a m P)) := by
  have hm : ¬ Int.ofNat (m + 1) < 0 := (Int.natCast_nonneg (m + 1)).not_gt
  rw [insertMode_apply, ite_eq_right hm, Module.End.mul_apply, mode_positive_single]

/-- Shift each Fock generator by its integrated positive mode, multiplied by
the corresponding power of the inverse cover variable. -/
def diagonalAnnihilationShift (B : FixedDualBases) (a : Charge lattice) :
    Fock →ₐ[ℂ] Polynomial R :=
  MvPolynomial.aeval fun j : Mode =>
    Polynomial.C (Cₜ (MvPolynomial.X j)) +
      Polynomial.C (mapScalarToFock (integratedNormalMode (frequency j : ℤ)) *
        Cₜ (positiveAnnihilator B a j.2 (MvPolynomial.X j))) * Polynomial.X ^ frequency j

/-- The residual positive shift of the native sum-charge polynomial is the
actual ordered diagonal substitution, at every coefficient series degree. -/
theorem diagonalAnnihilationPolynomial_transport (B : FixedDualBases) (a b : Charge lattice)
    (P : Fock) :
    Polynomial.aevalTower (diagonalAnnihilationShift B a) Polynomial.X
        (translatedPolynomial B (a + b) P) =
      diagonalInverseCoverPolynomial (translateOuter B b (translatedPolynomial B a P)) := by
  have htransport :
      (Polynomial.aevalTower (diagonalAnnihilationShift B a) Polynomial.X).comp
          (translatedPolynomial B (a + b)) =
        diagonalInverseCoverPolynomial.comp ((translateOuter B b).comp
          (translatedPolynomial B a)) := by
    apply MvPolynomial.algHom_ext
    intro j
    have hmode := C_mul_integratedNormalMode (frequency j : ℤ)
    rw [Int.cast_natCast, zpow_natCast, Units.val_pow_eq_pow_val, coe_diagonalCoverRatioUnit]
      at hmode
    have hscaled :
        Cₜ (algebraMap ℂ Fock (-(frequency j : ℂ) / 3)) *
            mapScalarToFock (integratedNormalMode (frequency j : ℤ)) =
          diagonalInverseRatio ^ frequency j - 1 := by
      simpa only [map_mul, map_sub, map_pow, map_one, mapScalarToFock,
        PowerSeries.map_C, diagonalInverseRatio] using congrArg mapScalarToFock hmode
    have hscale :
        Cₜ (algebraMap ℂ Fock ((frequency j : ℂ) / 3)) *
            mapScalarToFock (integratedNormalMode (frequency j : ℤ)) =
          1 - diagonalInverseRatio ^ frequency j := by
      rw [← neg_sub, ← hscaled, ← neg_mul, ← map_neg, ← map_neg, neg_div, neg_neg]
    have hcorrection :
        mapScalarToFock (integratedNormalMode (frequency j : ℤ)) *
            Cₜ (positiveAnnihilator B a j.2 (MvPolynomial.X j)) =
          (1 - diagonalInverseRatio ^ frequency j) *
            Cₜ (algebraMap ℂ Fock (annihilationPairing B a j)) := by
      rw [positiveAnnihilator_X, ite_eq_left rfl, Algebra.smul_def, mul_one, map_mul, map_mul,
        ← mul_assoc, mul_comm (mapScalarToFock _), hscale]
    simp only [AlgHom.comp_apply, translatedPolynomial_generator, map_sub, map_mul, map_pow,
      translateOuter_C, translateOuter_X, Polynomial.coe_mapAlgHom, Polynomial.map_C,
      Polynomial.map_X, AlgHom.coe_toRingHom, Polynomial.CAlgHom_apply,
      diagonalInverseCoverPolynomial, Polynomial.aevalTower_C, Polynomial.aevalTower_X,
      fockToSeries_apply, AlgHom.commutes, Polynomial.algebraMap_apply,
      PowerSeries.algebraMap_apply, diagonalAnnihilationShift, MvPolynomial.aeval_X,
      annihilationPairing_add_charge, map_add, mul_pow]
    rw [← Polynomial.C_mul (a := mapScalarToFock (integratedNormalMode (frequency j : ℤ))),
      hcorrection]
    simp only [Polynomial.C_mul, Polynomial.C_sub, Polynomial.C_pow, Polynomial.C_1]
    ring
  exact DFunLike.congr_fun htransport P

#print axioms insertMode_positiveAnnihilator_single
#print axioms diagonalAnnihilationShift
#print axioms diagonalAnnihilationPolynomial_transport

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
