import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.CorrectedInversion.Corrected

/-!
Faithful full-telescope source laws for the original scalar inversion endpoints.
No Contract.Registration or declared_validated status is asserted. Variation,
sensitivity, dependence and current source-selector binding remain obligations
under the delivery's linked audit issue.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.CorrectedInversion.Corrected
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFiniteCorrection LatticeHalfFockCorrectedField
open TwistedGround.ActualChargedAdjoint
open _root_.D5.S3.VertexAlgebra.CorrectedInversion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric (complexSignature complexEqual)
open MvPolynomial
open scoped BigOperators

def homogeneousArena : Arena where
  signature := complexSignature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (R : ℕ),
    IsWeightedHomogeneous (sourceWeight D) p R →
    ∀ (e : ℤ) (x y : ActualTensor D hu),
      readout.readout () ()
        (actualForm D hu ((correctedField D hu (Finsupp.single a p)).coeff e x) y)
        (paritySign (chargeNorm D a / 2) * (-1 : ℂ)^R *
          ∑ j ∈ Finset.range (R + 1),
            actualForm D hu x ((correctedField D hu (Finsupp.single a
              ((j.factorial : ℂ)⁻¹ • (((SourceMobius.sectorL1 D a).toLinearMap^j) p)))).coeff
                (-e-2*chargeNorm D a-4*(R : ℤ)+2*(j : ℤ)) y))
theorem homogeneous_source_bridge :
    (type_of% (@actual_corrected_single_inversion)) ↔ homogeneousArena.Law complexEqual := Iff.rfl
abbrev homogeneousRealizationObligation :=
  Registration homogeneousArena (type_of% (@actual_corrected_single_inversion))

def monomialArena : Arena where
  signature := complexSignature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (m : Index D →₀ ℕ) (e : ℤ) (x y : ActualTensor D hu),
    let R := Finsupp.weight (sourceWeight D) m
    readout.readout () ()
      (actualForm D hu ((correctedField D hu
        (Finsupp.single a (monomial m (1 : ℂ)))).coeff e x) y)
      (paritySign (chargeNorm D a / 2) * (-1 : ℂ)^R *
        ∑ j ∈ Finset.range (R + 1),
          actualForm D hu x ((correctedField D hu (Finsupp.single a
            ((j.factorial : ℂ)⁻¹ •
              (((SourceMobius.sectorL1 D a).toLinearMap^j) (monomial m (1 : ℂ)))))).coeff
                (-e-2*chargeNorm D a-4*(R : ℤ)+2*(j : ℤ)) y))
theorem monomial_source_bridge :
    (type_of% (@actual_corrected_monomial_inversion)) ↔ monomialArena.Law complexEqual := Iff.rfl
abbrev monomialRealizationObligation :=
  Registration monomialArena (type_of% (@actual_corrected_monomial_inversion))

end Reg.D5.S3.VertexAlgebra.CorrectedInversion.Corrected
