import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockRegularChargedScalar

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockRegularChargedScalar

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockRegularChargedScalar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  first : Charge lattice
  second : Charge lattice

def signature : Signature where
  Params := Parameters
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := PowerSeries ℂ × PowerSeries ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def scalarReadout : Realization signature :=
  realize signature (fun _ parameter _ =>
    (sheetSubstitution (chargedEnergyGaussian parameter.lattice parameter.first parameter.second),
      regularScalarOnSheet parameter.lattice parameter.first parameter.second))
    (fun empty => nomatch empty)

def ratioReadout : Realization signature :=
  realize signature (fun _ parameter _ =>
    (PowerSeries.C (chargeScalar parameter.lattice parameter.first *
        chargeScalar parameter.lattice parameter.second *
          epsilon parameter.lattice parameter.first parameter.second) *
      (_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.clearedPolynomial
        (bilinear parameter.lattice parameter.first parameter.second)).eval₂
          (PowerSeries.C : ℂ →+* PowerSeries ℂ) halfRoot,
      PowerSeries.C (chargeScalar parameter.lattice (parameter.first + parameter.second) *
          epsilon parameter.lattice parameter.first parameter.second) *
        PowerSeries.X ^
          (((bilinear parameter.lattice parameter.first parameter.second).natAbs : ℤ) +
          bilinear parameter.lattice parameter.first parameter.second).toNat *
        chargedEnergyGaussian parameter.lattice parameter.first parameter.second *
        halfLabel (chargeNorm parameter.lattice parameter.first -
          2 * (bilinear parameter.lattice parameter.first parameter.second).natAbs)))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem scalarBridge :
    (type_of% (@actual_charged_scalar_two_sheet)) ↔ arena.Law scalarReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.first parameter.second
  · intro law lattice first second
    exact law ⟨lattice, first, second⟩ ()

theorem ratioBridge :
    (type_of% (@actual_regular_charged_scalar_ratio)) ↔ arena.Law ratioReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.first parameter.second
  · intro law lattice first second
    exact law ⟨lattice, first, second⟩ ()

def escapeFrom := @chargedEnergyLog
def continuation : Contract.Continuation Unit := .unknown

abbrev scalarRealizationObligation :=
  Registration arena (type_of% (@actual_charged_scalar_two_sheet))
abbrev scalarContractObligation := Contract.Registration (@actual_charged_scalar_two_sheet)
  (type_of% scalarReadout) (type_of% escapeFrom) Unit
abbrev ratioRealizationObligation :=
  Registration arena (type_of% (@actual_regular_charged_scalar_ratio))
abbrev ratioContractObligation := Contract.Registration (@actual_regular_charged_scalar_ratio)
  (type_of% ratioReadout) (type_of% escapeFrom) Unit

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockRegularChargedScalar
