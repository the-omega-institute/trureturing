import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockNativeJointSupport

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeJointSupport

open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeJointSupport
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeNormalActions
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

structure Parameters where
  lattice : LatticeData
  native : IsUnit lattice.G.det
  charge : Charge lattice
  source : CorrectionPolynomial lattice
  exponent : ℤ
  polynomial : Oscillator lattice

def signature : Signature where
  Params := Parameters
  State parameter := ActualTensor parameter.lattice parameter.native
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.lattice parameter.native ×
    (NativeModeIndex parameter.lattice → ActualTensor parameter.lattice parameter.native)
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter state =>
    ((nativeCorrectionEvaluation parameter.lattice parameter.native parameter.charge
      parameter.source).coeff parameter.exponent
        (tensorMultiply parameter.lattice parameter.native parameter.polynomial state),
    fun index => nativeModeTerm parameter.lattice parameter.native parameter.charge parameter.source
      parameter.exponent parameter.polynomial state index))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ (parameter : Parameters)
      (state : ActualTensor parameter.lattice parameter.native),
    ∃ finiteModes : Finset (NativeModeIndex parameter.lattice),
      (∀ index ∉ finiteModes, (observation.readout () parameter state).2 index = 0) ∧
      (observation.readout () parameter state).1 =
        ∑ index ∈ finiteModes, (observation.readout () parameter state).2 index

theorem bridge :
    (type_of% (@actual_native_correction_joint_finite_action)) ↔ arena.Law readout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.native parameter.charge parameter.source
      parameter.exponent parameter.polynomial state
  · intro law lattice native charge source exponent polynomial state
    exact law ⟨lattice, native, charge, source, exponent, polynomial⟩ state

abbrev realizationObligation :=
  Registration arena (type_of% (@actual_native_correction_joint_finite_action))

abbrev contractObligation := Contract.Registration
  (@actual_native_correction_joint_finite_action) (type_of% readout)
    (type_of% (@nativeCorrectionEvaluation)) Unit

#print axioms bridge

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNativeJointSupport
