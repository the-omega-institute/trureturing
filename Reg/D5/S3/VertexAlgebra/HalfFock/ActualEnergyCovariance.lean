import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance

/- Faithful source reconstruction for both new public laws. These bridges
are an audit attempt, not Contract.Registration or declared_validated.
Variation, sensitivity, observational dependence and recognized source binding
remain unfinished; linked audit issue: https://github.com/the-omega-institute/trureturing/issues/21259. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField _root_.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Covariance
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  h : ℤ
  e : ℤ
abbrev signature : Signature where
  Params := Params
  State p := Carrier p.D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Module.End ℂ (ActualTensor p.D p.hu)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p a =>
  actualTensorL0 p.D p.hu * (correctedField p.D p.hu a).coeff p.e -
    (correctedField p.D p.hu a).coeff p.e * actualTensorL0 p.D p.hu) (fun e => nomatch e)

def law (readout : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (h : ℤ) (a : Carrier D),
    a ∈ grade D h → ∀ e : ℤ,
      readout.readout () ⟨D,hu,h,e⟩ a =
        ((e : ℂ)/2 + (h : ℂ)) • (correctedField D hu a).coeff e

theorem source_bridge : (type_of% (@correctedField_L_zero_commutator)) ↔ law actual := Iff.rfl
end Covariance

namespace SignedOutput
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  h : ℤ
  M : ℤ
  e : ℤ
  a : Carrier D
abbrev signature : Signature where
  Params := Params
  State p := ActualTensor p.D p.hu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ActualTensor p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p x =>
  actualTensorL0 p.D p.hu ((correctedField p.D p.hu p.a).coeff p.e x)) (fun e => nomatch e)

def law (readout : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (h M e : ℤ) (a : Carrier D),
    a ∈ grade D h → ∀ x : ActualTensor D hu,
    actualTensorL0 D hu x = ((D.rank : ℂ)/16 + (M : ℂ)/2) • x →
    readout.readout () ⟨D,hu,h,M,e,a⟩ x =
      ((D.rank : ℂ)/16 + ((M+e+2*h : ℤ) : ℂ)/2) • (correctedField D hu a).coeff e x

theorem source_bridge : (type_of% (@correctedField_signed_output)) ↔ law actual := Iff.rfl
end SignedOutput
end Reg.D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
