import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockActualChargedTwoSheetFullNormalJets

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockActualChargedTwoSheetFullNormalJets

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockActualChargedTwoSheetFullNormalJets
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyGaussian
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockRetainedEnergyFactorization
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockScalarLabelledGaussian
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

structure RecParameters where
  object : NativeLattice
  first : Charge object.lattice
  second : Charge object.lattice
  energy : ℕ

def recSignature : Signature where
  Params := RecParameters
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := NativeField parameter.object.lattice parameter.object.native ×
    NativeField parameter.object.lattice parameter.object.native
  Anchor := Empty
  finiteAnchor := inferInstance

def recReadout : Realization recSignature :=
  realize recSignature (fun _ parameter _ =>
    ((parameter.energy + 1 : ℂ) •
        Ytw parameter.object.lattice parameter.object.native
          (Finsupp.single (parameter.first + parameter.second)
            (creationCoeff parameter.object.lattice parameter.first
              (parameter.energy + 1 : ℕ))),
      ∑ frequency ∈ Finset.range (parameter.energy + 1),
        nativeCorrectionEvaluation parameter.object.lattice parameter.object.native
          (parameter.first + parameter.second)
            (retainedEnergyMultiplier parameter.object.lattice parameter.first parameter.second
              frequency *
              correctedCreationEnergy parameter.object.lattice parameter.first
                (parameter.first + parameter.second)
                ((parameter.energy - frequency : ℕ) : ℤ))))
    (fun empty => nomatch empty)

def recArena : Arena where
  signature := recSignature
  Law observation := ∀ parameter,
    (observation.readout () parameter ()).1 = (observation.readout () parameter ()).2

theorem recBridge :
    (type_of% (@retained_energy_field_recurrence)) ↔ recArena.Law recReadout := by
  constructor
  · intro source parameter
    exact source parameter.object parameter.first parameter.second parameter.energy
  · intro law object first second energy
    exact law ⟨object, first, second, energy⟩

abbrev recObligation := Registration recArena (type_of% (@retained_energy_field_recurrence))

structure JetParameters where
  object : NativeLattice
  first : Charge object.lattice
  second : Charge object.lattice
  energy : ℕ
  mode : ℤ
  target : ActualTensor object.lattice object.native

def jetSignature : Signature where
  Params := JetParameters
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.object.lattice parameter.object.native ×
    ActualTensor parameter.object.lattice parameter.object.native
  Anchor := Empty
  finiteAnchor := inferInstance

def jetReadout : Realization jetSignature :=
  realize jetSignature (fun _ parameter _ =>
    ((parameter.energy + 1 : ℂ) • retainedEnergyJet parameter.object parameter.first
        (parameter.first + parameter.second) (parameter.energy + 1 : ℤ)
        parameter.mode parameter.target,
      ∑ frequency ∈ Finset.range (parameter.energy + 1),
        (nativeCorrectionEvaluation parameter.object.lattice parameter.object.native
          (parameter.first + parameter.second)
          (retainedEnergyMultiplier parameter.object.lattice parameter.first parameter.second
            frequency * correctedCreationEnergy parameter.object.lattice parameter.first
              (parameter.first + parameter.second)
              ((parameter.energy - frequency : ℕ) : ℤ))).coeff parameter.mode parameter.target))
    (fun empty => nomatch empty)

def jetArena : Arena where
  signature := jetSignature
  Law observation := ∀ parameter,
    (observation.readout () parameter ()).1 = (observation.readout () parameter ()).2

theorem jetBridge :
    (type_of% (@retained_energy_normal_jet_recurrence)) ↔ jetArena.Law jetReadout := by
  constructor
  · intro source parameter
    exact source parameter.object parameter.first parameter.second parameter.energy
      parameter.mode parameter.target
  · intro law object first second energy mode target
    exact law ⟨object, first, second, energy, mode, target⟩

abbrev jetObligation := Registration jetArena (type_of% (@retained_energy_normal_jet_recurrence))

def finiteJetReadout : Realization jetSignature :=
  realize jetSignature (fun _ parameter _ =>
    (retainedEnergyJet parameter.object parameter.first (parameter.first + parameter.second)
        (parameter.energy : ℤ) parameter.mode parameter.target,
      ∑ normalEnergy ∈ Finset.range (parameter.energy + 1),
        (retainedGaussianJetSummand parameter.object parameter.first parameter.second
          parameter.energy normalEnergy).coeff parameter.mode parameter.target))
    (fun empty => nomatch empty)

def finiteJetArena : Arena where
  signature := jetSignature
  Law observation := ∀ parameter,
    (observation.readout () parameter ()).1 = (observation.readout () parameter ()).2

theorem finiteJetBridge :
    (type_of% (@retained_energy_normal_jet_finite_gaussian)) ↔
      finiteJetArena.Law finiteJetReadout := by
  constructor
  · intro source parameter
    exact source parameter.object parameter.first parameter.second parameter.energy
      parameter.mode parameter.target
  · intro law object first second energy mode target
    exact law ⟨object, first, second, energy, mode, target⟩

abbrev finiteJetObligation := Registration finiteJetArena
  (type_of% (@retained_energy_normal_jet_finite_gaussian))

structure SourceParameters where
  object : NativeLattice
  charge : Charge object.lattice
  weights : Index object.lattice →₀ ℂ
  degree : ℕ
  mode : ℤ
  target : ActualTensor object.lattice object.native

def sourceSignature : Signature where
  Params := SourceParameters
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ActualTensor parameter.object.lattice parameter.object.native ×
    ActualTensor parameter.object.lattice parameter.object.native
  Anchor := Empty
  finiteAnchor := inferInstance

def sourceReadout : Realization sourceSignature :=
  realize sourceSignature (fun _ parameter _ =>
    (((Ytw parameter.object.lattice parameter.object.native
        (Finsupp.single parameter.charge
          (sourceDirection parameter.object.lattice parameter.weights ^ parameter.degree))).coeff
          parameter.mode parameter.target),
      parameter.degree.factorial •
        (nativeCorrectionEvaluation parameter.object.lattice parameter.object.native
          parameter.charge
          (PowerSeries.coeff parameter.degree
            (retainedGaussian parameter.object.lattice parameter.charge parameter.weights))).coeff
          parameter.mode parameter.target))
    (fun empty => nomatch empty)

def sourceArena : Arena where
  signature := sourceSignature
  Law observation := ∀ parameter,
    (observation.readout () parameter ()).1 = (observation.readout () parameter ()).2

theorem sourceBridge :
    (type_of% (@source_normal_jet_gaussian_closed)) ↔ sourceArena.Law sourceReadout := by
  constructor
  · intro source parameter
    exact source parameter.object parameter.charge parameter.weights parameter.degree
      parameter.mode parameter.target
  · intro law object charge weights degree mode target
    exact law ⟨object, charge, weights, degree, mode, target⟩

abbrev sourceObligation := Registration sourceArena
  (type_of% (@source_normal_jet_gaussian_closed))

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockActualChargedTwoSheetFullNormalJets
