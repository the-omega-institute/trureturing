import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.OriginalColoredBrstMultiplicity

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.OriginalColoredBrstMultiplicity

open _root_.D5.S3.VertexAlgebra.OriginalColoredBrstMultiplicity
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
open _root_.D5.S3.VertexAlgebra.OriginalBrstReassembly
open _root_.D5.S3.VertexAlgebra.OriginalQEnergyInclusionPairing
open _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
open _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockMetric
open _root_.D5.S3.VertexAlgebra.RelativePairing.AbsolutePhysicalNoGhost
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure TransverseParameters where
  lattice : LatticeData
  xAxis : Fin lattice.rank
  yAxis : Fin lattice.rank
  distinct : xAxis ≠ yAxis

def transverseSignature : Signature where
  Params := TransverseParameters
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def transverseReadout : Realization transverseSignature :=
  realize transverseSignature (fun _ parameter level =>
    (Nat.card (TransverseDownIndex parameter.lattice parameter.xAxis parameter.yAxis level),
      coloredMultiplicity (parameter.lattice.rank - 2) level)) (fun empty => nomatch empty)

def transverseArena : Arena where
  signature := transverseSignature
  Law readout := ∀ parameter level,
    (readout.readout () parameter level).1 = (readout.readout () parameter level).2

theorem transverseBridge : (type_of% (@downIndex_card)) ↔
    transverseArena.Law transverseReadout := by
  constructor
  · intro source parameter level
    exact source parameter.lattice parameter.xAxis parameter.yAxis parameter.distinct level
  · intro law lattice xAxis yAxis distinct level
    exact law ⟨lattice, xAxis, yAxis, distinct⟩ level

structure PhysicalParameters where
  lattice : LatticeData
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  leftGram : inverse * gramComplex lattice = 1
  rightGram : gramComplex lattice * inverse = 1
  charge : Charge lattice
  critical : lattice.rank = 26
  chargeNonzero : charge ≠ 0
  lorentzian : _root_.D5.S3.QuadraticForms.ActualSignature.signature
    (gramReal lattice).toQuadraticForm' = (lattice.rank : ℤ) - 2

def physicalSignature : Signature where
  Params := PhysicalParameters
  State parameter := {level : ℤ // chosenH parameter.lattice parameter.charge + (level : ℂ) - 1 = 0}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)
  Anchor := Empty
  finiteAnchor := inferInstance

def physicalReadout : Realization physicalSignature :=
  realize physicalSignature (fun _ parameter state =>
    let sector := originalEnergySector parameter.lattice parameter.inverse parameter.charge state.val
    let stable := energyStable parameter.lattice parameter.inverse parameter.leftGram
      parameter.rightGram parameter.charge state.val
    ((Module.finrank ℂ (ghostCohomology parameter.lattice parameter.inverse parameter.leftGram
        parameter.rightGram parameter.critical sector stable 1),
      Module.finrank ℂ (ghostCohomology parameter.lattice parameter.inverse parameter.leftGram
        parameter.rightGram parameter.critical sector stable 2),
      Module.finrank ℂ (Cohomology parameter.lattice parameter.inverse parameter.leftGram
        parameter.rightGram parameter.critical sector stable)),
      (p24 state.val, p24 state.val, 2 * p24 state.val))) (fun empty => nomatch empty)

def physicalArena : Arena where
  signature := physicalSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem physicalBridge : (type_of% (@original_brst_multiplicities)) ↔
    physicalArena.Law physicalReadout := by
  constructor
  · intro source parameter state
    have dimensions := source parameter.lattice parameter.inverse parameter.leftGram
      parameter.rightGram parameter.charge state.val parameter.critical state.property
      parameter.chargeNonzero parameter.lorentzian
    exact Prod.ext dimensions.1 (Prod.ext dimensions.2.1 dimensions.2.2)
  · intro law lattice inverse leftGram rightGram charge level critical shell nonzero lorentzian
    have dimensions := law ⟨lattice, inverse, leftGram, rightGram, charge, critical, nonzero,
      lorentzian⟩ ⟨level, shell⟩
    exact ⟨congrArg Prod.fst dimensions, congrArg (fun triple => triple.2.1) dimensions,
      congrArg (fun triple => triple.2.2) dimensions⟩

def physicalEscapeFrom := @downOccupationEquiv
def physicalContinuation : Contract.Continuation Unit := .unknown

abbrev transverseRealizationObligation := Registration transverseArena (type_of% (@downIndex_card))
abbrev transverseContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@downIndex_card)
    (type_of% transverseReadout) (type_of% physicalEscapeFrom) Unit
abbrev physicalRealizationObligation := Registration physicalArena
  (type_of% (@original_brst_multiplicities))
abbrev physicalContractObligation :=
  Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@original_brst_multiplicities)
    (type_of% physicalReadout) (type_of% physicalEscapeFrom) Unit

end

end Reg.D5.S3.VertexAlgebra.OriginalColoredBrstMultiplicity
