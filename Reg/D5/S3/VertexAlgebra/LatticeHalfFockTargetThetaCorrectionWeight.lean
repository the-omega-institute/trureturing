import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCorrectionWeight

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCorrectionWeight

open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraConformal
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGrading
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure Parameters where
  lattice : LatticeData
  charge : Charge lattice

structure State (parameter : Parameters) where
  polynomial : Oscillator parameter.lattice
  shift : ℕ

def signature : Signature where
  Params := Parameters
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Oscillator parameter.lattice × Oscillator parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun _ parameter state =>
    (oscillatorEuler parameter.lattice (Corr parameter.lattice parameter.charge state.polynomial state.shift) + (state.shift : ℂ) • Corr parameter.lattice parameter.charge state.polynomial state.shift,
     Corr parameter.lattice parameter.charge
      (oscillatorEuler parameter.lattice state.polynomial) state.shift)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem bridge : (type_of% (@Corr_Euler)) ↔ arena.Law readout := by
  constructor
  · intro theoremProof parameter state
    exact theoremProof parameter.lattice parameter.charge state.polynomial state.shift
  · intro law lattice charge polynomial shift
    exact law ⟨lattice, charge⟩ ⟨polynomial, shift⟩

def escapeFrom := @Corr
def continuation : Contract.Continuation Unit := .unknown
abbrev realizationObligation := Registration arena (type_of% (@Corr_Euler))
abbrev contractObligation := Contract.Registration (@Corr_Euler)
  (type_of% readout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCorrectionWeight
