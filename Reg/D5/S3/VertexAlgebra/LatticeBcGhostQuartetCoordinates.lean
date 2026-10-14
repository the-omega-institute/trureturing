import D5.S3.VertexAlgebra.LatticeBcGhostQuartetCoordinates
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostQuartetCoordinates

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

structure Parameters where
  lattice : LatticeData
  frame : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  inverse : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ

def signature : Signature where
  Params := Parameters
  State parameter := Oscillator parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Oscillator parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ parameter polynomial => coordinateSub parameter.lattice parameter.frame polynomial)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter : Parameters,
    parameter.inverse * parameter.frame = 1 →
    parameter.frame * parameter.inverse = 1 →
    Function.Bijective (realization.readout () parameter)

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.OriginalQQuartetSource.coordinateSub_bijective)) ↔
      arena.Law actual := by
  constructor
  · intro source parameter leftInverse rightInverse
    exact source parameter.lattice parameter.frame parameter.inverse leftInverse rightInverse
  · intro law lattice frame inverse leftInverse rightInverse
    exact law ⟨lattice, frame, inverse⟩ leftInverse rightInverse

def variationObligation : Prop := Variation arena actual

def sensitivityObligation : Prop := Sensitivity arena actual

def dependenceObligation : Prop := ObservationalDependence signature actual

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostQuartetCoordinates
