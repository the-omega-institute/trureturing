import D5.S3.VertexAlgebra.OriginalQRelativeFiniteHpl
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.OriginalQRelativeFiniteHpl

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
  _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
  _root_.D5.S3.VertexAlgebra.OriginalQQuartetSource
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Parameters := Sigma fun lattice : LatticeData =>
  Sigma fun _matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ =>
  Sigma fun _charge : Charge lattice => ℤ

def signature : Signature where
  Params := Parameters
  State parameter := State parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameter state => B parameter.1 0 state)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ (parameter : Parameters) (state : State parameter.1),
    state ∈ originalEnergySector parameter.1 parameter.2.1 parameter.2.2.1 parameter.2.2.2 →
      realization.readout () parameter state ∈
        originalEnergySector parameter.1 parameter.2.1 parameter.2.2.1 parameter.2.2.2

theorem sourceBridge :
    (type_of% (@original_B0_preserves_energy_sector)) ↔ arena.Law actual := by
  constructor
  · intro source parameter state member
    exact source parameter.1 parameter.2.1 parameter.2.2.1 parameter.2.2.2 state member
  · intro law lattice matrix charge level state member
    exact law ⟨lattice, matrix, charge, level⟩ state member

abbrev WardTarget := type_of% (@energy_B0_original_ward)
abbrev LeadingTarget := type_of% (@energy_B0_leading_anticommutes)
abbrev NormalizerTarget := type_of% (@energy_B0_normalizer_anticommutes)
abbrev ProjectorTarget := type_of% (@energy_B0_projector_commutes)
abbrev InverseTarget := type_of% (@energy_B0_finite_inverse_commutes_on_shell)
abbrev TransferTarget := type_of% (@energy_B0_transfer_compatibility_on_shell)

end

end Reg.D5.S3.VertexAlgebra.OriginalQRelativeFiniteHpl
