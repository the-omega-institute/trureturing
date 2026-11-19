import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetFusionRigidity

/-! Exact original source telescopes and typed proof bridges.
Four-slot registration evidence remains incomplete. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeDualCosetFusionRigidity

open _root_.D5.S3.VertexAlgebra.LatticeDualCosetIntertwiner

/- Exact original telescopes and proof terms are source evidence.
   They are not four-slot registrations or validated audit certificates. -/
abbrev sourceScope_charged_source_recurrence :=
  type_of% (@charged_source_recurrence)
theorem source_actual_charged_source_recurrence : sourceScope_charged_source_recurrence :=
  @charged_source_recurrence

abbrev sourceScope_charged_input_recurrence :=
  type_of% (@charged_input_recurrence)
theorem source_actual_charged_input_recurrence : sourceScope_charged_input_recurrence :=
  @charged_input_recurrence

abbrev sourceScope_ground_normalization_character :=
  type_of% (@ground_normalization_character)
theorem source_actual_ground_normalization_character : sourceScope_ground_normalization_character :=
  @ground_normalization_character

abbrev sourceScope_pair_ground_detects_zero :=
  type_of% (@pair_ground_detects_zero)
theorem source_actual_pair_ground_detects_zero : sourceScope_pair_ground_detects_zero :=
  @pair_ground_detects_zero

abbrev sourceScope_ground_sequence_detects_zero :=
  type_of% (@ground_sequence_detects_zero)
theorem source_actual_ground_sequence_detects_zero : sourceScope_ground_sequence_detects_zero :=
  @ground_sequence_detects_zero

abbrev sourceScope_normalized_ground_detects_zero :=
  type_of% (@normalized_ground_detects_zero)
theorem source_actual_normalized_ground_detects_zero : sourceScope_normalized_ground_detects_zero :=
  @normalized_ground_detects_zero

abbrev sourceScope_groundEvaluation_injective :=
  type_of% (@groundEvaluation_injective)
theorem source_actual_groundEvaluation_injective : sourceScope_groundEvaluation_injective :=
  @groundEvaluation_injective

namespace NormalizedGround

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeDualCosetModule LatticeSugawaraCurrents
open LatticeDualCosetIntertwiner LatticeDualCosetConformal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix

noncomputable section

structure Params where
  D : LatticeData
  a : Charge D
  b : Charge D
  H : Matrix (Fin D.rank) (Fin D.rank) ℂ
  hHG : H * gramComplex D = 1
  hGH : gramComplex D * H = 1
  μ : Fin D.rank → ℚ
  ν : Fin D.rank → ℚ
  ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ)
  hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ)

abbrev signature : Signature where
  Params := Params
  State p := Fields p.D
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output role p := match role with
    | true => ℂ
    | false => Fields p.D
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p I => match role with
    | true => groundScalar p.D I p.μ p.ν 0 0
    | false => I)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ p I, Lawful p.D p.a p.b p.H I →
    r.readout true p I = 0 → r.readout false p I = 0

theorem source_bridge : sourceScope_normalized_ground_detects_zero ↔ arena.Law actual := by
  constructor
  · intro h p I hI heval
    exact h p.D p.a p.b p.H I hI p.hHG p.hGH p.μ p.ν p.ha p.hb heval
  · intro h D a b H I hI hHG hGH μ ν ha hb heval
    exact h ⟨D, a, b, H, hHG, hGH, μ, ν, ha, hb⟩ I hI heval

theorem source_actual : arena.Law actual :=
  source_bridge.mp source_actual_normalized_ground_detects_zero

/- The original theorem is equivalent to the law on these two actual
readouts. Whole-family Variation, per-role Sensitivity, actual
ObservationalDependence and exact source-selection binding are not supplied.
In particular, changing only the scalar readout can violate this law only
at a nonzero Lawful field, an existence result absent from the upper bound.
No Contract.Registration or declared_validated status is asserted. -/

end
end NormalizedGround
end Reg.D5.S3.VertexAlgebra.LatticeDualCosetFusionRigidity
