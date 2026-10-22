import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution

open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := ℤ
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := PowerSeries ℂ × PowerSeries ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def relationReadout : Realization signature :=
  realize signature (fun _ _ _ =>
    (twoSheetSeries * (1 - PowerSeries.X) ^ 2, 4 * PowerSeries.X))
    (fun empty => nomatch empty)

def rootReadout : Realization signature :=
  realize signature (fun _ _ _ =>
    (sheetSubstitution halfRoot,
      (1 - PowerSeries.X) * (1 + PowerSeries.X : PowerSeries ℂ)⁻¹))
    (fun empty => nomatch empty)

def labelReadout : Realization signature :=
  realize signature (fun _ label _ =>
    (sheetSubstitution (halfLabel label), twoSheetLabel label))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    (observation.readout () parameter state).1 = (observation.readout () parameter state).2

theorem relationBridge :
    (type_of% (@formal_two_sheet_relation)) ↔ arena.Law relationReadout := by
  constructor
  · intro source parameter state
    exact source
  · intro law
    exact law (0 : ℤ) ()

theorem rootBridge :
    (type_of% (@original_half_root_two_sheet)) ↔ arena.Law rootReadout := by
  constructor
  · intro source parameter state
    exact source
  · intro law
    exact law (0 : ℤ) ()

theorem labelBridge :
    (type_of% (@original_half_integer_all_label_two_sheet)) ↔ arena.Law labelReadout := by
  constructor
  · intro source label state
    exact source label
  · intro law label
    exact law label ()

def escapeFrom := @halfRoot
def continuation : Contract.Continuation Unit := .unknown

abbrev relationRealizationObligation :=
  Registration arena (type_of% (@formal_two_sheet_relation))
abbrev rootRealizationObligation :=
  Registration arena (type_of% (@original_half_root_two_sheet))
abbrev labelRealizationObligation :=
  Registration arena (type_of% (@original_half_integer_all_label_two_sheet))
abbrev relationContractObligation := Contract.Registration (@formal_two_sheet_relation)
  (type_of% relationReadout) (type_of% escapeFrom) Unit
abbrev rootContractObligation := Contract.Registration (@original_half_root_two_sheet)
  (type_of% rootReadout) (type_of% escapeFrom) Unit
abbrev labelContractObligation := Contract.Registration (@original_half_integer_all_label_two_sheet)
  (type_of% labelReadout) (type_of% escapeFrom) Unit

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution
