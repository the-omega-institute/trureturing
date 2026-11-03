import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie

open _root_.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie
open LeanInformationAudit

structure Inputs where
  D : LatticeData
  H : Matrix (Fin D.rank) (Fin D.rank) ℂ
  hHG : H * gramComplex D = 1
  hGH : gramComplex D * H = 1

abbrev signature : Signature where
  Params := Inputs
  State P := primarySpace P.D P.H 1 × primarySpace P.D P.H 1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ P ab =>
      ⁅Submodule.Quotient.mk ab.1, Submodule.Quotient.mk ab.2⁆ =
        Submodule.Quotient.mk (zeroModeP P.D P.H P.hHG P.hGH ab.1 ab.2))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ P : Inputs, ∀ ab : primarySpace P.D P.H 1 × primarySpace P.D P.H 1,
    r.readout () P ab

theorem actual_law : arena.Law actual := by
  intro P ab
  exact physicalBracket_mk P.D P.H P.hHG P.hGH ab.1 ab.2

theorem claim : ∀ (P : Inputs), ∀ ab : primarySpace P.D P.H 1 × primarySpace P.D P.H 1,
    ⁅Submodule.Quotient.mk ab.1, Submodule.Quotient.mk ab.2⁆ =
      Submodule.Quotient.mk (zeroModeP P.D P.H P.hHG P.hGH ab.1 ab.2) := by
  intro P ab
  exact physicalBracket_mk P.D P.H P.hHG P.hGH ab.1 ab.2

def registration : Contract.Registration
    (@claim)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie.actual
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨actual_law⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ P ab =>
      ⁅Submodule.Quotient.mk ab.1, Submodule.Quotient.mk ab.2⁆ =
        Submodule.Quotient.mk (zeroModeP P.D P.H P.hHG P.hGH ab.1 ab.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie
