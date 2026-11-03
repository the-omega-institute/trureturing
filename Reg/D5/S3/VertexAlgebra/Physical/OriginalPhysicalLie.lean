import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie

open _root_.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure Inputs where
  D : LatticeData
  H : Matrix (Fin D.rank) (Fin D.rank) ℂ
  hHG : H * gramComplex D = 1
  hGH : gramComplex D * H = 1

abbrev Pair (P : Inputs) := primarySpace P.D P.H 1 × primarySpace P.D P.H 1

abbrev signature : Signature where
  Params := Inputs
  State P := Pair P × Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop × Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ P s =>
      (⁅(physicalIdeal P.D P.H P.hHG P.hGH).mkQ s.1.1,
          (physicalIdeal P.D P.H P.hHG P.hGH).mkQ s.1.2⁆ =
        (physicalIdeal P.D P.H P.hHG P.hGH).mkQ
          (zeroModeP P.D P.H P.hHG P.hGH s.1.1 s.1.2), s.2))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ P : Inputs, ∀ ab : Pair P, (r.readout () P (ab, true)).1

theorem actual_law : arena.Law actual := by
  intro P ab
  simpa [actual, realize, physicalBracket_mk] using
    physicalBracket_mk P.D P.H P.hHG P.hGH ab.1 ab.2

def zeroD : LatticeData where
  rank := 0
  G := fun i _ => Fin.elim0 i
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

def zeroInputs : Inputs where
  D := zeroD
  H := 1
  hHG := by ext i; exact Fin.elim0 i
  hGH := by ext i; exact Fin.elim0 i

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (False, False)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [rejected, realize] using h zeroInputs (0 : Pair zeroInputs)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨zeroInputs, ((0 : Pair zeroInputs), true), ((0 : Pair zeroInputs), false), ?_⟩
  intro he
  simpa [actual, realize, physicalBracket_mk] using he

theorem claim : ∀ (P : Inputs), ∀ ab : Pair P,
    ⁅(physicalIdeal P.D P.H P.hHG P.hGH).mkQ ab.1,
      (physicalIdeal P.D P.H P.hHG P.hGH).mkQ ab.2⁆ =
      (physicalIdeal P.D P.H P.hHG P.hGH).mkQ
        (zeroModeP P.D P.H P.hHG P.hGH ab.1 ab.2) := by
  intro P ab
  exact physicalBracket_mk P.D P.H P.hHG P.hGH ab.1 ab.2

def family : Registration arena (type_of% (@claim)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@claim)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Physical.OriginalPhysicalLie
