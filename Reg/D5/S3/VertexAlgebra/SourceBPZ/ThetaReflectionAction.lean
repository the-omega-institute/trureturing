import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for the order-two theta reflection action. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.SourceBPZ
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open _root_.D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction
open LeanInformationAudit

noncomputable section

structure Params where
  D : LatticeData
  g : ReflectionGroup

abbrev signature : Signature where
  Params := Params
  State p := Carrier p.D × Carrier p.D × Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool × Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p s => (s.2.2,
    sourcePairing p.D (thetaRep p.D p.g s.1) (thetaRep p.D p.g s.2.1) =
      sourcePairing p.D s.1 s.2.1))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p s => (s.2.2, False)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (g : ReflectionGroup)
    (u v : Carrier D), (R.readout () ⟨D, g⟩ (u, v, true)).2

theorem sourceBridge :
    (type_of% (@thetaRep_pairing)) ↔ arena.Law actual := Iff.rfl

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h emptyLattice 0 0 0

def family : Registration arena (type_of% (@thetaRep_pairing)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp (@thetaRep_pairing), rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro i
    refine ⟨⟨emptyLattice, 0⟩, (0, 0, true), (0, 0, false), ?_⟩
    intro h
    have hb := congrArg (fun z : Bool × Prop => z.1) h
    simpa [actual, realize] using hb

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@thetaRep_pairing)
    (Realization signature) Params Unit := {
  unitName := `D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction.thetaRep_pairing.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => (s.2.2,
      sourcePairing p.D (thetaRep p.D p.g s.1) (thetaRep p.D p.g s.2.1) =
        sourcePairing p.D s.1 s.2.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end
end Reg.D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction
