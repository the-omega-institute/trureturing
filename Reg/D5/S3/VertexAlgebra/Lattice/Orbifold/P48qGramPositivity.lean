import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of positive definiteness of the concrete P48q Gram form. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity

open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate (nebeGram)
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev IntegralMatrix48 := Matrix (Fin 48) (Fin 48) ℤ
abbrev RealMatrix48 := Matrix (Fin 48) (Fin 48) ℝ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => IntegralMatrix48) (fun _ => RealMatrix48)

def actual : Realization signature :=
  realize signature
    (fun _ _ G => G.map (Int.cast : ℤ → ℝ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (R.readout () () nebeGram).PosDef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (0 : RealMatrix48).PosDef := h
  have hi := hz.diag_pos (i := 0)
  simp at hi

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have he := congrArg (fun G : RealMatrix48 => G 0 0) h
  change ((1 : IntegralMatrix48) 0 0 : ℝ) = ((0 : IntegralMatrix48) 0 0 : ℝ) at he
  simp at he

def family : Registration arena (type_of% nebeGram_posDef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nebeGram_posDef, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      nebeGram_posDef (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity.nebeGram_posDef.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity.family
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
    (fun _ _ G => G.map (Int.cast : ℤ → ℝ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end
end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
