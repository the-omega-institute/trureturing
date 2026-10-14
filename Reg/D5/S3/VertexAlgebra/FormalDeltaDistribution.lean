import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.FormalDeltaDistribution
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.FormalDeltaDistribution
open _root_.D5.S3.VertexAlgebra.SuperFieldProducts

noncomputable section

namespace Reg.D5.S3.VertexAlgebra.FormalDeltaDistribution.EpsilonNeg

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun role _ power => if role = 0 then epsilon (-power) else epsilon power)
    (fun empty => nomatch empty)

def rejected (role : Fin 2) : Realization signature :=
  realize signature
    (fun other parameter power => if other = role then 0 else actual.readout other parameter power)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law realization := ∀ power : ℤ, realization.readout 0 () power = realization.readout 1 () power

theorem exact_source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.FormalDeltaDistribution.epsilon_neg)) ↔ arena.Law actual := by
  simp only [arena, actual, realize]
  norm_num

theorem rejected_law (role : Fin 2) : ¬ arena.Law (rejected role) := by
  intro law
  have equality := law 0
  fin_cases role <;> norm_num [arena, rejected, actual, realize, epsilon] at equality

def family : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.FormalDeltaDistribution.epsilon_neg)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp epsilon_neg, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro other different
      funext parameter power
      simp [rejected, realize, different]
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    fin_cases role <;> refine ⟨(), 0, 1, ?_⟩ <;> norm_num [actual, realize, epsilon]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.VertexAlgebra.FormalDeltaDistribution.epsilon_neg)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.VertexAlgebra.FormalDeltaDistribution.EpsilonNeg.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.FormalDeltaDistribution.EpsilonNeg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.FormalDeltaDistribution
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg", "arg"]
        booleanPredicate := false },
      { path := #["body", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.VertexAlgebra.FormalDeltaDistribution.EpsilonNeg

end
