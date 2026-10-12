import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Resource.SeparableConeResidualWitness
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Resource.CompositeCones
open _root_.D5.S3.Resource.CompositeConeDuality
open _root_.D5.S3.Resource.SeparableConeResidualWitness
open scoped ComplexOrder Kronecker

noncomputable section
namespace Reg.D5.S3.Resource.SeparableConeResidualWitness

namespace Generator

abbrev signature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := CompositeMatrix p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := CompositeMatrix p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} {S : CompositeMatrix m n},
    S ∈ sourceGenerators m n → separableCone (R.readout () ⟨m, n⟩ S)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1)
    ⟨(1 : Matrix (Fin 1) (Fin 1) ℂ), 1, PosSemidef.one, PosSemidef.one, rfl⟩
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤ -1 at hd
  norm_num [Complex.le_def] at hd

def family : Registration arena (type_of% @generator_separable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨generator_separable, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
    intro h
    have he := congrFun (congrFun h (0, 0)) (0, 0)
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@generator_separable) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Resource.SeparableConeResidualWitness.Generator.unit
  realizationName := `Reg.D5.S3.Resource.SeparableConeResidualWitness.Generator.family
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
    owner := `D5.S3.Resource.SeparableConeResidualWitness
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Generator

end Reg.D5.S3.Resource.SeparableConeResidualWitness
