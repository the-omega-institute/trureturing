import D5.S3.Arith.Robin.PaddingRatio
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source bridge for monotonicity of reciprocal geometric sums. -/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.PaddingRatio

open _root_.D5.S3.Arith.Robin.PaddingRatio
open _root_.D5.S3.Arith.RobinExponentSwap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => reciprocalGeomSum p k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p a b : ℕ}, a ≤ b → R.readout () p a ≤ R.readout () p b

private theorem actual_law : arena.Law actual := @geom_mono

private theorem source_bridge : (type_of% (@geom_mono)) ↔ arena.Law actual := Iff.rfl

def rejected : Realization signature :=
  realize signature (fun _ _ k => -(k : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (p := 2) (a := 0) (b := 1) (by decide)
  norm_num [rejected, realize] at hh

def evidence : Registration arena (type_of% @geom_mono) where
  actual := actual
  bridge := source_bridge
  variation := ⟨@actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize, reciprocalGeomSum, Finset.sum_range_succ]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@geom_mono) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PaddingRatio.geom_mono.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.PaddingRatio.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p k => reciprocalGeomSum p k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PaddingRatio
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PaddingRatio
