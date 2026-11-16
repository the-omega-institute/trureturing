import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge
import Reg.Support.DependentFamily

/-! Whole natural families for the literal scalar support and row edge. -/
noncomputable section
namespace Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge
open _root_.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
open _root_.D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge
open _root_.D5.S1.Digit.DyadicRowPolynomialRecurrence (wt)
open _root_.D5.S1.Digit.KurkovWeightProductBinomial (a)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ n k => T n k) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
namespace Support
 def arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), wt n + 2 < k → R.readout () n k = 0
 private theorem rejected_bad : ¬ arena.Law rejected := by
  intro hh
  have h := hh 0 3 (by norm_num [wt])
  norm_num [rejected, realize] at h
 def family : Registration arena (type_of% support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨support, rejected, rejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bad⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, 1, 3, ?_⟩
    change T 0 1 ≠ T 0 3
    norm_num [T]
end Support
namespace Edge
 def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () n (wt n + 2) = (a n : ℚ) / ((1 + wt n).factorial : ℚ)
 private theorem rejected_bad : ¬ arena.Law rejected := by
  intro hh
  have h := hh 2
  norm_num [rejected, realize, wt, a, Nat.digits] at h
 def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bad⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, 1, 3, ?_⟩
    change T 0 1 ≠ T 0 3
    norm_num [T]
end Edge

def support_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@support) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge.supportUnit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge.Support.family
  realizationSource := none
  generated := false
  arena := .source ⟨Support.arena⟩
  objectArena := .source ⟨Support.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Support.arena ⟨Support.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => T n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


def edge_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge.edgeUnit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge.Edge.family
  realizationSource := none
  generated := false
  arena := .source ⟨Edge.arena⟩
  objectArena := .source ⟨Edge.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Edge.arena ⟨Edge.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => T n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


#print axioms support_registration
#print axioms edge_registration
end Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge
