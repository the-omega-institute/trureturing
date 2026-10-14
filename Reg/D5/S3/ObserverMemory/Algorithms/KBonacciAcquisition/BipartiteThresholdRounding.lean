import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding

open _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ × ℕ × ℕ
  State := fun _ => Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p s => (crossThresholds p.1 p.2.1 p.2.2).card + if s then 1 else 0)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N a b : ℕ) (ha : a ≤ N) (hb : b ≤ N),
    R.readout () (N, a, b) false = a + b - N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 1 (by decide) (by decide)
  norm_num [rejected, realize] at hh

private theorem actual_law : arena.Law actual := by
  intro N a b ha hb
  simpa [actual, realize] using (cross_threshold_card N a b ha hb)

def evidence : Registration arena (type_of% (@cross_threshold_card)) where
  actual := actual
  bridge := by
    simp [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1, 1, 1), false, true, ?_⟩
    simp [actual, realize, crossThresholds]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding.cross_threshold_card)
      (type_of% (realize signature
        (fun _ p s => (crossThresholds p.1 p.2.1 p.2.2).card + if s then 1 else 0)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding.informationUnit
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => (crossThresholds p.1 p.2.1 p.2.2).card + if s then 1 else 0)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.BipartiteThresholdRounding
