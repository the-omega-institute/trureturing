import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.InversionSeq.ClassCSites
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.InversionSeq.ClassCSites
open _root_.D5.S3.Combinatorics Nonnesting

namespace Reg.D5.S3.Combinatorics.InversionSeq.ClassCSites

namespace safe_append_iff

abbrev signature : Signature where
  Params := Nat
  State _ := List Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature := by
  classical
  exact realize signature (fun _ x w => decide (Safe w x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ w x, r.readout () x w = true ↔
    Avoids w ∧ ∀ i j : Nat, i < j → j < w.length →
      ¬ ForbiddenTriple (w.getD i 0) (w.getD j 0) x

private theorem empty_safe : Safe [] 0 := by
  apply (_root_.D5.S3.Combinatorics.InversionSeq.ClassCSites.safe_append_iff [] 0).mpr
  constructor
  · intro σ hσ ho
    obtain ⟨v, _, _, hsub, _⟩ := ho
    have hlen := hsub.length_le
    simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl <;> simp at hlen
  · intro i j hij hj
    simp at hj

private theorem bad_safe : ¬ Safe [1, 0] 0 := by
  intro hs
  have ht := (_root_.D5.S3.Combinatorics.InversionSeq.ClassCSites.safe_append_iff [1, 0] 0).mp hs
    |>.2 0 1 (by omega) (by simp)
  norm_num [ForbiddenTriple] at ht

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr := (_root_.D5.S3.Combinatorics.InversionSeq.ClassCSites.safe_append_iff [] 0).mp empty_safe
  have ht := (h [] 0).mpr hr
  change false = true at ht
  contradiction

noncomputable def registration : Registration arena
    (∀ w x, Safe w x ↔ Avoids w ∧ ∀ i j : Nat, i < j → j < w.length →
      ¬ ForbiddenTriple (w.getD i 0) (w.getD j 0) x) where
  actual := actual
  bridge := by
    classical
    simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro w x
    simpa only [arena, actual, realize, decide_eq_true_eq] using
      _root_.D5.S3.Combinatorics.InversionSeq.ClassCSites.safe_append_iff w x,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    classical
    intro ⟨⟩
    refine ⟨0, [], [1, 0], ?_⟩
    simp only [actual, realize, empty_safe, bad_safe, decide_true, decide_false]
    decide

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.InversionSeq.ClassCSites.safe_append_iff)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ x w => @decide (Safe w x) (Classical.propDecidable _)) (fun e => nomatch e)))
    Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCSites.safe_append_iff.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCSites.safe_append_iff.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ x w => @decide (Safe w x) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (List Nat)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.InversionSeq.ClassCSites
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end safe_append_iff

end Reg.D5.S3.Combinatorics.InversionSeq.ClassCSites
