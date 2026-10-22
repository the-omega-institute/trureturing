import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.ZeroSumSubsets
import Reg.Support.DependentFamily

/-! # Source-bound audits of physical zero-subset restrictions -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.ZeroSumSubsets
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ZeroSumSubsets
open scoped BigOperators

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin k → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev countArena : Arena where
  signature := signature
  Law R := ∀ k t : ℕ, 3 ≤ k →
    (Finset.univ.filter (fun A : Finset (Fin k) =>
      (∑ p ∈ A, R.readout () k t p) = 0)).card ≤ Nat.gcd t (2 ^ k - 1) + 1

abbrev blocksArena : Arena where
  signature := signature
  Law R := ∀ k t : ℕ, 3 ≤ k → ∀ blocks : Finset (Finset (Fin k)),
    (∀ A ∈ blocks, A.Nonempty) →
    Set.PairwiseDisjoint (blocks : Set (Finset (Fin k))) id →
    (∀ A ∈ blocks, (∑ p ∈ A, R.readout () k t p) = 0) →
    2 ^ blocks.card ≤ Nat.gcd t (2 ^ k - 1) + 1

private theorem rejected_count : ¬ countArena.Law rejected := by
  intro h
  have hh := h 3 1 (by decide)
  norm_num [rejected, realize] at hh

private theorem rejected_blocks : ¬ blocksArena.Law rejected := by
  intro h
  have hh := h 3 1 (by decide) ({{(0 : Fin 3)}, {(1 : Fin 3)}})
    (by simp) (by simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun])
    (by simp [rejected, realize])
  norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 3)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def count_registration : Registration countArena (type_of% (@zero_subsets_card_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨zero_subsets_card_le, rejected, rejected_count⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_count⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def blocks_registration : Registration blocksArena (type_of% (@disjoint_zero_blocks_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨disjoint_zero_blocks_bound, rejected, rejected_blocks⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_blocks⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def count_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.ZeroSumSubsets.zero_subsets_card_le)
    (type_of% (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ZeroSumSubsets.zero_subsets_card_le.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ZeroSumSubsets.count_registration
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨count_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.ZeroSumSubsets
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "arg", "fn", "fn", "arg", "body", "fn", "arg", "arg", "body", "fn"],
        stateBinder := 1, functionOperand := false, stateOperand := none,
        booleanPredicate := false }
    ] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def blocks_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.ZeroSumSubsets.disjoint_zero_blocks_bound)
    (type_of% (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ZeroSumSubsets.disjoint_zero_blocks_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ZeroSumSubsets.blocks_registration
  realizationSource := none
  generated := false
  arena := .source ⟨blocksArena⟩
  objectArena := .source ⟨blocksArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source blocksArena ⟨blocks_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.ZeroSumSubsets
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "domain", "body", "body", "fn", "arg", "arg", "body", "fn"],
        stateBinder := 1, functionOperand := false, stateOperand := none,
        booleanPredicate := false }
    ] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms count_registration
#print axioms blocks_registration
#print axioms count_audit
#print axioms blocks_audit
end Reg.D5.S3.Combinatorics.Circle.ZeroSumSubsets
