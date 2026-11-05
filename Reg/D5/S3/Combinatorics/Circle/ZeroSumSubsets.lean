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


abbrev carryArena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (hk : 0 < k) (t : ℕ)
    (n : Fin k → ℕ) (hne : n ≠ 0),
    ∃! z : Finset (Fin k) × (Fin k → ℕ),
      let A := z.1
      let m := z.2
      let N : ℕ := 2 ^ k - 1
      let s := R.readout () k t
      let eps : Fin k → ℤ := fun i =>
        if modulus k < 4 * s i then 1
        else if 4 * s i < -modulus k then -1 else 0
      A.Nonempty ∧
      (∀ i : Fin k, (n i : ℤ) =
        (if i ∈ A then (1 : ℤ) else 0) +
          2 * (m i : ℤ) - (m ((finRotate k).symm i) : ℤ)) ∧
      (∑ i : Fin k, n i) = A.card + (∑ i : Fin k, m i) ∧
      (∑ i : Fin k, n i * 2 ^ i.val) =
        (∑ i ∈ A, 2 ^ i.val) + N * m ⟨k - 1, by omega⟩ ∧
      (∑ i : Fin k, (n i : ℤ) * s i) =
        (∑ i ∈ A, s i) + modulus k *
          (∑ i : Fin k, (m i : ℤ) * eps i) ∧
      ((∑ i : Fin k, (n i : ℤ) * s i) = 0 →
        N / Nat.gcd t N ∣ (∑ i ∈ A, 2 ^ i.val)) ∧
      (Nat.Coprime t N →
        (∑ i : Fin k, (n i : ℤ) * s i) = 0 →
        A = Finset.univ ∧
        (∑ i : Fin k, (m i : ℤ) * eps i) = 0 ∧
        (∑ i : Fin k, n i) = k + (∑ i : Fin k, m i) ∧
        k ≤ (∑ i : Fin k, n i) ∧
        ((∑ i : Fin k, n i) = k ↔ ∀ i : Fin k, n i = 1))

private theorem rejected_carry : ¬ carryArena.Law rejected := by
  intro h
  let n : Fin 2 → ℕ := fun i => if i = 0 then 1 else 0
  have hn : n ≠ 0 := by
    intro he
    have hh := congrFun he (0 : Fin 2)
    norm_num [n] at hh
  obtain ⟨z, hz, _⟩ := h 2 (by decide) 1 n hn
  have hc := hz.2.2.2.2.2.2 (by decide : Nat.Coprime 1 (2 ^ 2 - 1))
    (by simp [rejected, realize])
  have hb := hc.2.2.2.1
  norm_num [n, Fin.sum_univ_succ] at hb

def carry_registration : Registration carryArena (type_of% (@cyclic_binary_normal_form)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cyclic_binary_normal_form, rejected, rejected_carry⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_carry⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def carry_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.ZeroSumSubsets.cyclic_binary_normal_form)
    (type_of% (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.ZeroSumSubsets.cyclic_binary_normal_form.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ZeroSumSubsets.carry_registration
  realizationSource := none
  generated := false
  arena := .source ⟨carryArena⟩
  objectArena := .source ⟨carryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source carryArena ⟨carry_registration⟩
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
      { path := #["body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "value"],
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false }
    ] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/- The neutral path theorem is genuinely source-generic: its source vector is a
   free argument, and the Boolean potential and modulus are free arguments as
   well.  This exact source witness records the theorem for the audit surface.
   A four-slot variation cannot be supplied for a theorem that is true for
   every readout satisfying its hypotheses, so the remaining audit is left
   explicitly open under issue #22063 rather than manufacturing a rejected
   realization. -/
abbrev neutral_carry_path_source :=
  type_of% (@_root_.D5.S3.Combinatorics.Circle.ZeroSumSubsets.neutral_carry_path)

theorem neutral_carry_path_source_actual : neutral_carry_path_source :=
  @_root_.D5.S3.Combinatorics.Circle.ZeroSumSubsets.neutral_carry_path

#print axioms carry_registration
#print axioms carry_audit

#print axioms count_registration
#print axioms blocks_registration
#print axioms count_audit
#print axioms blocks_audit
end Reg.D5.S3.Combinatorics.Circle.ZeroSumSubsets
