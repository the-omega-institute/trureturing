import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.GronwallAbundant.Coding
import Reg.Support.SingleDependentReadout

set_option linter.style.longLine false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.GronwallAbundant
open scoped BigOperators

namespace primeCode_injective_on
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature ℕ
  (fun _ => ℕ) (fun L => ℕ × (Fin L → ℕ) × Finset ℕ)
def actual : Realization signature :=
  realize signature (fun _ L N => primeCode L N) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, (fun _ => 0), ∅)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ L : ℕ, Set.InjOn (R.readout () L) {N : ℕ | N ≠ 0 ∧
    ∀ q : ℕ, L ≤ q → N.factorization q ≤ 1}
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 : 1 ∈ {N : ℕ | N ≠ 0 ∧ ∀ q : ℕ, 0 ≤ q → N.factorization q ≤ 1} := by
    refine ⟨by decide, ?_⟩
    intro q hq
    simp
  have h2 : 2 ∈ {N : ℕ | N ≠ 0 ∧ ∀ q : ℕ, 0 ≤ q → N.factorization q ≤ 1} := by
    refine ⟨by decide, ?_⟩
    intro q hq
    have hh := Nat.factorization_lt q (by decide : 2 ≠ 0)
    omega
  have he : (1 : ℕ) = 2 := h 0 h1 h2 rfl
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 1, 2, ?_⟩
  intro he
  have hh : primeEnd 1 = primeEnd 2 := congrArg Prod.fst he
  norm_num [primeEnd, Nat.prime_two.primeFactors] at hh
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.primeCode_injective_on) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.primeCode_injective_on, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.primeCode_injective_on) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.primeCode_injective_on.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.primeCode_injective_on.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ L N => primeCode L N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Coding
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end primeCode_injective_on

namespace prime_code_card_bound
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : Finset ℕ) (M L A K : ℕ),
    (∀ N ∈ s, N ≠ 0) →
    (∀ N ∈ s, primeEnd N < M) →
    (∀ N ∈ s, ∀ q : Fin L, N.factorization q ≤ A) →
    (∀ N ∈ s, ∀ q : ℕ, L ≤ q → N.factorization q ≤ 1) →
    (∀ N ∈ s, (upperHoles N L).card ≤ K) →
    R.readout () () s.card
      (M * (A + 1) ^ L * (∑ j ∈ Finset.range (K + 1), M.choose j))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ∅ 0 0 0 0 (by simp) (by simp) (by simp) (by simp) (by simp)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  omega
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.prime_code_card_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.prime_code_card_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.prime_code_card_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.prime_code_card_bound.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.prime_code_card_bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Coding
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end prime_code_card_bound


namespace small_subsets_card
universe u
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (s : Finset α) (K : ℕ),
    R.readout () () (s.powerset.filter (fun u => u.card ≤ K)).card
      (∑ j ∈ Finset.range (K + 1), s.card.choose j)
private theorem rejected_law : ¬ (arena.{u}).Law rejected := by
  intro h
  exact h (α := ULift.{u} Unit) ∅ 0
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact Nat.one_ne_zero hf
def source_registration : Registration arena.{u} (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.small_subsets_card.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.small_subsets_card.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity (arena.{u}).Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.small_subsets_card.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.small_subsets_card.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.small_subsets_card.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Coding
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end small_subsets_card

namespace binomial_partial_sum_weighted
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M K : ℕ), K ≤ M → ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
    R.readout () () (t ^ K * (∑ j ∈ Finset.range (K + 1), (M.choose j : ℝ)))
      ((1 + t) ^ M)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 le_rfl 0 le_rfl (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.binomial_partial_sum_weighted) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.binomial_partial_sum_weighted, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.binomial_partial_sum_weighted) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.binomial_partial_sum_weighted.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.binomial_partial_sum_weighted.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Coding
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end binomial_partial_sum_weighted

namespace binomial_partial_sum_entropy
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M K : ℕ), 1 ≤ K → K ≤ M →
    R.readout () () (∑ j ∈ Finset.range (K + 1), (M.choose j : ℝ))
      (Real.exp ((K : ℝ) * (1 + Real.log ((M : ℝ) / K))))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 le_rfl le_rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.binomial_partial_sum_entropy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.binomial_partial_sum_entropy, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.binomial_partial_sum_entropy) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.binomial_partial_sum_entropy.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding.binomial_partial_sum_entropy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Coding
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end binomial_partial_sum_entropy
end Reg.D5.S3.Arith.Robin.GronwallAbundant.Coding
