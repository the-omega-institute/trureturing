import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.CoonsAdjacentGrowthRefutation
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection

/-! Source-bound audits of the original Coons counting statements. -/

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open LeanInformationAudit

namespace Reg.D5.S1.Digit.CoonsAdjacentGrowthRefutation
noncomputable section

private lemma count_varies : count 5 4 (repunit 0) ≠ count 5 4 (repunit 1) := by
  rw [count_repunit 5 0 (by norm_num) (by norm_num),
    count_repunit 5 1 (by norm_num) (by norm_num)]
  norm_num

private lemma readout_varies : readout 5 4 1 ≠ readout 5 4 (repunit 1) := by
  have h0 : readout 5 4 1 = 0 := by simp [readout]
  have hp : 0 < readout 5 4 (repunit 1) := by
    unfold readout
    rw [count_repunit 5 1 (by norm_num) (by norm_num)]
    norm_num [repunit]
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  rw [h0]
  exact ne_of_lt hp

private lemma exponent_zero_le : exponent 0 4 ≤ (0 : EReal) := by
  apply iInf_le_of_le 2
  apply iInf_le_of_le (by norm_num : 2 ≤ 2)
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  have he : IsEmpty (Partitions 0 4 n) := ⟨by
    intro a
    have hz : a.val = 0 := by
      ext i
      have h := a.property.1 i
      simpa using (show a.val i = 0 by omega)
    have hw := a.property.2
    rw [hz] at hw
    simp [weight] at hw
    omega⟩
  have hc : count 0 4 n = 0 := @Nat.card_of_isEmpty _ he
  simp [readout, hc]

namespace partitions_finite
abbrev signature : Signature where
  Params := Unit
  State _ := Type
  Output _ _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,1,0,0,0} signature
  (fun _ _ s => Finite s) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,1,0,0,0} signature
  (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ k ell n : ℕ, 2 ≤ ell → Finite (Partitions k ell n)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k ell n : ℕ, 2 ≤ ell → R.readout () () (Partitions k ell n)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 2 0 (by norm_num)
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.partitions_finite, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), PUnit, ℕ, ?_⟩
    change Finite PUnit ≠ Finite ℕ
    intro h
    have hn : Finite ℕ := Eq.mp h inferInstance
    exact @not_finite ℕ inferInstance hn

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.partitions_finite)
    (type_of% (realize.{0,1,0,0,0} signature (fun _ _ s => Finite s) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.CoonsAdjacentGrowthRefutation.partitions_finite.__information_unit,
  realizationName := `Reg.D5.S1.Digit.CoonsAdjacentGrowthRefutation.partitions_finite.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,1,0,0,0} signature (fun _ _ s => Finite s) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.CoonsAdjacentGrowthRefutation, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end partitions_finite

namespace count_positive
abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ
  Output _ _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ p n => count p.1 p.2 n) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ k ell n : ℕ, 2 ≤ ell → ell-1 ≤ k → 0 < count k ell n
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k ell n : ℕ, 2 ≤ ell → ell-1 ≤ k → 0 < R.readout () (k,ell) n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 3 4 0 (by norm_num) (by norm_num)
  exact (Nat.lt_irrefl 0 hh)
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_positive, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(5,4), repunit 0, repunit 1, count_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_positive)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p n => count p.1 p.2 n) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_positive.__information_unit,
  realizationName := `Reg.D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_positive.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p n => count p.1 p.2 n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.CoonsAdjacentGrowthRefutation, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end count_positive

namespace count_upper
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Output _ _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ k n => count k 4 n) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 3) (fun e => nomatch e)
def sourceStatement : Prop := ∀ k m n : ℕ, k ≤ 6 → n < 4^(m+1) → count k 4 n ≤ 2^m
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k m n : ℕ, k ≤ 6 → n < 4^(m+1) → R.readout () k n ≤ 2^m
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 0 (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_upper, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨5, repunit 0, repunit 1, count_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_upper)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ k n => count k 4 n) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_upper.__information_unit,
  realizationName := `Reg.D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_upper.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ k n => count k 4 n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.CoonsAdjacentGrowthRefutation, definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end count_upper

namespace count_repunit
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Output _ _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ k m => count k 4 (repunit m)) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ k m : ℕ, 5 ≤ k → k ≤ 6 → count k 4 (repunit m) = 2^m
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k m : ℕ, 5 ≤ k → k ≤ 6 → R.readout () k m = 2^m
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 5 0 (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_repunit, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨5, 0, 1, count_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_repunit)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ k m => count k 4 (repunit m)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_repunit.__information_unit,
  realizationName := `Reg.D5.S1.Digit.CoonsAdjacentGrowthRefutation.count_repunit.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ k m => count k 4 (repunit m)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.CoonsAdjacentGrowthRefutation, definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end count_repunit

namespace tail_supremum
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Output _ _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ k n => readout k 4 n) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ k N : ℕ, 5 ≤ k → k ≤ 6 → 2 ≤ N → (⨆ (n : ℕ) (_ : N ≤ n), (readout k 4 n : EReal)) = ((1/2 : ℝ) : EReal)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k N : ℕ, 5 ≤ k → k ≤ 6 → 2 ≤ N → (⨆ (n : ℕ) (_ : N ≤ n), (R.readout () k n : EReal)) = ((1/2 : ℝ) : EReal)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 5 2 (by norm_num) (by norm_num) (by norm_num)
  change (⨆ (n : ℕ) (_ : 2 ≤ n), (0 : EReal)) = ((1/2 : ℝ) : EReal) at hh
  have hz : (⨆ (n : ℕ) (_ : 2 ≤ n), (0 : EReal)) ≤ 0 :=
    iSup_le (fun _ => iSup_le (fun _ => le_rfl))
  rw [hh] at hz
  exact not_le_of_gt (EReal.coe_lt_coe (by norm_num : (0 : ℝ) < 1/2)) hz
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.tail_supremum, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨5, 1, repunit 1, readout_varies⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.tail_supremum)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ k n => readout k 4 n) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.CoonsAdjacentGrowthRefutation.tail_supremum.__information_unit,
  realizationName := `Reg.D5.S1.Digit.CoonsAdjacentGrowthRefutation.tail_supremum.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ k n => readout k 4 n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.CoonsAdjacentGrowthRefutation, definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg"], stateBinder := 5,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end tail_supremum

namespace exponent_eq_half
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Output _ _ := EReal
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ k => exponent k 4) (fun e => nomatch e)
def rejected : Realization signature := realize.{0,0,0,0,0} signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def sourceStatement : Prop := ∀ k : ℕ, 5 ≤ k → k ≤ 6 → exponent k 4 = ((1/2 : ℝ) : EReal)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 5 ≤ k → k ≤ 6 → R.readout () () k = ((1/2 : ℝ) : EReal)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 5 (by norm_num) (by norm_num)
  change (0 : EReal) = ((1/2 : ℝ) : EReal) at hh
  exact ne_of_lt (EReal.coe_lt_coe (by norm_num : (0 : ℝ) < 1/2)) hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.exponent_eq_half, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 0, 5, ?_⟩
    change exponent 0 4 ≠ exponent 5 4
    rw [exponent_eq_half 5 (by norm_num) (by norm_num)]
    intro h
    have hh := exponent_zero_le
    rw [h] at hh
    exact not_le_of_gt (EReal.coe_lt_coe (by norm_num : (0 : ℝ) < 1/2)) hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.CoonsAdjacentGrowthRefutation.exponent_eq_half)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ k => exponent k 4) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.CoonsAdjacentGrowthRefutation.exponent_eq_half.__information_unit,
  realizationName := `Reg.D5.S1.Digit.CoonsAdjacentGrowthRefutation.exponent_eq_half.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ k => exponent k 4) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.CoonsAdjacentGrowthRefutation, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end exponent_eq_half

end
end Reg.D5.S1.Digit.CoonsAdjacentGrowthRefutation
