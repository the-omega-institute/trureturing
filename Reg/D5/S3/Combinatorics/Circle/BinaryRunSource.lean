import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.BinaryRunSource
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.BinaryRunSource
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ExpandingSourcePath

/-! Whole-source dependent-family audits for the physical binary run bridge. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Combinatorics.Circle.BinaryRunSource

namespace recurrence_wordValue
abbrev signature : Signature where
  Params := Σ k : ℕ, Fin k → Bool
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => wordValue p.2 a) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} (hk : 0 < k) (u : Fin k → ℕ) (c : Fin k → Bool) (a : Fin k)
    (hrec : ∀ i, (u (finRotate k i) : ℤ) =
      2 * (u i : ℤ) - ((2 ^ k - 1 : ℕ) : ℤ) * (c i).toNat),
    R.readout () ⟨k, c⟩ a = u a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (k := 1) (by decide) (fun _ => 1) (fun _ => true) 0
    (by intro i; norm_num)
  change (0 : ℕ) = 1 at hh
  omega
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨⟨2, fun i => decide (i.val = 1)⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩
  change wordValue (fun i : Fin 2 => decide (i.val = 1)) (0 : Fin 2) ≠
    wordValue (fun i : Fin 2 => decide (i.val = 1)) (1 : Fin 2)
  norm_num [wordValue, lsbDigit, forwardDigit, finCycle_apply,
    Fin.sum_univ_two, Fin.rev, Fin.val_add]
def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.recurrence_wordValue)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.recurrence_wordValue,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.recurrence_wordValue)
    (type_of% (realize signature (fun _ p a => wordValue p.2 a) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.BinaryRunSource.recurrence_wordValue.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.BinaryRunSource.recurrence_wordValue.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => wordValue p.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.BinaryRunSource
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
end recurrence_wordValue

namespace binaryRunTops_separated
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => binaryRunTops e) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => {0, 1}) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {e a b : ℕ} (ha : a ∈ R.readout () () e)
    (hb : b ∈ R.readout () () e) (hab : a < b), a + 1 < b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (e := 0) (a := 0) (b := 1)
    (by simp [rejected, realize]) (by simp [rejected, realize]) (by decide)
  omega
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨(), 0, 1, ?_⟩
  change binaryRunTops 0 ≠ binaryRunTops 1
  decide
def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.binaryRunTops_separated)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.binaryRunTops_separated,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.binaryRunTops_separated)
    (type_of% (realize signature (fun _ _ e => binaryRunTops e) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.BinaryRunSource.binaryRunTops_separated.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.BinaryRunSource.binaryRunTops_separated.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => binaryRunTops e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.BinaryRunSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
end binaryRunTops_separated

namespace separated_run_bound
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => binaryRunCount e) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ e => e + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ e : ℕ, 4 ^ R.readout () () e ≤ 3 * e + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected, realize] at hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨(), 0, 1, ?_⟩
  change binaryRunCount 0 ≠ binaryRunCount 1
  decide
def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.separated_run_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.separated_run_bound,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.separated_run_bound)
    (type_of% (realize signature (fun _ _ e => binaryRunCount e) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.BinaryRunSource.separated_run_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.BinaryRunSource.separated_run_bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => binaryRunCount e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.BinaryRunSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
end separated_run_bound

namespace cyclic_binary_run_bound
abbrev signature : Signature where
  Params := ℕ
  State p := Fin p → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ c => physicalRunCount c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} (hk : 2 ≤ k) (u : Fin k → ℕ) (c : Fin k → Bool)
    (hrec : ∀ i, (u (finRotate k i) : ℤ) =
      2 * (u i : ℤ) - ((2 ^ k - 1 : ℕ) : ℤ) * (c i).toNat)
    (a : Fin k) (e : ℕ) (ha : u a = 4 * e + 1)
    (hhalf : u a < 2 ^ (k - 1)),
    R.readout () k c = binaryRunCount e + 1 ∧
      4 ^ (R.readout () k c - 1) ≤ 3 * e + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr : ∀ i : Fin 6, (nativeUnsigned 6 42 (finRotate 6 i) : ℤ) =
      2 * (nativeUnsigned 6 42 i : ℤ) -
        ((2 ^ 6 - 1 : ℕ) : ℤ) * (nativeCarry 6 42 i).toNat := by
    intro i
    fin_cases i <;> norm_num [nativeUnsigned, nativeCarry, actualSource,
      centered, modulus, finRotate_apply, Fin.val_add]
  have hh := (h (k := 6) (by decide) (nativeUnsigned 6 42) (nativeCarry 6 42)
    hr ⟨0, by decide⟩ 5
    (by norm_num [nativeUnsigned, actualSource, centered, modulus])
    (by norm_num [nativeUnsigned, actualSource, centered, modulus])).1
  change 0 = binaryRunCount 5 + 1 at hh
  omega
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨6, (fun _ => false), nativeCarry 6 42, ?_⟩
  change physicalRunCount (fun _ : Fin 6 => false) ≠ physicalRunCount (nativeCarry 6 42)
  rw [actualSource_runCount_eq (by decide)]
  have hc : actualNegativeLargeCount 6 42 = 3 := by decide
  rw [hc]
  have hz : physicalRunCount (fun _ : Fin 6 => false) = 0 := by
    classical
    have hf : Finset.univ.filter (falseTrueEdge (fun _ : Fin 6 => false)) = ∅ := by
      ext i
      simp [falseTrueEdge]
    rw [physicalRunCount, hf]
    rfl
  omega
def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.cyclic_binary_run_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.cyclic_binary_run_bound,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.cyclic_binary_run_bound)
    (type_of% (realize signature (fun _ _ c => physicalRunCount c) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.BinaryRunSource.cyclic_binary_run_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.BinaryRunSource.cyclic_binary_run_bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => physicalRunCount c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.BinaryRunSource
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
end cyclic_binary_run_bound

namespace actualSource_falseTrueEdge_iff
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => actualSource p.1 p.2 i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k t : ℕ} (hk : 3 ≤ k) (i : Fin k),
    falseTrueEdge (nativeCarry k t) i ↔ R.readout () ⟨k, t⟩ i ≤ -quarter k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : falseTrueEdge (nativeCarry 6 42) ⟨0, by decide⟩ :=
    (actualSource_falseTrueEdge_iff (by decide) _).mpr
      (by norm_num [actualSource, centered, modulus, quarter])
  have hh := (h (k := 6) (t := 42) (by decide) ⟨0, by decide⟩).mp he
  norm_num [rejected, realize, quarter] at hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨⟨6, 42⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩
  norm_num [actual, realize, actualSource, centered, modulus]
def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_falseTrueEdge_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_falseTrueEdge_iff,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_falseTrueEdge_iff)
    (type_of% (realize signature (fun _ p i => actualSource p.1 p.2 i) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_falseTrueEdge_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_falseTrueEdge_iff.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p i => actualSource p.1 p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.BinaryRunSource
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
end actualSource_falseTrueEdge_iff

namespace actualSource_runCount_eq
abbrev signature : Signature where
  Params := ℕ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualNegativeLargeCount k t) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k t : ℕ} (hk : 3 ≤ k),
    physicalRunCount (nativeCarry k t) = R.readout () k t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (k := 6) (t := 42) (by decide)
  rw [actualSource_runCount_eq (by decide)] at hh
  change actualNegativeLargeCount 6 42 = 0 at hh
  have hc : actualNegativeLargeCount 6 42 = 3 := by decide
  omega
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨6, 0, 42, ?_⟩
  change actualNegativeLargeCount 6 0 ≠ actualNegativeLargeCount 6 42
  decide
def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_runCount_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_runCount_eq,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_runCount_eq)
    (type_of% (realize signature (fun _ k t => actualNegativeLargeCount k t) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_runCount_eq.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_runCount_eq.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k t => actualNegativeLargeCount k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.BinaryRunSource
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
end actualSource_runCount_eq

namespace actualSource_binary_run_bound
abbrev signature : Signature where
  Params := ℕ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualNegativeLargeCount k t) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k t : ℕ} (hk : 3 ≤ k) (a : Fin k) (e : ℕ)
    (ha : actualSource k t a = -(4 * e + 1)) (hstrict : 3 * e + 1 < quarter k),
    R.readout () k t = binaryRunCount e + 1 ∧
      4 ^ (R.readout () k t - 1) ≤ 3 * e + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (k := 6) (t := 50) (by decide) ⟨0, by decide⟩ 3
    (by norm_num [actualSource, centered, modulus]) (by norm_num [quarter])).1
  change 0 = binaryRunCount 3 + 1 at hh
  omega
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨6, 0, 50, ?_⟩
  change actualNegativeLargeCount 6 0 ≠ actualNegativeLargeCount 6 50
  decide
def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_binary_run_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_binary_run_bound,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_binary_run_bound)
    (type_of% (realize signature (fun _ k t => actualNegativeLargeCount k t) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_binary_run_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.BinaryRunSource.actualSource_binary_run_bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k t => actualNegativeLargeCount k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.BinaryRunSource
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
end actualSource_binary_run_bound

end Reg.D5.S3.Combinatorics.Circle.BinaryRunSource
