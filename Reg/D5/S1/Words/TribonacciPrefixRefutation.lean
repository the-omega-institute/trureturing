import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.TribonacciPrefixRefutation
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.TribonacciPrefixRefutation
open _root_.D5.S1.Words.TribonacciPrefixRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open _root_.D5.S1.Words.TribonacciAlignedWindows
open _root_.D5.S1.Words.RankOneMorphismIterationBound (image)
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor)

namespace FourOdd
abbrev signature : Signature where
  Params := ℕ
  State _ := Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n x => (image sigma (4*n) x).length) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (x : Letter), Odd (R.readout () n x)
private theorem actual_law : arena.Law actual := by
  exact four_odd
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  norm_num [rejected, realize] at hh
private theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i
private theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 0, 1, ?_⟩
  change (image sigma 4 0).length ≠ (image sigma 4 1).length
  decide
def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S1.Words.TribonacciPrefixRefutation.four_odd)
    (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.TribonacciPrefixRefutation.four_odd.__information_unit
  realizationName := `Reg.D5.S1.Words.TribonacciPrefixRefutation.FourOdd.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n x => (image sigma (4*n) x).length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.TribonacciPrefixRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FourOdd

namespace ClosedCharge
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => prefixCharge n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n = 1 - (-1 : ℤ)^n * ((n:ℤ)^2 + 3*(n:ℤ) + 1)
private theorem actual_law : arena.Law actual := by
  exact prefixCharge_closed
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1
  norm_num [rejected, realize] at hh
private theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i
private theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change prefixCharge 0 ≠ prefixCharge 1
  rw [prefixCharge_closed, prefixCharge_closed]
  norm_num
def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S1.Words.TribonacciPrefixRefutation.prefixCharge_closed)
    (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.TribonacciPrefixRefutation.prefixCharge_closed.__information_unit
  realizationName := `Reg.D5.S1.Words.TribonacciPrefixRefutation.ClosedCharge.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => prefixCharge n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.TribonacciPrefixRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ClosedCharge

namespace ActualPrefix
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List Letter
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => prefixWord n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, factor W 0 (prefixLength n) = R.readout () () n
private theorem actual_law : arena.Law actual := by
  exact prefixWord_actual
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1
  change factor W 0 (prefixLength 1) = [] at hh
  rw [prefixWord_actual] at hh
  have hn : prefixWord 1 ≠ [] := by decide
  exact hn hh
private theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i
private theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change prefixWord 0 ≠ prefixWord 1
  decide
def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S1.Words.TribonacciPrefixRefutation.prefixWord_actual)
    (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.TribonacciPrefixRefutation.prefixWord_actual.__information_unit
  realizationName := `Reg.D5.S1.Words.TribonacciPrefixRefutation.ActualPrefix.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => prefixWord n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.TribonacciPrefixRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ActualPrefix

end
end Reg.D5.S1.Words.TribonacciPrefixRefutation


open _root_.D5.S1.Words.TribonacciPrefixRefutation (a b c)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.TribonacciPrefixRefutation.abc_closed
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ n => (-1 : ℤ)^n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    a n = 2 ∧ b n = 2 - R.readout () () n ∧ c n = 2 - (2*(n : ℤ)+2)*(-1 : ℤ)^n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0).2.1
  change (1 : ℤ) = 2 - 0 at hh
  norm_num at hh

def family : Registration arena
    (type_of% (@_root_.D5.S1.Words.TribonacciPrefixRefutation.abc_closed)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.TribonacciPrefixRefutation.abc_closed,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (1 : ℤ) ≠ -1
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.TribonacciPrefixRefutation.abc_closed)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.TribonacciPrefixRefutation.abc_closed.__information_unit,
  realizationName := `Reg.D5.S1.Words.TribonacciPrefixRefutation.abc_closed.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.TribonacciPrefixRefutation, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "arg", "fn", "arg", "arg", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Reg.D5.S1.Words.TribonacciPrefixRefutation.abc_closed
