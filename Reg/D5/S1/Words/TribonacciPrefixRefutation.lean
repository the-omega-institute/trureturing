import D5.S1.Words.TribonacciPrefixRefutation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

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
