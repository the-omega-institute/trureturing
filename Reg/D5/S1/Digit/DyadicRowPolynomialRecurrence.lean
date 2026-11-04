import D5.S1.Digit.DyadicRowPolynomialRecurrence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open D5.S1.Digit.DyadicRowPolynomialRecurrence (wt wt_zero wt_even wt_odd)
namespace Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ n => wt n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => wt n + 1) (fun e => nomatch e)

abbrev zeroArena : Arena where
  signature := signature
  Law R := R.readout () () 0 = 0
theorem zero_rejected : ¬ zeroArena.Law rejected := by
  intro h
  change wt 0 + 1 = 0 at h
  omega

def zeroRegistration : Registration zeroArena (zeroArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨wt_zero, rejected, zero_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, zero_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change wt 0 ≠ wt 1
    have hw : wt 1 = wt 0 + 1 := by simpa using wt_odd 0
    omega

noncomputable def registration_zero : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.DyadicRowPolynomialRecurrence.wt_zero)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => wt n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := .str (.str `D5.S1.Digit.DyadicRowPolynomialRecurrence.wt_zero "Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence/Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence.zeroArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence.zeroRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨zeroArena⟩
  objectArena := .source ⟨zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zeroArena ⟨zeroRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => wt n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S1.Digit.DyadicRowPolynomialRecurrence, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

abbrev evenArena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (2 * n) = wt n
theorem even_rejected : ¬ evenArena.Law rejected := by
  intro h
  have hh := h 0
  change wt (2 * 0) + 1 = wt 0 at hh
  rw [wt_even] at hh
  omega

def evenRegistration : Registration evenArena (evenArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨wt_even, rejected, even_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, even_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change wt 0 ≠ wt 1
    have hw : wt 1 = wt 0 + 1 := by simpa using wt_odd 0
    omega

noncomputable def registration_even : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.DyadicRowPolynomialRecurrence.wt_even)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => wt n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := .str (.str `D5.S1.Digit.DyadicRowPolynomialRecurrence.wt_even "Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence/Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence.evenArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence.evenRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨evenArena⟩
  objectArena := .source ⟨evenArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source evenArena ⟨evenRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => wt n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S1.Digit.DyadicRowPolynomialRecurrence, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

abbrev oddArena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (2 * n + 1) = wt n + 1
theorem odd_rejected : ¬ oddArena.Law rejected := by
  intro h
  have hh := h 0
  change wt (2 * 0 + 1) + 1 = wt 0 + 1 at hh
  rw [wt_odd] at hh
  omega

def oddRegistration : Registration oddArena (oddArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨wt_odd, rejected, odd_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, odd_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change wt 0 ≠ wt 1
    have hw : wt 1 = wt 0 + 1 := by simpa using wt_odd 0
    omega

noncomputable def registration_odd : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.DyadicRowPolynomialRecurrence.wt_odd)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => wt n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := .str (.str `D5.S1.Digit.DyadicRowPolynomialRecurrence.wt_odd "Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence/Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence.oddArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence.oddRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨oddArena⟩
  objectArena := .source ⟨oddArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source oddArena ⟨oddRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => wt n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S1.Digit.DyadicRowPolynomialRecurrence, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S1.Digit.DyadicRowPolynomialRecurrence
