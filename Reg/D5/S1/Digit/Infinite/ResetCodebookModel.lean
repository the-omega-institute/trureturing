import Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookModel
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookModel.Center
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => (1+x)/5) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => c0+1) (fun e => nomatch e)
def sourceStatement : Prop := c0 = (1+g)/5
abbrev arena : Arena where
  signature := signature
  Law R := c0 = R.readout () () g
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change c0 = c0+1 at h
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.center,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.center)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => (1+x)/5) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.center.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookModel.Center.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => (1+x)/5) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookModel, definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "arg", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookModel.Center

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookModel.LiteralTail
abbrev signature : Signature where
  Params := Bool
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ low x => wordScalar (tailWord low) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ low x => wordScalar (tailWord low) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ low : Bool, stateAddress true (literalTail low) ∧ finiteTail (literalTail low) ∧
  addressPrefix (tailWord low) (literalTail low) zeroAddress ∧
  kappa (literalTail low) = wordScalar (tailWord low) 0
abbrev arena : Arena where
  signature := signature
  Law R := ∀ low : Bool, stateAddress true (literalTail low) ∧ finiteTail (literalTail low) ∧
  addressPrefix (tailWord low) (literalTail low) zeroAddress ∧
  kappa (literalTail low) = R.readout () low 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h false).2.2.2
  change kappa (literalTail false) = wordScalar (tailWord false) 0 + 1 at hb
  have ht := (literal_tail_spec false).2.2.2
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.literal_tail_spec,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨false,(0 : ℝ),(1 : ℝ),?_⟩
    change wordScalar (tailWord false) 0 ≠ wordScalar (tailWord false) 1
    rw [wordScalar_affine (tailWord false) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (tailWord false).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.literal_tail_spec)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ low x => wordScalar (tailWord low) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.literal_tail_spec.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookModel.LiteralTail.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ low x => wordScalar (tailWord low) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookModel, definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookModel.LiteralTail

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookModel.ActualPair
abbrev signature : Signature where
  Params := Unit
  State _ := List Label
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LegalDigits → LegalDigits → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ w x y => addressPrefix w x y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (anchor : Bool) (exec : List Return), ∃ src : Bool → LegalDigits, ∀ low,
  stateAddress false (src low) ∧ finiteTail (src low) ∧
  addressPrefix (sourcePrefix low anchor exec) (src low) (literalTail low) ∧
  kappa (src low) = wordScalar (sourcePrefix low anchor exec) (kappa (literalTail low))
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (anchor : Bool) (exec : List Return), ∃ src : Bool → LegalDigits, ∀ low,
  stateAddress false (src low) ∧ finiteTail (src low) ∧
  R.readout () () (sourcePrefix low anchor exec) (src low) (literalTail low) ∧
  kappa (src low) = wordScalar (sourcePrefix low anchor exec) (kappa (literalTail low))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨src,hs⟩ := h false []
  exact (hs false).2.2.1
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.actual_pair,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(),[],sourcePrefix false false [],?_⟩
    intro he
    have hp : addressPrefix (sourcePrefix false false []) zeroAddress zeroAddress :=
      Eq.mp (congrFun (congrFun he zeroAddress) zeroAddress) rfl
    have hw : window zeroAddress 0 = fiveLabel := hp.1
    have hh := congrArg (fun l : Label => l.val ⟨2,by decide⟩) hw
    change false = true at hh
    cases hh
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.actual_pair)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ w x y => addressPrefix w x y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.actual_pair.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookModel.ActualPair.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ w x y => addressPrefix w x y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookModel, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookModel.ActualPair
