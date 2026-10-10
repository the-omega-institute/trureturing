import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookOrder
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_10
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 10) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 10) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 10) x = ((3/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^10*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((3/10 : ℝ) + (3/10 : ℝ)*g) + (-g)^10*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 10) 0 + 1 = _ at hb
  rw [C_scalar_10 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_10,rejected,rejected_law⟩
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
    change wordScalar (C.drop 10) 0 ≠ wordScalar (C.drop 10) 1
    rw [wordScalar_affine (C.drop 10) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 10).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_10)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 10) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_10.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_10.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 10) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_10

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_11
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 11) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 11) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 11) x = ((0 : ℝ) + (1/5 : ℝ)*g) + (-g)^9*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((0 : ℝ) + (1/5 : ℝ)*g) + (-g)^9*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 11) 0 + 1 = _ at hb
  rw [C_scalar_11 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_11,rejected,rejected_law⟩
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
    change wordScalar (C.drop 11) 0 ≠ wordScalar (C.drop 11) 1
    rw [wordScalar_affine (C.drop 11) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 11).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_11)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 11) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_11.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_11.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 11) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_11

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_12
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 12) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 12) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 12) x = ((-1/5 : ℝ) + (0 : ℝ)*g) + (-g)^8*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-1/5 : ℝ) + (0 : ℝ)*g) + (-g)^8*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 12) 0 + 1 = _ at hb
  rw [C_scalar_12 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_12,rejected,rejected_law⟩
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
    change wordScalar (C.drop 12) 0 ≠ wordScalar (C.drop 12) 1
    rw [wordScalar_affine (C.drop 12) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 12).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_12)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 12) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_12.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_12.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 12) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_12

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_13
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 13) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 13) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 13) x = ((4/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^7*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((4/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^7*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 13) 0 + 1 = _ at hb
  rw [C_scalar_13 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_13,rejected,rejected_law⟩
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
    change wordScalar (C.drop 13) 0 ≠ wordScalar (C.drop 13) 1
    rw [wordScalar_affine (C.drop 13) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 13).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_13)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 13) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_13.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_13.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 13) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_13

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_14
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 14) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 14) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 14) x = ((3/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^6*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((3/5 : ℝ) + (1/5 : ℝ)*g) + (-g)^6*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 14) 0 + 1 = _ at hb
  rw [C_scalar_14 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_14,rejected,rejected_law⟩
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
    change wordScalar (C.drop 14) 0 ≠ wordScalar (C.drop 14) 1
    rw [wordScalar_affine (C.drop 14) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 14).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_14)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 14) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_14.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_14.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 14) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_14

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_15
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 15) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 15) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 15) x = ((7/5 : ℝ) + (2/5 : ℝ)*g) + (-g)^5*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((7/5 : ℝ) + (2/5 : ℝ)*g) + (-g)^5*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 15) 0 + 1 = _ at hb
  rw [C_scalar_15 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_15,rejected,rejected_law⟩
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
    change wordScalar (C.drop 15) 0 ≠ wordScalar (C.drop 15) 1
    rw [wordScalar_affine (C.drop 15) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 15).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_15)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 15) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_15.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_15.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 15) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_15

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_16
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 16) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 16) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 16) x = ((-1/2 : ℝ) + (1/10 : ℝ)*g) + (-g)^4*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-1/2 : ℝ) + (1/10 : ℝ)*g) + (-g)^4*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 16) 0 + 1 = _ at hb
  rw [C_scalar_16 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_16,rejected,rejected_law⟩
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
    change wordScalar (C.drop 16) 0 ≠ wordScalar (C.drop 16) 1
    rw [wordScalar_affine (C.drop 16) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 16).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_16)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 16) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_16.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_16.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 16) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_16

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_17
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 17) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 17) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 17) x = ((-3/5 : ℝ) + (0 : ℝ)*g) + (-g)^3*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-3/5 : ℝ) + (0 : ℝ)*g) + (-g)^3*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 17) 0 + 1 = _ at hb
  rw [C_scalar_17 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_17,rejected,rejected_law⟩
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
    change wordScalar (C.drop 17) 0 ≠ wordScalar (C.drop 17) 1
    rw [wordScalar_affine (C.drop 17) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 17).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_17)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 17) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_17.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_17.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 17) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_17

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_18
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 18) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 18) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 18) x = ((-1/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^2*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-1/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^2*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 18) 0 + 1 = _ at hb
  rw [C_scalar_18 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_18,rejected,rejected_law⟩
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
    change wordScalar (C.drop 18) 0 ≠ wordScalar (C.drop 18) 1
    rw [wordScalar_affine (C.drop 18) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 18).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_18)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 18) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_18.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_18.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 18) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_18

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_19
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 19) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (C.drop 19) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (C.drop 19) x = ((3/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((3/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (C.drop 19) 0 + 1 = _ at hb
  rw [C_scalar_19 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_19,rejected,rejected_law⟩
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
    change wordScalar (C.drop 19) 0 ≠ wordScalar (C.drop 19) 1
    rw [wordScalar_affine (C.drop 19) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (C.drop 19).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_scalar_19)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 19) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_scalar_19.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_19.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (C.drop 19) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.C_scalar_19
