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

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_0
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 0) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (V.drop 0) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (V.drop 0) x = ((-342/5 : ℝ) + (1451/5 : ℝ)*g) + (-g)^6*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-342/5 : ℝ) + (1451/5 : ℝ)*g) + (-g)^6*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (V.drop 0) 0 + 1 = _ at hb
  rw [V_scalar_0 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_0,rejected,rejected_law⟩
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
    change wordScalar (V.drop 0) 0 ≠ wordScalar (V.drop 0) 1
    rw [wordScalar_affine (V.drop 0) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (V.drop 0).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_0)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 0) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.V_scalar_0.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_0.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 0) x) (fun e => nomatch e)),
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
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_0

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_1
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 1) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (V.drop 1) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (V.drop 1) x = ((-83/5 : ℝ) + (342/5 : ℝ)*g) + (-g)^5*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-83/5 : ℝ) + (342/5 : ℝ)*g) + (-g)^5*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (V.drop 1) 0 + 1 = _ at hb
  rw [V_scalar_1 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_1,rejected,rejected_law⟩
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
    change wordScalar (V.drop 1) 0 ≠ wordScalar (V.drop 1) 1
    rw [wordScalar_affine (V.drop 1) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (V.drop 1).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_1)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 1) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.V_scalar_1.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_1.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 1) x) (fun e => nomatch e)),
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
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_1

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_2
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 2) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (V.drop 2) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (V.drop 2) x = ((-9/2 : ℝ) + (161/10 : ℝ)*g) + (-g)^4*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-9/2 : ℝ) + (161/10 : ℝ)*g) + (-g)^4*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (V.drop 2) 0 + 1 = _ at hb
  rw [V_scalar_2 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_2,rejected,rejected_law⟩
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
    change wordScalar (V.drop 2) 0 ≠ wordScalar (V.drop 2) 1
    rw [wordScalar_affine (V.drop 2) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (V.drop 2).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_2)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 2) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.V_scalar_2.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_2.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 2) x) (fun e => nomatch e)),
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
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_2

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_3
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 3) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (V.drop 3) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (V.drop 3) x = ((-3/5 : ℝ) + (4 : ℝ)*g) + (-g)^3*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-3/5 : ℝ) + (4 : ℝ)*g) + (-g)^3*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (V.drop 3) 0 + 1 = _ at hb
  rw [V_scalar_3 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_3,rejected,rejected_law⟩
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
    change wordScalar (V.drop 3) 0 ≠ wordScalar (V.drop 3) 1
    rw [wordScalar_affine (V.drop 3) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (V.drop 3).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_3)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 3) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.V_scalar_3.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_3.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 3) x) (fun e => nomatch e)),
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
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_3

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_4
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 4) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (V.drop 4) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (V.drop 4) x = ((-1/10 : ℝ) + (11/10 : ℝ)*g) + (-g)^2*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-1/10 : ℝ) + (11/10 : ℝ)*g) + (-g)^2*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (V.drop 4) 0 + 1 = _ at hb
  rw [V_scalar_4 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_4,rejected,rejected_law⟩
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
    change wordScalar (V.drop 4) 0 ≠ wordScalar (V.drop 4) 1
    rw [wordScalar_affine (V.drop 4) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (V.drop 4).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_4)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 4) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.V_scalar_4.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_4.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 4) x) (fun e => nomatch e)),
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
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_4

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_5
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 5) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => wordScalar (V.drop 5) x + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ x : ℝ, wordScalar (V.drop 5) x = ((-7/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () x = ((-7/10 : ℝ) + (1/10 : ℝ)*g) + (-g)^1*(x-c0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change wordScalar (V.drop 5) 0 + 1 = _ at hb
  rw [V_scalar_5 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_5,rejected,rejected_law⟩
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
    change wordScalar (V.drop 5) 0 ≠ wordScalar (V.drop 5) 1
    rw [wordScalar_affine (V.drop 5) 1]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp := pow_ne_zero (V.drop 5).length (neg_ne_zero.mpr hg)
    simpa only [mul_one, ne_eq, left_eq_add, eq_comm] using hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.V_scalar_5)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 5) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.V_scalar_5.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_5.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => wordScalar (V.drop 5) x) (fun e => nomatch e)),
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
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_scalar_5
