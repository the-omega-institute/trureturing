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

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.Lambda
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => (1-x)/20) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => lambda+1) (fun e => nomatch e)
def sourceStatement : Prop := lambda = (1-g)/20
abbrev arena : Arena where
  signature := signature
  Law R := lambda = R.readout () () g
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  change lambda = lambda+1 at hh
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.lambda_linear,rejected,rejected_law⟩
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
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.lambda_linear)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => (1-x)/20) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.lambda_linear.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.Lambda.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => (1-x)/20) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
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
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.Lambda

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.GTight
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => 236067/1000000 < x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := 236067/1000000 < g ∧ g < 236068/1000000
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () g ∧ g < 236068/1000000
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh.1
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.g_tight,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(),(1 : ℝ),(0 : ℝ),?_⟩
    intro he
    have hb := Eq.mp he (show actual.readout i () 1 from by norm_num [actual,realize])
    norm_num [actual,realize] at hb
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.g_tight)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => 236067/1000000 < x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.g_tight.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.GTight.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => 236067/1000000 < x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.GTight

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.U_map
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ D => wordScalar U (coord false D)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ D => wordScalar U (coord false D)+1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ D : ℝ, wordScalar U (coord false D) = coord false (A false+rho*D)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ D : ℝ, R.readout () () D = coord false (A false+rho*D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := hh 0
  change wordScalar U (coord false 0)+1 = _ at hb
  rw [U_map 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.U_map,rejected,rejected_law⟩
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
    change wordScalar U (coord false 0) ≠ wordScalar U (coord false 1)
    rw [U_map 0,U_map 1]
    simp only [coord,Bool.false_eq_true,if_false,if_true,mul_zero,add_zero,mul_one]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp : rho ≠ 0 := pow_ne_zero 6 hg
    intro he
    apply hp
    linarith
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.U_map)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ D => wordScalar U (coord false D)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.U_map.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.U_map.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ D => wordScalar U (coord false D)) (fun e => nomatch e)),
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
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.U_map

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_map
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ D => wordScalar V (coord true D)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ D => wordScalar V (coord true D)+1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ D : ℝ, wordScalar V (coord true D) = coord true (A true+rho*D)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ D : ℝ, R.readout () () D = coord true (A true+rho*D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := hh 0
  change wordScalar V (coord true 0)+1 = _ at hb
  rw [V_map 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.V_map,rejected,rejected_law⟩
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
    change wordScalar V (coord true 0) ≠ wordScalar V (coord true 1)
    rw [V_map 0,V_map 1]
    simp only [coord,Bool.false_eq_true,if_false,if_true,mul_zero,add_zero,mul_one]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp : rho ≠ 0 := pow_ne_zero 6 hg
    intro he
    apply hp
    linarith
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.V_map)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ D => wordScalar V (coord true D)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.V_map.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_map.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ D => wordScalar V (coord true D)) (fun e => nomatch e)),
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
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.V_map

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.CMap
abbrev signature : Signature where
  Params := Bool
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ low D => wordScalar C (coord low D)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ low D => wordScalar C (coord low D)+1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (low : Bool) (D : ℝ), wordScalar C (coord low D) = coord low (chi*D)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (low : Bool) (D : ℝ), R.readout () low D = coord low (chi*D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := hh false 0
  change wordScalar C (coord false 0)+1 = _ at hb
  rw [C_map false 0] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.C_map,rejected,rejected_law⟩
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
    change wordScalar C (coord false 0) ≠ wordScalar C (coord false 1)
    rw [C_map false 0,C_map false 1]
    simp only [coord,Bool.false_eq_true,if_false,mul_zero,mul_one,add_zero]
    have hg : g ≠ 0 := ne_of_gt (lt_trans (by norm_num) SixWindowForcing.algebra.2.1)
    have hp : chi ≠ 0 := pow_ne_zero 20 hg
    intro he
    apply hp
    linarith
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_map)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ low D => wordScalar C (coord low D)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_map.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.CMap.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ low D => wordScalar C (coord low D)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.CMap
