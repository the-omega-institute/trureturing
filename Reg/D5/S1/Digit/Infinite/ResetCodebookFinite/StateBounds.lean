import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookFinite
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.execute_bounds
abbrev signature : Signature where
  Params := Σ _ : Bool, List Return
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (low : Bool) (as : List Return) (D : ℝ),
  0 ≤ D → D ≤ h low → 0 ≤ execute low as D ∧ execute low as D ≤ h low
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (low : Bool) (as : List Return) (D : ℝ),
  0 ≤ D → D ≤ h low → 0 ≤ R.readout () ⟨low,as⟩ D ∧ execute low as D ≤ h low
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := (hh false [] 0 le_rfl (parameters false).2.2.2.2.1.le).1
  change (0 : ℝ) ≤ -1 at hb
  norm_num at hb
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.execute_bounds,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨false,[]⟩,(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize,execute]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.execute_bounds)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.execute_bounds.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.execute_bounds.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.execute_bounds

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.execute_floor
abbrev signature : Signature where
  Params := Σ _ : Bool, List Return
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p _ => A p.1 - 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (low : Bool) (as : List Return) (D : ℝ),
  A low ≤ D → D ≤ h low → A low ≤ execute low as D
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (low : Bool) (as : List Return) (D : ℝ),
  A low ≤ D → D ≤ h low → A low ≤ R.readout () ⟨low,as⟩ D
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hp := parameters false
  have hA : A false ≤ h false := by
    unfold A
    nlinarith [hp.1,hp.2.2.2.2.1]
  have hb := hh false [] (A false) le_rfl hA
  change A false ≤ A false - 1 at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.execute_floor,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨false,[]⟩,(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize,execute]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.execute_floor)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.execute_floor.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.execute_floor.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.execute_floor

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.run_bounds
abbrev signature : Signature where
  Params := Σ _ : Bool, Return
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p D => run p.1 p.2 D) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (low : Bool) (a : Return) (D : ℝ), 0 ≤ D → D ≤ h low →
  0 ≤ run low a D ∧ run low a D ≤ h low
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (low : Bool) (a : Return) (D : ℝ), 0 ≤ D → D ≤ h low →
  0 ≤ R.readout () ⟨low,a⟩ D ∧ run low a D ≤ h low
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := (hh false ⟨⟨1,1⟩,by decide⟩ 0 le_rfl (parameters false).2.2.2.2.1.le).1
  change (0 : ℝ) ≤ -1 at hb
  norm_num at hb
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.run_bounds,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨false,⟨⟨1,1⟩,by decide⟩⟩,(0 : ℝ),(1 : ℝ),?_⟩
    change run false ⟨⟨1,1⟩,by decide⟩ 0 ≠ run false ⟨⟨1,1⟩,by decide⟩ 1
    simp only [run,Function.iterate_one,pow_one,step,mul_zero,add_zero,mul_one]
    have hp := mul_pos (parameters false).1 (parameters false).2.2.1
    intro he
    linarith
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.run_bounds)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p D => run p.1 p.2 D) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.run_bounds.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.run_bounds.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p D => run p.1 p.2 D) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.run_bounds

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.run_closed
abbrev signature : Signature where
  Params := Σ _ : Bool, Return
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p D => run p.1 p.2 D) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p D => run p.1 p.2 D + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (low : Bool) (a : Return) (D : ℝ),
  run low a D = closedRun low a.val.1 a.val.2 D
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (low : Bool) (a : Return) (D : ℝ),
  R.readout () ⟨low,a⟩ D = closedRun low a.val.1 a.val.2 D
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := hh false ⟨⟨1,1⟩,by decide⟩ 0
  change run false ⟨⟨1,1⟩,by decide⟩ 0 + 1 = _ at hb
  have hrun := _root_.D5.S1.Digit.Infinite.ResetCodebook.run_closed
    false (⟨⟨1,1⟩,by decide⟩ : Return) 0
  rw [hrun] at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.run_closed,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨false,⟨⟨1,1⟩,by decide⟩⟩,(0 : ℝ),(1 : ℝ),?_⟩
    change run false ⟨⟨1,1⟩,by decide⟩ 0 ≠ run false ⟨⟨1,1⟩,by decide⟩ 1
    simp only [run,Function.iterate_one,pow_one,step,mul_zero,add_zero,mul_one]
    have hp := mul_pos (parameters false).1 (parameters false).2.2.1
    intro he
    linarith
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.run_closed)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p D => run p.1 p.2 D) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.run_closed.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.run_closed.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p D => run p.1 p.2 D) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.run_closed

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ResetLifts
abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ M z => closedRun false M 1 z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ M _ => Statement.B M - 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (M : ℕ) (z : ℝ), A false ≤ z → Statement.B M ≤ closedRun false M 1 z
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : ℕ) (z : ℝ), A false ≤ z → Statement.B M ≤ R.readout () M z
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hb := hh 0 (A false) le_rfl
  change Statement.B 0 ≤ Statement.B 0 - 1 at hb
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.reset_lifts,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(0 : ℕ),(0 : ℝ),(1 : ℝ),?_⟩
    change closedRun false 0 1 0 ≠ closedRun false 0 1 1
    simp only [closedRun,pow_zero,pow_one,one_mul,mul_zero,mul_one,sub_sub_cancel]
    exact (ne_of_gt (parameters false).2.2.1).symm
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.reset_lifts)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ M z => closedRun false M 1 z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.reset_lifts.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ResetLifts.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ M z => closedRun false M 1 z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ResetLifts

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.WeakRun
abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℝ, Σ _ : Return, List Return
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p D => Statement.weak p.1 p.2.1 (p.2.2.1::p.2.2.2) D) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (K : ℕ) (d : ℝ) (a : Return) (as : List Return) (D : ℝ),
  Statement.weak K d (a::as) D ↔
    a.val.2 ≤ K ∧ (a.val.2=K → d ≤ D) ∧ Statement.weak K d as (run false a D)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℕ) (d : ℝ) (a : Return) (as : List Return) (D : ℝ),
  R.readout () ⟨K,d,a,as⟩ D ↔
    a.val.2 ≤ K ∧ (a.val.2=K → d ≤ D) ∧ Statement.weak K d as (run false a D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  apply (hh 1 0 ⟨⟨1,1⟩,by decide⟩ [] 0).mpr
  exact ⟨le_rfl,fun _ => le_rfl,trivial⟩
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.weak_run,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let a : Return := ⟨⟨1,1⟩,by decide⟩
    refine ⟨⟨1,0,a,[]⟩,(0 : ℝ),(-1 : ℝ),?_⟩
    intro he
    have hp : actual.readout i ⟨1,0,a,[]⟩ 0 := by
      change Statement.weak 1 0 [a] 0
      simp [Statement.weak,a]
    have hb := Eq.mp he hp
    change Statement.weak 1 0 [a] (-1) at hb
    norm_num [Statement.weak,a] at hb
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.weak_run)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p D => Statement.weak p.1 p.2.1 (p.2.2.1::p.2.2.2) D) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.weak_run.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.WeakRun.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p D => Statement.weak p.1 p.2.1 (p.2.2.1::p.2.2.2) D) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.WeakRun
