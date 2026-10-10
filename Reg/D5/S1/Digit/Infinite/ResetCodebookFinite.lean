import Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ParameterBounds
import Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.StateBounds
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookFinite
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.Memory
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ n => rho^n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (K : ℕ) (height eps : ℝ), 0 < height → 0 < eps →
  ∃ n : ℕ, K ≤ n ∧ height*rho^n < eps
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℕ) (height eps : ℝ), 0 < height → 0 < eps →
  ∃ n : ℕ, K ≤ n ∧ height*R.readout () () n < eps
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n,_,hn⟩ := h 0 1 1 (by norm_num) (by norm_num)
  change (1 : ℝ)*1 < 1 at hn
  norm_num at hn
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.common_memory_cutoff,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(),(0 : ℕ),(1 : ℕ),?_⟩
    change rho^0 ≠ rho^1
    simpa using (ne_of_lt (parameters false).2.1).symm
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.common_memory_cutoff)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => rho^n) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.common_memory_cutoff.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.Memory.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => rho^n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "arg"], stateBinder := 5,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.Memory

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.WeakGain
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → List Return → ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ K d as z => Statement.weak K d as z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (K : ℕ) (d delta x y : ℝ) (as : List Return),
  0 < delta → x+delta ≤ y → Statement.weak K d as x →
  Statement.weak K (d+delta*g^(Statement.weight as)) as y
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℕ) (d delta x y : ℝ) (as : List Return),
  0 < delta → x+delta ≤ y → Statement.weak K d as x →
  R.readout () () K (d+delta*g^(Statement.weight as)) as y
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 1 0 1 [] (by norm_num) (by norm_num) trivial
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.weak_gain,rejected,rejected_law⟩
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
    refine ⟨(),1,0,?_⟩
    intro he
    have hp : Statement.weak 1 0 [a] 0 := by norm_num [Statement.weak,a]
    have hb : Statement.weak 0 0 [a] 0 :=
      Eq.mp (congrFun (congrFun (congrFun he 0) [a]) 0) hp
    norm_num [Statement.weak,a] at hb
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.weak_gain)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ K d as z => Statement.weak K d as z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.weak_gain.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.WeakGain.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ K d as z => Statement.weak K d as z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.WeakGain

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.WeakAppend
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → List Return → ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ K d as z => Statement.weak K d as z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (K : ℕ) (q : ℝ) (as bs : List Return) (z : ℝ),
  Statement.weak K q as z → Statement.weak K q bs (execute false as z) →
  Statement.weak K q (as++bs) z
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℕ) (q : ℝ) (as bs : List Return) (z : ℝ),
  Statement.weak K q as z → Statement.weak K q bs (execute false as z) →
  R.readout () () K q (as++bs) z
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 [] [] 0 trivial trivial
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Infinite.ResetCodebook.weak_append,rejected,rejected_law⟩
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
    refine ⟨(),1,0,?_⟩
    intro he
    have hp : Statement.weak 1 0 [a] 0 := by norm_num [Statement.weak,a]
    have hb : Statement.weak 0 0 [a] 0 :=
      Eq.mp (congrFun (congrFun (congrFun he 0) [a]) 0) hp
    norm_num [Statement.weak,a] at hb
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.weak_append)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ K d as z => Statement.weak K d as z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.weak_append.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.WeakAppend.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ K d as z => Statement.weak K d as z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.WeakAppend
