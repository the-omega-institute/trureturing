import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookWeighted
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Topology
noncomputable section

namespace Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_append
abbrev signature : Signature where
  Params := Σ _ : List Label, List Label
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p x => wordScalar (p.1 ++ p.2) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (u v : List Label) (x : ℝ), wordScalar (u ++ v) x = wordScalar u (wordScalar v x)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v : List Label) (x : ℝ), R.readout () ⟨u,v⟩ x = wordScalar u (wordScalar v x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh [] [] 0
  norm_num [rejected,realize,wordScalar] at he
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_append,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨[],[]⟩,(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize,wordScalar]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_append)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p x => wordScalar (p.1 ++ p.2) x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_append.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_append.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p x => wordScalar (p.1 ++ p.2) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.FixedTailClosedBudget, definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_append

namespace Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_affine
abbrev signature : Signature where
  Params := List Label
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ w x => wordScalar w x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : List Label) (x : ℝ), wordScalar w x = wordScalar w 0 + (-g)^w.length*x
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : List Label) (x : ℝ), R.readout () w x = wordScalar w 0 + (-g)^w.length*x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh [] 0
  norm_num [rejected,realize,wordScalar] at he
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_affine,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨[],(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize,wordScalar]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_affine)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ w x => wordScalar w x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_affine.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_affine.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ w x => wordScalar w x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.FixedTailClosedBudget, definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.wordScalar_affine

namespace Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.prefix_scalar
abbrev signature : Signature where
  Params := List Label
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ w z => wordScalar w z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ z => z + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : List Label) (x y : LegalDigits), addressPrefix w x y → kappa x = wordScalar w (kappa y)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : List Label) (x y : LegalDigits), addressPrefix w x y → kappa x = R.readout () w (kappa y)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh [] zeroAddress zeroAddress rfl
  change kappa zeroAddress = kappa zeroAddress + 1 at he
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.prefix_scalar,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨[],(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize,wordScalar]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.prefix_scalar)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ w z => wordScalar w z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.FixedTailClosedBudget.prefix_scalar.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.prefix_scalar.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ w z => wordScalar w z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.FixedTailClosedBudget, definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.prefix_scalar

namespace Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.path_append
abbrev signature : Signature where
  Params := Σ _ : Bool, Σ _ : List Label, List Label
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p s => SourcePath p.1 (p.2.1 ++ p.2.2) s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {s s' s'' : Bool} {u v : List Label}, SourcePath s u s' → SourcePath s' v s'' → SourcePath s (u ++ v) s''
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s s' s'' : Bool} {u v : List Label}, SourcePath s u s' → SourcePath s' v s'' → R.readout () ⟨s,u,v⟩ s''
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh (SourcePath.nil false) (SourcePath.nil false)
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.path_append,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨false,[],[]⟩,false,true,?_⟩
    intro he
    have hp : SourcePath false [] true := Eq.mp he (SourcePath.nil false)
    cases hp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.path_append)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p s => SourcePath p.1 (p.2.1 ++ p.2.2) s) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.FixedTailClosedBudget.path_append.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.path_append.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p s => SourcePath p.1 (p.2.1 ++ p.2.2) s) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.FixedTailClosedBudget, definition := none, coordinates := #[0, 3, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.path_append

namespace Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_append
abbrev signature : Signature where
  Params := Σ _ : List Label, Σ _ : List Label, Σ _ : List (Fin 6), Σ _ : List (Fin 6), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p z => max (wordCost p.1 p.2.2.1 (wordScalar p.2.1 p.2.2.2.2)) z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (u v : List Label) (r t' : List (Fin 6)), u.length = r.length → ∀ x : ℝ, wordCost (u ++ v) (r ++ t') x = max (wordCost u r (wordScalar v x)) (wordCost v t' x)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v : List Label) (r t' : List (Fin 6)), u.length = r.length → ∀ x : ℝ, wordCost (u ++ v) (r ++ t') x = R.readout () ⟨u,v,r,t',x⟩ (wordCost v t' x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh [] [] [] [] rfl 0
  norm_num [rejected,realize,wordCost] at he
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_append,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨[],[],[],[],0⟩,(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize,wordCost]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_append)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p z => max (wordCost p.1 p.2.2.1 (wordScalar p.2.1 p.2.2.2.2)) z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_append.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_append.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p z => max (wordCost p.1 p.2.2.1 (wordScalar p.2.1 p.2.2.2.2)) z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.FixedTailClosedBudget, definition := none, coordinates := #[0, 1, 2, 3, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_append

namespace Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_endpoint_bound
abbrev signature : Signature where
  Params := Σ _ : List Label, Σ _ : List (Fin 6), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p z => max (wordCost p.1 p.2.1 p.2.2) z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : List Label) (r : List (Fin 6)) (lo hi x : ℝ), x ∈ Set.Icc lo hi → wordCost w r x ≤ max (wordCost w r lo) (wordCost w r hi)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : List Label) (r : List (Fin 6)) (lo hi x : ℝ), x ∈ Set.Icc lo hi → wordCost w r x ≤ R.readout () ⟨w,r,lo⟩ (wordCost w r hi)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh [] [] 0 0 0 ⟨le_rfl,le_rfl⟩
  norm_num [rejected,realize,wordCost] at he
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_endpoint_bound,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨[],[],0⟩,(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize,wordCost]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_endpoint_bound)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p z => max (wordCost p.1 p.2.1 p.2.2) z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_endpoint_bound.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_endpoint_bound.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p z => max (wordCost p.1 p.2.1 p.2.2) z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.FixedTailClosedBudget, definition := none, coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.FixedTailClosedBudget.cost_endpoint_bound

