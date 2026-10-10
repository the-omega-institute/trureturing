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

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.stateRec_limit
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ z => nhds z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : ℤ → Bool) (i : ℤ), Filter.Tendsto (fun n => pastRec w i n 0) Filter.atTop (nhds (stateRec w i))
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : ℤ → Bool) (i : ℤ), Filter.Tendsto (fun n => pastRec w i n 0) Filter.atTop (R.readout () () (stateRec w i))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hh' := hh (fun _ => false) 0
  exact Filter.atTop_neBot.ne (Filter.tendsto_bot_right_iff.mp hh')
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.stateRec_limit,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    exact nhds_injective.ne (by norm_num)
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.stateRec_limit)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ z => nhds z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.stateRec_limit.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.stateRec_limit.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ z => nhds z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookIndexed, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.stateRec_limit

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.stateRec_interval
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : ℤ → Bool) (i : ℤ), 0 ≤ stateRec w i ∧ stateRec w i ≤ h false
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : ℤ → Bool) (i : ℤ), R.readout () () 0 (stateRec w i) ∧ stateRec w i ≤ h false
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact (hh (fun _ => false) 0).1
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.stateRec_interval,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    intro he
    have bad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at bad
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.stateRec_interval)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.stateRec_interval.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.stateRec_interval.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookIndexed, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.stateRec_interval

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.stateRec_next
abbrev signature : Signature where
  Params := Σ _ : (ℤ → Bool), ℤ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p z => Statement.f (p.1 p.2) z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p _ => stateRec p.1 (p.2+1)+1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : ℤ → Bool) (i : ℤ), stateRec w (i+1) = Statement.f (w i) (stateRec w i)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : ℤ → Bool) (i : ℤ), stateRec w (i+1) = R.readout () ⟨w,i⟩ (stateRec w i)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh (fun _ => false) 0
  change stateRec (fun _ => false) (0+1) = stateRec (fun _ => false) (0+1)+1 at he
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.stateRec_next,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨(fun _ => true),0⟩,(0 : ℝ),(1 : ℝ),?_⟩
    change Statement.f true 0 ≠ Statement.f true 1
    simpa [Statement.f] using (ne_of_gt (parameters false).2.2.1).symm
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.stateRec_next)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p z => Statement.f (p.1 p.2) z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.stateRec_next.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.stateRec_next.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p z => Statement.f (p.1 p.2) z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookIndexed, definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.stateRec_next

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.past_eq_pastRec
abbrev signature : Signature where
  Params := Σ _ : (ℤ → Bool), Σ _ : ℤ, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p z => pastRec p.1 p.2.1 p.2.2 z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p z => pastRec p.1 p.2.1 p.2.2 z + 1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : ℤ → Bool) (i : ℤ) (n : ℕ) (z : ℝ), Statement.past w i n z = pastRec w i n z
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : ℤ → Bool) (i : ℤ) (n : ℕ) (z : ℝ), Statement.past w i n z = R.readout () ⟨w,i,n⟩ z
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh (fun _ => false) 0 0 0
  norm_num [rejected, realize, Statement.past, pastRec] at he
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.past_eq_pastRec,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨(fun _ => false),0,0⟩,(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize,pastRec]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.past_eq_pastRec)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p z => pastRec p.1 p.2.1 p.2.2 z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Coding.past_eq_pastRec.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.past_eq_pastRec.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p z => pastRec p.1 p.2.1 p.2.2 z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookIndexed, definition := none, coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"], stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.past_eq_pastRec

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.state_eq_stateRec
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : ℤ → Bool) (i : ℤ), Statement.state w i = stateRec w i
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : ℤ → Bool) (i : ℤ), R.readout () () (Statement.state w i) (stateRec w i)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh (fun _ => false) 0
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.state_eq_stateRec,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    intro he
    have bad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at bad
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.state_eq_stateRec)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Coding.state_eq_stateRec.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.state_eq_stateRec.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x y => x = y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookIndexed, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.state_eq_stateRec

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.letters_end_false
abbrev signature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ u => u ++ [false]) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (a : Return) (as : List Return), ∃ u : List Bool, Statement.letters (a::as) = u ++ [false]
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : Return) (as : List Return), ∃ u : List Bool, Statement.letters (a::as) = R.readout () () u
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  obtain ⟨u,hu⟩ := hh ⟨⟨1,1⟩,by constructor <;> omega⟩ []
  change [true,false] = [] at hu
  cases hu
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.letters_end_false,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),[],[true],?_⟩
    simp [actual,realize]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.letters_end_false)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ u => u ++ [false]) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Coding.letters_end_false.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.letters_end_false.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ u => u ++ [false]) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookIndexed, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.letters_end_false

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.aux_mem_XMinus
abbrev signature : Signature where
  Params := Unit
  State _ := Set (ℤ → Bool)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℤ → Bool) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ s w => w ∈ s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (K n : ℕ) (tau eps : ℝ) (w : ℤ → Bool), Statement.cap K w → (∀ i, Statement.high K w i → tau + eps ≤ stateRec w i) → 0 < eps → h false*rho^n < eps → w ∈ XMinus K n tau
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K n : ℕ) (tau eps : ℝ) (w : ℤ → Bool), Statement.cap K w → (∀ i, Statement.high K w i → tau + eps ≤ stateRec w i) → 0 < eps → h false*rho^n < eps → R.readout () () (XMinus K n tau) w
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  apply hh 2 0 0 (h false+1) (fun _ => false)
  · intro i hi
    have := hi 0 (by omega)
    simp at this
  · intro i hi
    have := hi 0 (by omega)
    simp at this
  · linarith [(parameters false).2.2.2.2.1]
  · simp
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.aux_mem_XMinus,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),Set.univ,∅,?_⟩
    intro he
    have bad : (fun _ : ℤ => false) ∈ (∅ : Set (ℤ → Bool)) :=
      Eq.mp (congrFun he (fun _ => false)) (Set.mem_univ _)
    exact bad
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.aux_mem_XMinus)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ s w => w ∈ s) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Coding.aux_mem_XMinus.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.aux_mem_XMinus.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ s w => w ∈ s) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookIndexed, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.aux_mem_XMinus

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.lowerLanguage_eq_XMinus
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (ℤ → Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ p tau => XMinus p.1 p.2 tau) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (K n : ℕ) (d : ℝ), Statement.lowerLanguage K n d = XMinus K n (chi^(K-1)*d)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K n : ℕ) (d : ℝ), Statement.lowerLanguage K n d = R.readout () ⟨K,n⟩ (chi^(K-1)*d)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh 2 0 0
  have hm : (fun _ : ℤ => false) ∈ Statement.lowerLanguage 2 0 0 := by
    constructor
    · intro j hj
      have := hj 0 (by omega)
      simp at this
    · intro j hj
      have := hj 0 (by omega)
      simp at this
  rw [he] at hm
  exact hm
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.lowerLanguage_eq_XMinus,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    let w : ℤ → Bool := fun j => decide (j = 0 ∨ j = -1)
    have hm : w ∈ XMinus 2 0 (-1) := by
      constructor
      · intro j hj
        have h0 := hj 0 (by omega)
        have h1 := hj 1 (by omega)
        have h2 := hj 2 (by omega)
        simp [w] at h0 h1 h2
        omega
      · intro j hj
        norm_num [pastRec]
    refine ⟨⟨2,0⟩,(-1 : ℝ),(0 : ℝ),?_⟩
    intro he
    change XMinus 2 0 (-1) = XMinus 2 0 0 at he
    have hm' : w ∈ XMinus 2 0 0 := he ▸ hm
    have hi : Statement.high 2 w 0 := by
      intro j hj
      have hh : j = 0 ∨ j = 1 := by omega
      rcases hh with rfl | rfl <;> simp [w]
    have bad := hm'.2 0 hi
    norm_num [pastRec] at bad
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Coding.lowerLanguage_eq_XMinus)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p tau => XMinus p.1 p.2 tau) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Coding.lowerLanguage_eq_XMinus.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.lowerLanguage_eq_XMinus.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p tau => XMinus p.1 p.2 tau) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookIndexed, definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookIndexed.lowerLanguage_eq_XMinus
