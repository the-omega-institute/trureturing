import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.CounterSequences.KimberlingA371279

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Arith.CounterSequences.KimberlingA371279
open _root_.D5.S3.Arith.CounterSequences.KimberlingA371279
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace Update
abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => List ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := DependentFamily.realize signature (fun _ _ xs => nextList xs) (fun e => nomatch e)
abbrev arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ xs : List ℚ, xs.Nodup →
    r.readout () () xs = (xs ++ pairList xs).eraseDups
abbrev sourceScope := type_of% (@source_update)
theorem bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased := DependentFamily.realize signature (fun _ _ _ => []) (fun e => nomatch e)
theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := h [1] (by simp)
  change ([] : List ℚ) = ([1] ++ pairList [1]).eraseDups at hh
  have hm : (1 : ℚ) ∈ ([1] ++ pairList [1]).eraseDups := by simp
  rw [← hh] at hm
  simpa using hm

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@source_update), erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), [], [1], ?_⟩
    change nextList [] ≠ nextList [1]
    intro he
    have hm : (1 : ℚ) ∈ nextList [1] := by simp [nextList]
    rw [← he] at hm
    simpa [nextList, freshTail, pairList, firstRetention, firstRetentionAux] using hm

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@source_update) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Arith.CounterSequences.KimberlingA371279.source_update.__information_unit
  realizationName := `Reg.D5.S3.Arith.CounterSequences.KimberlingA371279.Update.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ _ xs => nextList xs) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (List ℚ : Type)
  sourceSelection := some {
    owner := `D5.S3.Arith.CounterSequences.KimberlingA371279
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Update

namespace Whole
abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := DependentFamily.realize signature (fun _ _ i => fraction i) (fun e => nomatch e)
abbrev arena : DependentFamily.Arena where
  signature := signature
  Law := fun r =>
    (∀ n, cumulative (n + 1) = (cumulative n ++ pairList (cumulative n)).eraseDups) ∧
    (∀ n, cumulative n = flattenedPrefix (n + 1)) ∧
    (∀ n q, q ∈ cumulative n → 0 < q ∧ q ≤ 1) ∧
    (∀ q : ℚ, 0 < q → q ≤ 1 → ∃! p : ℕ × ℕ, Occurs q p) ∧
    (∀ t, ∃ n, t < (flattenedPrefix n).length) ∧
    (∀ n i, i < (flattenedPrefix n).length →
      (flattenedPrefix n)[i]? = some (r.readout () () i)) ∧
    (∀ q p, Occurs q p → r.readout () () (flatIndex p) = q) ∧
    (∀ t, ∃! p : ℕ × ℕ, Occurs (r.readout () () t) p ∧ flatIndex p = t) ∧
    Function.Injective (r.readout () ()) ∧
    (∀ i, 0 < r.readout () () i ∧ r.readout () () i ≤ 1 ∧
      0 < denominator i ∧ (numerator i).natAbs.Coprime (denominator i) ∧
      r.readout () () i = (numerator i : ℚ) / (denominator i : ℚ))
abbrev sourceScope := type_of% (@result)
theorem bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased := DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)
theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := h.2.2.2.2.2.1 1 0 (by decide)
  exact (by decide : (flattenedPrefix 1)[0]? ≠ some (0 : ℚ)) hh

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp result, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, DependentFamily.realize, fraction, cumulative,
      nextList, freshTail, pairList, firstRetention, firstRetentionAux]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@result) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Arith.CounterSequences.KimberlingA371279.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.CounterSequences.KimberlingA371279.Whole.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ _ i => fraction i) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (ℕ : Type)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Whole
end Reg.D5.S3.Arith.CounterSequences.KimberlingA371279
