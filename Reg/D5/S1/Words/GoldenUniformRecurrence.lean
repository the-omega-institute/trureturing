import D5.S1.Words.GoldenUniformRecurrence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Tactic

open _root_.D5.S1.Words
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.GoldenUniformRecurrence
universe u v

namespace take_drop_isInfix

abbrev signature : Signature where
  Params := Σ _α : Type u, Σ _p : ℕ, ℕ
  State p := List p.1
  Output _ p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p l => (l.drop p.2.1).take p.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ l => l ++ l) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} (l : List α) (p n : ℕ), R.readout () ⟨α, p, n⟩ l <:+: l

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := h ([⟨()⟩] : List (ULift.{u} Unit)) 0 1
  have hl := hh.length_le
  change 2 ≤ 1 at hl
  omega

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S1.Words.take_drop_isInfix.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.take_drop_isInfix, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨ULift.{u} Unit, 0, 1⟩, [], [⟨()⟩], ?_⟩
    intro he
    have hl := congrArg List.length he
    change 0 = 1 at hl
    omega

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.take_drop_isInfix.{u}) (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S1.Words.take_drop_isInfix.__information_unit,
  realizationName := `Reg.D5.S1.Words.GoldenUniformRecurrence.take_drop_isInfix.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u}
    (fun _ p l => (l.drop p.2.1).take p.2.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.GoldenUniformRecurrence, definition := none,
    coordinates := #[0, 2, 3],
    readouts := #[{
      path := #[
        "body",
        "body",
        "body",
        "body",
        "fn",
        "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end take_drop_isInfix

namespace exists_flatMap_block

abbrev signature : Signature where
  Params := Σ α : Type u, Σ β : Type v, α → List β
  State p := p.1
  Output _ p := List p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature.{u, v} (fun _ p a => p.2.2 a) (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature.{u, v} (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {α : Type u} {β : Type v} {f : α → List β} {l : List α} {p : ℕ}
    (_hp : p < (l.flatMap f).length),
    ∃ (pre : List α) (a : α) (post : List α), l = pre ++ a :: post ∧
      (pre.flatMap f).length ≤ p ∧
      p < (pre.flatMap f).length + (R.readout () ⟨α, β, f⟩ a).length

private theorem rejected_law : ¬ arena.{u, v}.Law rejected.{u, v} := by
  intro h
  let f : ULift.{u} Unit → List (ULift.{v} Unit) := fun _ => [⟨()⟩]
  obtain ⟨pre, a, post, he, _, hi⟩ := h (f := f) (l := [⟨()⟩]) (p := 0) (by decide)
  have hl := congrArg List.length he
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  have hpre : pre = [] := by
    cases pre with
    | nil => rfl
    | cons b bs => simp only [List.length_cons] at hl; omega
  subst pre
  simp [rejected, realize] at hi

def family : Registration arena.{u, v}
    (type_of% (@_root_.D5.S1.Words.exists_flatMap_block.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.exists_flatMap_block, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    let f : ULift.{u} Bool → List (ULift.{v} Unit) :=
      fun b => if b.down then [⟨()⟩] else []
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Unit, f⟩, ⟨false⟩, ⟨true⟩, ?_⟩
    intro he
    have hl := congrArg List.length he
    change 0 = 1 at hl
    omega

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.exists_flatMap_block.{u, v}) (type_of% actual.{u, v}) Unit Unit := {
  unitName := `D5.S1.Words.exists_flatMap_block.__information_unit,
  realizationName := `Reg.D5.S1.Words.GoldenUniformRecurrence.exists_flatMap_block.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u, v}
    (fun _ p a => p.2.2 a) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.GoldenUniformRecurrence, definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #[
        "body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "arg",
        "body",
        "arg",
        "body",
        "arg",
        "body",
        "arg",
        "arg",
        "arg",
        "arg",
        "arg"],
      stateBinder := 7,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end exists_flatMap_block

namespace take_drop_append_eq_left

abbrev signature : Signature where
  Params := Σ α : Type u, Σ _y : List α, Σ _p : ℕ, ℕ
  State p := List p.1
  Output _ p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p x => ((x ++ p.2.1).drop p.2.2.1).take p.2.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} {x y : List α} {p n : ℕ} (_h : p + n ≤ x.length),
    R.readout () ⟨α, y, p, n⟩ x = (x.drop p).take n

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := h (x := ([⟨()⟩] : List (ULift.{u} Unit))) (y := [])
    (p := 0) (n := 1) (by decide)
  have hl := congrArg List.length hh
  change 0 = 1 at hl
  omega

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S1.Words.take_drop_append_eq_left.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.take_drop_append_eq_left, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨ULift.{u} Unit, [], 0, 1⟩, [], [⟨()⟩], ?_⟩
    intro he
    have hl := congrArg List.length he
    change 0 = 1 at hl
    omega

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.take_drop_append_eq_left.{u}) (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S1.Words.take_drop_append_eq_left.__information_unit,
  realizationName := `Reg.D5.S1.Words.GoldenUniformRecurrence.take_drop_append_eq_left.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u}
    (fun _ p x => ((x ++ p.2.1).drop p.2.2.1).take p.2.2.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.GoldenUniformRecurrence, definition := none,
    coordinates := #[0, 2, 3, 4],
    readouts := #[{
      path := #[
        "body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "fn",
        "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg", "arg", "fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end take_drop_append_eq_left

end Reg.D5.S1.Words.GoldenUniformRecurrence

namespace Reg.D5.S1.Words.GoldenUniformRecurrence.flatMap_window_infix_one_or_two
universe u v
abbrev signature : Signature where
  Params := Σ α : Type u, Σ β : Type v, Σ _f : α → List β, ℕ × ℕ
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} := realize signature
  (fun _ p l => ((l.flatMap p.2.2.1).drop p.2.2.2.1).take p.2.2.2.2)
  (fun e => nomatch e)

def rejected : Realization signature.{u,v} := realize signature
  (fun _ p l => actual.readout () p l ++ actual.readout () p l ++ actual.readout () p l)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {α : Type u} {β : Type v} {f : α → List β} {l : List α} {p n : ℕ}
    (_hnpos : 0 < n) (_hblocks : ∀ a ∈ l, n < (f a).length)
    (_hend : p+n ≤ (l.flatMap f).length),
    (∃ a, [a] <:+: l ∧ R.readout () ⟨α, β, f, p, n⟩ l <:+: f a) ∨
      ∃ a b, [a,b] <:+: l ∧ ((l.flatMap f).drop p).take n <:+: f a ++ f b

private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  let f : ULift.{u} Unit → List (ULift.{v} Unit) := fun _ => [⟨()⟩, ⟨()⟩]
  have hh := h (f := f) (l := [⟨()⟩]) (p := 0) (n := 1)
    (by decide) (by intro a ha; norm_num [f]) (by norm_num [f])
  rcases hh with ⟨a, _, ha⟩ | ⟨a, b, hab, _⟩
  · have hl := ha.length_le
    change 3 ≤ 2 at hl
    omega
  · have hl := hab.length_le
    change 2 ≤ 1 at hl
    omega

def family : Registration arena.{u,v}
    (type_of% (@_root_.D5.S1.Words.flatMap_window_infix_one_or_two.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.flatMap_window_infix_one_or_two,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit, (fun _ => [⟨()⟩]), 0, 1⟩,
      [], [⟨()⟩], ?_⟩
    change ([] : List (ULift.{v} Unit)) ≠ [⟨()⟩]
    simp

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.flatMap_window_infix_one_or_two.{u,v})
    (type_of% actual.{u,v}) Unit Unit := {
  unitName := `D5.S1.Words.flatMap_window_infix_one_or_two.__information_unit,
  realizationName := `Reg.D5.S1.Words.GoldenUniformRecurrence.flatMap_window_infix_one_or_two.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.GoldenUniformRecurrence, definition := none,
    coordinates := #[0, 1, 2, 4, 5], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "fn", "arg"],
      stateBinder := 3, functionOperand := false, stateOperand := some #["arg", "arg", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Reg.D5.S1.Words.GoldenUniformRecurrence.flatMap_window_infix_one_or_two
