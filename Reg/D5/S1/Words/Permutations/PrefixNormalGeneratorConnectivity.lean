import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity

/-! Source-bound four-slot registrations for the retained generator connectivity proof. -/

open _root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity

private theorem path_length {P : List Nat → Prop} {l m : List Nat}
    (h : Relation.ReflTransGen (Edge P) l m) : l.length = m.length := by
  induction h with
  | refl => rfl
  | @tail u v h e ih =>
    have he : u.length = v.length := by
      rcases e with ⟨_, _, p, s, a, b, rfl, rfl⟩
      simp [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    exact ih.trans he

private theorem generator_one : Generator 1 [0] := by
  constructor
  · decide
  · intro t ht
    interval_cases t <;> intro s l hsl
    all_goals
      have hs : s ≤ 1 := by omega
      have hl : l ≤ 1 := by omega
      interval_cases s <;> interval_cases l <;> norm_num [count] at *

private theorem generator_three : Generator 3 [1,2,0] := by
  constructor
  · decide
  · intro t ht
    interval_cases t <;> intro s l hsl
    all_goals
      have hs : s ≤ 3 := by omega
      have hl : l ≤ 3 := by omega
      interval_cases s <;> interval_cases l <;> norm_num [count] at *

namespace count_erase
abbrev signature := Reg.Support.SingleDependentReadout.signature (Σ _ : Finset Nat, Σ _ : Nat, Nat)
  (fun _ => Nat) (fun _ => Nat)

def actual : Realization signature :=
  realize signature (fun _ p a =>
    if a ∈ p.1 ∧ p.2.1 ≤ a ∧ a < p.2.1 + p.2.2
      then count p.1 p.2.1 p.2.2 - 1 else count p.1 p.2.1 p.2.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (S : Finset Nat) (s l a : Nat),
    count (S.erase a) s l = R.readout () ⟨S,s,l⟩ a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h ∅ 0 0 0
  change count ((∅ : Finset Nat).erase 0) 0 0 = 2 at hh
  exact (by decide : ¬ (count ((∅ : Finset Nat).erase 0) 0 0 = 2)) hh

def evidence : Registration arena (type_of% (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.count_erase)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.count_erase, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨⟨{0},0,1⟩, 0, 1, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.count_erase) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.count_erase.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.count_erase.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end count_erase

namespace erase_later_preserves
abbrev signature := Reg.Support.SingleDependentReadout.signature (Nat)
  (fun _ => Finset Nat) (fun _ => Finset Nat)

def actual : Realization signature :=
  realize signature (fun _ b S => S.erase b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => {1}) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : Nat) (S : Finset Nat) (a b : Nat),
    a < b → a ∈ S → b ∈ S → PN n S → PN n (S.erase a) →
      PN n (R.readout () b S)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hS : PN 3 ({0,1,2} : Finset Nat) := by
    have he : (([1,2,0] : List Nat).drop 0).toFinset = ({0,1,2} : Finset Nat) := by decide
    rw [← he]
    exact generator_three.2 0 (by decide)
  have hA : PN 3 (({0,1,2} : Finset Nat).erase 1) := by
    have he : (([1,2,0] : List Nat).drop 1).toFinset = ({0,1,2} : Finset Nat).erase 1 := by decide
    rw [← he]
    exact generator_three.2 1 (by decide)
  have hh := h 3 {0,1,2} 1 2 (by decide) (by decide) (by decide) hS hA
  have impossible := hh 1 1 (by decide)
  change count {1} 1 1 ≤ count {1} 0 1 at impossible
  exact (by decide : ¬ (count {1} 1 1 ≤ count {1} 0 1)) impossible

def evidence : Registration arena (type_of% (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.erase_later_preserves)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.erase_later_preserves, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨0, ∅, {1}, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.erase_later_preserves) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.erase_later_preserves.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.erase_later_preserves.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end erase_later_preserves

namespace generator_ascent_swap
abbrev signature := Reg.Support.SingleDependentReadout.signature (List Nat)
  (fun _ => List Nat) (fun _ => List Nat)

def actual : Realization signature :=
  realize signature (fun _ p s => p ++ s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : Nat) (p s : List Nat) (a b : Nat),
    a < b → Generator n (p ++ a :: b :: s) →
      Generator n (R.readout () p (b :: a :: s))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 3 [] [0] 1 2 (by decide) generator_three
  have impossible := hh.1.length_eq
  norm_num [rejected, realize] at impossible

def evidence : Registration arena (type_of% (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_ascent_swap)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_ascent_swap, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    exact ⟨[], [], [0], by simp [actual, realize]⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_ascent_swap) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_ascent_swap.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_ascent_swap.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end generator_ascent_swap

namespace normalize_by_adjacent_ascents
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => List Nat) (fun _ => List Nat)

def actual : Realization signature :=
  realize signature (fun _ _ l => l.insertionSort (fun a b : Nat => b ≤ a)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : List Nat → Prop),
    (∀ (p s : List Nat) (a b : Nat), a < b →
      P (p ++ a :: b :: s) → P (p ++ b :: a :: s)) →
    ∀ (l p : List Nat), P (p ++ l) →
      Relation.ReflTransGen (Edge P) (p ++ l)
        (p ++ R.readout () () l)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => True) (by intros; trivial) [0] [] trivial
  have impossible := path_length hh
  change 1 = 0 at impossible
  omega

def evidence : Registration arena (type_of% (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.normalize_by_adjacent_ascents)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.normalize_by_adjacent_ascents, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨(), [], [0], by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.normalize_by_adjacent_ascents) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.normalize_by_adjacent_ascents.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.normalize_by_adjacent_ascents.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end normalize_by_adjacent_ascents

namespace full_event_list
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => List Nat) (fun _ => List Nat)

def actual : Realization signature :=
  realize signature (fun _ _ m => m) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : Nat) (l m : List Nat), Generator n l → Generator n m →
    Relation.ReflTransGen (Edge (Generator n)) l (R.readout () () m)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible := path_length (h 1 [0] [0] generator_one generator_one)
  norm_num [rejected, realize] at impossible

def evidence : Registration arena (type_of% (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.full_event_list)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.full_event_list, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    exact ⟨(), [], [0], by simp [actual, realize]⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.full_event_list) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.full_event_list.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.full_event_list.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end full_event_list

namespace suffix_eq_undeleted
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => List Nat) (fun _ => Finset Nat)

def actual : Realization signature :=
  realize signature (fun _ _ l => l.toFinset) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : Nat) (l : List Nat), l.Perm (List.range n) → ∀ (t : Nat),
    R.readout () () (l.drop t) = Finset.range n \ (l.take t).toFinset

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 [0] (by decide) 0
  change (∅ : Finset Nat) = {0} at hh
  exact (by decide : ¬ (∅ : Finset Nat) = {0}) hh

def evidence : Registration arena (type_of% (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.suffix_eq_undeleted)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.suffix_eq_undeleted, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    exact ⟨(), [], [0], by simp [actual, realize]⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.suffix_eq_undeleted) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.suffix_eq_undeleted.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.suffix_eq_undeleted.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end suffix_eq_undeleted

namespace generator_iff_exact
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => List Nat) (fun _ => List Nat)

def actual : Realization signature :=
  realize signature (fun _ _ l => l) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : Nat) (l : List Nat),
    Generator n l ↔ ExactGenerator n (R.readout () () l)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 [0]).mp generator_one
  have impossible := hh.1.length_eq
  norm_num [rejected, realize] at impossible

def evidence : Registration arena (type_of% (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_iff_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_iff_exact, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    exact ⟨(), [], [0], by simp [actual, realize]⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_iff_exact) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_iff_exact.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.generator_iff_exact.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end generator_iff_exact

namespace result
abbrev signature := Reg.Support.SingleDependentReadout.signature (Unit)
  (fun _ => List Nat) (fun _ => List Nat)

def actual : Realization signature :=
  realize signature (fun _ _ m => m) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : Nat) (l m : List Nat), ExactGenerator n l → ExactGenerator n m →
    Relation.ReflTransGen (Edge (ExactGenerator n)) l (R.readout () () m)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hOne := (generator_iff_exact 1 [0]).mp generator_one
  have impossible := path_length (h 1 [0] [0] hOne hOne)
  norm_num [rejected, realize] at impossible

def evidence : Registration arena (type_of% (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    exact ⟨(), [], [0], by simp [actual, realize]⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.result) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.result.__information_unit
  realizationName := `Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity.result.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end result

end Reg.D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
