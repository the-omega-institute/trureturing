import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique
import Reg.Support.DependentFamily

/-! Source-bound registrations for the minimum suffix and uniqueness of Lyndon factors. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open _root_.D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique
universe u

abbrev signature : Signature where
  Params := Type u
  State A := List (List A)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ A := List A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ fs => fs.flatten) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

private theorem singleton_lyndon {A : Type u} [LinearOrder A] (a : A) : IsLyndon [a] := by
  refine ⟨by simp, ?_⟩
  intro x y hx hy hxy
  have hlen := congrArg List.length hxy
  simp only [List.length_singleton, List.length_append] at hlen
  have hxpos := List.length_pos_of_ne_nil hx
  have hypos := List.length_pos_of_ne_nil hy
  omega

namespace minimum

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [LinearOrder A] (fs : List (List A)) (m : List A),
    (∀ w ∈ fs ++ [m], IsLyndon w) →
    (fs ++ [m]).Pairwise (fun a b => b ≤ a) →
    IsLeast {s : List A | s ≠ [] ∧ s <:+ R.readout () A (fs ++ [m])} m

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} Nat := ⟨0⟩
  have hm : IsLyndon [a] := singleton_lyndon a
  have hh := h [] [a] (by simpa using hm) (by simp)
  have hs := hh.1.2
  change [a] <:+ ([] : List (ULift.{u} Nat)) at hs
  simpa using hs

def family : Registration arena.{u}
    (type_of% (@last_factor_is_min_nonempty_suffix.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@last_factor_is_min_nonempty_suffix, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨ULift.{u} Nat, [], [[⟨0⟩]], ?_⟩
    intro h
    have hl := congrArg List.length h
    change 0 = 1 at hl
    omega

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@last_factor_is_min_nonempty_suffix.{u}) (type_of% actual.{u}) Unit Unit where
  unitName := `D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique.last_factor_is_min_nonempty_suffix.__information_unit
  realizationName := `Reg.D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique.minimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ fs => fs.flatten) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end minimum

namespace uniqueness

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [LinearOrder A] (fs gs : List (List A)),
    (∀ w ∈ fs, IsLyndon w) → fs.Pairwise (fun a b => b ≤ a) →
    (∀ w ∈ gs, IsLyndon w) → gs.Pairwise (fun a b => b ≤ a) →
    R.readout () A fs = R.readout () A gs → fs = gs

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} Nat := ⟨0⟩
  have hh := h ([] : List (List (ULift.{u} Nat))) [[a]] (by simp) (by simp)
    (by simpa using singleton_lyndon a) (by simp) rfl
  cases hh

def family : Registration arena.{u}
    (type_of% (@nonincreasing_lyndon_factorization_unique.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonincreasing_lyndon_factorization_unique, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨ULift.{u} Nat, [], [[⟨0⟩]], ?_⟩
    intro h
    have hl := congrArg List.length h
    change 0 = 1 at hl
    omega

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonincreasing_lyndon_factorization_unique.{u}) (type_of% actual.{u}) Unit Unit where
  unitName := `D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique.nonincreasing_lyndon_factorization_unique.__information_unit
  realizationName := `Reg.D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique.uniqueness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ fs => fs.flatten) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end uniqueness

end Reg.D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique
