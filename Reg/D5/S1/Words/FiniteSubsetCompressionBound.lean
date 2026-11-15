import D5.S1.Words.FiniteSubsetCompressionBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The original compression telescope with its actual finite-image readout. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.FiniteSubsetCompressionBound

universe u v

structure Parameters where
  States : Type u
  Letters : Type v
  equality : DecidableEq States
  step : States → Letters → States
  cost : Nat → Nat

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Finset p.States
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def compressionConclusion (p : Parameters.{u,v}) (S : Finset p.States) : Prop :=
  letI := p.equality
  ∃ w : List p.Letters,
    w.length ≤ ∑ k ∈ Finset.range (S.card - 1), p.cost (k + 2) ∧
      (S.image (fun x => w.foldl p.step x)).card ≤ 1

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p S => compressionConclusion p S) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ (X : Type u) (A : Type v) (eqX : DecidableEq X)
    (step : X → A → X) (C : Nat → Nat) (S : Finset X),
    letI := eqX
    (∀ T : Finset X, 2 ≤ T.card →
      ∃ w : List A, w.length ≤ C T.card ∧
        (T.image (fun x => w.foldl step x)).card < T.card) →
      R.readout () ⟨X, A, eqX, step, C⟩ S

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have localReduction : ∀ T : Finset (ULift.{u} Unit), 2 ≤ T.card →
      ∃ w : List (ULift.{v} Unit), w.length ≤ 0 ∧
        (T.image (fun x => w.foldl (fun y _ => y) x)).card < T.card := by
    intro T hT
    have := Finset.card_le_one_of_subsingleton T
    omega
  exact h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance
    (fun x _ => x) (fun _ => 0) ∅ localReduction

private abbrev separatingParameters : Parameters.{u,v} where
  States := ULift.{u} Bool
  Letters := ULift.{v} Unit
  equality := inferInstance
  step x _ := x
  cost _ := 0

private theorem empty_readout :
    compressionConclusion separatingParameters.{u,v} ∅ := by
  refine ⟨[], Nat.zero_le _, ?_⟩
  change (Finset.image (fun x : ULift.{u} Bool => x) ∅).card ≤ 1
  simp

private theorem two_readout :
    ¬ compressionConclusion separatingParameters.{u,v}
      {⟨false⟩, ⟨true⟩} := by
  rintro ⟨w, hw, hcard⟩
  have hwzero : w.length = 0 := Nat.eq_zero_of_le_zero (by simpa using hw)
  have hnil : w = [] := List.eq_nil_of_length_eq_zero hwzero
  subst w
  simpa using hcard

def family : Registration arena.{u,v}
    (type_of% (@_root_.D5.S1.Words.FiniteSubsetCompressionBound.exists_compressing_word_length_le.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.FiniteSubsetCompressionBound.exists_compressing_word_length_le,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨separatingParameters, ∅, {⟨false⟩, ⟨true⟩}, ?_⟩
    change compressionConclusion separatingParameters ∅ ≠
      compressionConclusion separatingParameters {⟨false⟩, ⟨true⟩}
    intro heq
    exact two_readout (Eq.mp heq empty_readout)

noncomputable def audit : Contract.Registration
    (@_root_.D5.S1.Words.FiniteSubsetCompressionBound.exists_compressing_word_length_le.{u,v})
    (type_of% actual.{u,v}) Unit Unit := {
  unitName := `D5.S1.Words.FiniteSubsetCompressionBound.exists_compressing_word_length_le.__information_unit,
  realizationName := `Reg.D5.S1.Words.FiniteSubsetCompressionBound.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.FiniteSubsetCompressionBound, definition := none,
    coordinates := #[0, 1, 3, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"],
      stateBinder := 5, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S1.Words.FiniteSubsetCompressionBound
