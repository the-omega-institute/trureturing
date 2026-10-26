import D5.S1.Words.Sequenceability.BlockSpliceOrdering
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.CharP.Two

/-! The complete group-valued interval observation, with the original telescope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.Sequenceability.BlockSpliceOrdering

open _root_.D5.S1.Words.Sequenceability.BlockSpliceOrdering
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

abbrev signature : Signature where
  Params := Σ G : Type u, AddCommGroup G × (ℕ × ℕ)
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p w => by
    letI := p.2.1
    exact ((w.drop p.2.2.1).take (p.2.2.2 - p.2.2.1)).sum)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => by letI := p.2.1; exact 0)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] (z c : ℕ → G) (N k t : ℕ),
    2 ≤ k → k ≤ t → t < N →
    Set.InjOn z (Set.Iio N) → Set.InjOn c (Set.Iio N) →
    (∀ i < N, c i = z ((i + 1) % N) - z i) → z k - z 0 = c t →
    ∃ (P : ℕ → G) (w : List G),
      ((List.range (N - k + 1)).map P).Perm ((0 :: List.range' k (N - k)).map z) ∧
      ((List.range (N - k + 1)).map P).Nodup ∧
      w = (List.range (N - k)).map (fun i => P (i + 1) - P i) ∧
      (∀ j ≤ N - k, (w.take j).sum = P j - P 0) ∧
      w.Perm ((List.range' k (N - k)).map c) ∧ w.Nodup ∧ w.length = N - k ∧
      Function.Injective (fun j : Fin (w.length + 1) => (w.take j.val).sum) ∧
      (∀ i j : ℕ, i < j → j ≤ w.length →
        R.readout () ⟨G, inferInstance, i, j⟩ w ≠ 0) ∧
      w.sum = -c t ∧ w.sum ≠ 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let z : ℕ → ULift.{u} (ZMod 2 × ZMod 2) := fun i =>
    ⟨if i = 0 then (1, 0) else if i = 1 then (0, 1) else (1, 1)⟩
  let c : ℕ → ULift.{u} (ZMod 2 × ZMod 2) := fun i =>
    ⟨if i = 0 then (1, 1) else if i = 1 then (1, 0) else (0, 1)⟩
  have hz : Set.InjOn z (Set.Iio 3) := by
    intro i hi j hj he
    have hi' : i < 3 := hi
    have hj' : j < 3 := hj
    interval_cases i <;> interval_cases j <;> first | rfl | simpa [z] using he
  have hc : Set.InjOn c (Set.Iio 3) := by
    intro i hi j hj he
    have hi' : i < 3 := hi
    have hj' : j < 3 := hj
    interval_cases i <;> interval_cases j <;> first | rfl | simpa [c] using he
  have hcycle : ∀ i < 3, c i = z ((i + 1) % 3) - z i := by
    intro i hi
    interval_cases i <;> ext <;> norm_num [z, c] <;>
      simp only [CharTwo.neg_one_eq_one]
  have hchord : z 2 - z 0 = c 2 := by ext <;> norm_num [z, c, CharTwo.neg_one_eq_one]
  obtain ⟨P, w, _, _, _, _, _, _, hwlen, _, hint, _, _⟩ :=
    @h (ULift.{u} (ZMod 2 × ZMod 2)) inferInstance z c 3 2 2
      (by omega) (by omega) (by omega) hz hc hcycle hchord
  exact hint 0 1 (by omega) (by omega) rfl

def family : Registration arena.{u} (type_of% (@block_splice_ordering.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨block_splice_ordering, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℤ, inferInstance, 0, 1⟩, [0], [1], ?_⟩
    change (0 : ULift.{u} ℤ) ≠ 1
    exact zero_ne_one

def audit : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@block_splice_ordering.{u}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName :=
    `D5.S1.Words.Sequenceability.BlockSpliceOrdering.block_splice_ordering.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.BlockSpliceOrdering.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.BlockSpliceOrdering
    definition := none
    coordinates := #[0, 16, 17]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.BlockSpliceOrdering
