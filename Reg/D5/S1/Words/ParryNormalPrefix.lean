import D5.S1.Words.ParryNormalPrefix
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.ParryNormalPrefix
open _root_.D5.S1.Words.RankOneMorphismIterationBound (image subst)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.ParryNormalPrefix.greedy_remainder_prefix
universe u

abbrev signature : Signature where
  Params := Σ _α : Type u, ℕ
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => w.take p.2) (fun e _ => Empty.elim e)

def rejected : Realization signature :=
  realize signature (fun _ _ w => w) (fun e _ => Empty.elim e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (f : α → List α) (z : α)
    (digit : α → ℕ) (next : α → Option α)
    (_hshape : ∀ a, f a = List.replicate (digit a) z ++ (next a).toList)
    (_hpositive : ∀ k, 0 < (image f k z).length)
    (_hdominant : ∀ k a, (image f k a).length ≤ (image f k z).length)
    (k : ℕ) (a : α) (n : ℕ) (_hn : n < (image f k a).length),
      R.readout () ⟨α,n⟩ (image f k a) = greedyBlocks f z k n

private theorem actual_law : arena.{u}.Law actual :=
  @_root_.D5.S1.Words.ParryNormalPrefix.greedy_remainder_prefix

private theorem identity_image {α : Type u} (k : ℕ) (a : α) :
    image (fun b => [b]) k a = [a] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [image, ih, subst]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let α := ULift.{u} Unit
  let z : α := ⟨()⟩
  have hs : ∀ a : α, [a] = List.replicate 1 z ++ (none : Option α).toList := by
    intro a; have he : a = z := Subsingleton.elim _ _; simp [he]
  have hp : ∀ k, 0 < (image (fun a : α => [a]) k z).length := by
    intro k; simp [identity_image]
  have hd : ∀ k (a : α), (image (fun b : α => [b]) k a).length ≤
      (image (fun b : α => [b]) k z).length := by
    intro k a; simp [identity_image]
  have hh := h (fun a : α => [a]) z (fun _ => 1) (fun _ => none) hs hp hd
    0 z 0 (by simp [image])
  simp [rejected, realize, image, greedyBlocks] at hh

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S1.Words.ParryNormalPrefix.greedy_remainder_prefix.{u})) where
  actual := realize signature (fun _ p w => w.take p.2) (fun e _ => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℕ, 1⟩, [⟨0⟩], [⟨1⟩], ?_⟩
    change ([⟨0⟩] : List (ULift.{u} ℕ)) ≠ [⟨1⟩]
    decide

noncomputable def audit.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.ParryNormalPrefix.greedy_remainder_prefix.{u_1})
    (type_of% actual.{u_1}) Unit Unit := {
  unitName := `D5.S1.Words.ParryNormalPrefix.greedy_remainder_prefix.__information_unit,
  realizationName := `Reg.D5.S1.Words.ParryNormalPrefix.greedy_remainder_prefix.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p w => w.take p.2) (fun e _ => Empty.elim e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.ParryNormalPrefix, definition := none,
    coordinates := #[0, 10],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms family
#print axioms audit
end Reg.D5.S1.Words.ParryNormalPrefix.greedy_remainder_prefix

namespace Reg.D5.S1.Words.ParryNormalPrefix.greedy_prefix_of_successor_dominance
universe u

abbrev signature : Signature where
  Params := Σ _α : Type u, ℕ
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => w.take p.2) (fun e _ => Empty.elim e)

def rejected : Realization signature :=
  realize signature (fun _ _ w => w) (fun e _ => Empty.elim e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (f : α → List α) (z : α)
    (c : α → ℕ) (s : α → α)
    (_hf : ∀ a, f a = List.replicate (c a) z ++ [s a])
    (_hd : SuccessorDominated c s z) (k : ℕ) (a : α) (n : ℕ)
    (_hn : n < (image f k a).length),
      R.readout () ⟨α,n⟩ (image f k a) = greedyBlocks f z k n

private theorem actual_law : arena.{u}.Law actual :=
  @_root_.D5.S1.Words.ParryNormalPrefix.greedy_prefix_of_successor_dominance

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let α := ULift.{u} Unit
  let z : α := ⟨()⟩
  have hs : ∀ a : α, [a] = List.replicate 0 z ++ [a] := by simp
  have hd : SuccessorDominated (fun _ : α => 0) (fun a => a) z := by
    intro a k; exact Or.inl (by intro i hi; rfl)
  have hh := h (fun a : α => [a]) z (fun _ => 0) (fun a => a) hs hd
    0 z 0 (by simp [image])
  simp [rejected, realize, image, greedyBlocks] at hh

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S1.Words.ParryNormalPrefix.greedy_prefix_of_successor_dominance.{u})) where
  actual := realize signature (fun _ p w => w.take p.2) (fun e _ => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℕ, 1⟩, [⟨0⟩], [⟨1⟩], ?_⟩
    change ([⟨0⟩] : List (ULift.{u} ℕ)) ≠ [⟨1⟩]
    decide

noncomputable def audit.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.ParryNormalPrefix.greedy_prefix_of_successor_dominance.{u_1})
    (type_of% actual.{u_1}) Unit Unit := {
  unitName := `D5.S1.Words.ParryNormalPrefix.greedy_prefix_of_successor_dominance.__information_unit,
  realizationName := `Reg.D5.S1.Words.ParryNormalPrefix.greedy_prefix_of_successor_dominance.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p w => w.take p.2) (fun e _ => Empty.elim e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.ParryNormalPrefix, definition := none,
    coordinates := #[0, 9],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms family
#print axioms audit
end Reg.D5.S1.Words.ParryNormalPrefix.greedy_prefix_of_successor_dominance
