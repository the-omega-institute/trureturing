/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionBranchExistence
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every nonfinite native completion has an actual infinite address branch. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
import Mathlib.Order.WellFounded
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply)
open NativeCompletionPrefixLifting

/-- The relation uses the actual ordered children, allowing equal or repeated subtrees. -/
def Child (S T : CompletionTree) : Prop :=
  ∃ l r, T = node l r ∧ (S = l ∨ S = r)

private theorem finite_of_accessible (T : CompletionTree) (h : Acc Child T) :
    ∃ t : Source, embed t = T := by
  induction h with
  | intro T _ ih =>
    induction T using tree_cases with
    | leaf_case b => exact ⟨.of b, rfl⟩
    | node_case l r =>
      obtain ⟨s, hs⟩ := ih l ⟨l, r, rfl, Or.inl rfl⟩
      obtain ⟨t, ht⟩ := ih r ⟨l, r, rfl, Or.inr rfl⟩
      refine ⟨.mul s t, ?_⟩
      change node (embed s) (embed t) = node l r
      rw [hs, ht]

private theorem child_direction {S T : CompletionTree} (h : Child S T) :
    ∃ b : Bool, ∀ a : Address, completionReadout (b :: a) T = completionReadout a S := by
  obtain ⟨l, r, rfl, h⟩ := h
  rcases h with rfl | rfl
  · exact ⟨false, fun a => by simp [completionReadout, node]⟩
  · exact ⟨true, fun a => by simp [completionReadout, node]⟩

private theorem root_present (T : CompletionTree) : completionReadout [] T ≠ .absent := by
  induction T using tree_cases with
  | leaf_case b => cases b <;> simp [completionReadout, leaf]
  | node_case l r => simp [completionReadout, node]

private theorem chain_readout (T : Nat → CompletionTree) (b : Nat → Bool)
    (step : ∀ n a, completionReadout (b n :: a) (T n) = completionReadout a (T (n + 1)))
    (d : Nat) (a : Address) :
    completionReadout (List.ofFn (fun i : Fin d => b i.val) ++ a) (T 0) =
      completionReadout a (T d) := by
  induction d generalizing a with
  | zero => simp
  | succ d ih =>
    rw [List.ofFn_succ']
    simpa only [List.concat_eq_append, List.append_assoc, List.singleton_append,
      Fin.val_castSucc, Fin.val_last] using
      (ih (b d :: a)).trans (step d a)

/-- A completion outside the exact finite embedding has one coherent branch at every depth. -/
theorem infinite_of_not_finite (T : CompletionTree)
    (h : ¬ ∃ t : Source, embed t = T) : HasInfiniteBranch T := by
  classical
  have inaccessible : ¬ Acc Child T := fun hacc => h (finite_of_accessible T hacc)
  obtain ⟨trees, first, descend⟩ := not_acc_iff_exists_descending_chain.mp inaccessible
  choose b direction using fun n => child_direction (descend n)
  refine ⟨b, fun d => ?_⟩
  have same := chain_readout trees b direction d []
  simp only [List.append_nil, first] at same
  rw [same]
  exact root_present (trees d)

#print axioms infinite_of_not_finite

end D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence
