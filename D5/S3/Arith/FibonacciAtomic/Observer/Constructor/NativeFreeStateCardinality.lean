/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFreeStateCardinality
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFreeStateCardinality
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Function.Basic]
   utility: none
   digest: Infinite native stream trees exclude countable all-solution parameterizations. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
import Mathlib.Logic.Function.Basic
import Mathlib.Basic.Countable.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFreeStateCardinality

open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints
open ActualTreeReadoutAcquisition (Address Reply)

/-- Shift the supplied infinite sequence by one chronological position. -/
def tail (s : Nat → Bool) : Nat → Bool := fun j => s (j + 1)

/-- False denotes the left edge and true the right edge. -/
def bitAddress (j : Nat) : Address := List.replicate j false ++ [true]

private def streamStep : (Nat → Bool) ⊕ Bool →
    completionFunctor ((Nat → Bool) ⊕ Bool)
  | .inl s => ⟨.inr (), fun b => if b then .inr (s 0) else .inl (tail s)⟩
  | .inr b => ⟨.inl (!b), Empty.elim⟩

/-- The infinite left spine retains the original bit at its j-th right leaf.
The bit false is the native alpha atom and true is the native beta atom. -/
def streamTree (s : Nat → Bool) : CompletionTree :=
  PFunctor.M.corec streamStep (.inl s)

private theorem streamStep_leaf (b : Bool) :
    PFunctor.M.corec streamStep (.inr b) = leaf (!b) := by
  rw [PFunctor.M.corec_def]
  apply congrArg PFunctor.M.mk
  apply Sigma.ext rfl
  apply heq_of_eq
  funext e
  exact e.elim

private theorem streamTree_unfold (s : Nat → Bool) :
    streamTree s = node (streamTree (tail s)) (leaf (!(s 0))) := by
  unfold streamTree
  rw [PFunctor.M.corec_def]
  simp only [streamStep, PFunctor.map, node]
  congr 1
  congr 1
  funext b
  cases b
  · rfl
  · exact streamStep_leaf _

/-- Exact reached whole subtrees, with no value assigned to an absent address. -/
private theorem streamTree_subtree (s : Nat → Bool) (j : Nat) :
    subtree (bitAddress j) (streamTree s) = some (leaf (!(s j))) := by
  induction j generalizing s with
  | zero =>
    rw [streamTree_unfold]
    rfl
  | succ j ih =>
    simp only [bitAddress, List.replicate_succ, List.cons_append]
    rw [streamTree_unfold]
    change subtree (bitAddress j) (streamTree (tail s)) = _
    simpa only [tail] using ih (tail s)

private theorem streamTree_injective : Function.Injective streamTree := by
  intro s t h
  funext j
  have bits := congrArg (subtree (bitAddress j)) h
  rw [streamTree_subtree, streamTree_subtree] at bits
  have labels := GenealogicalFiberTransport.Source.of.inj
    (NativeCompletionSupportClosure.embed_injective
      (show embed (.of (!(s j))) = embed (.of (!(t j))) from Option.some.inj bits))
  exact Bool.not_inj labels

private theorem streamTree_ne_omega (s : Nat → Bool) : streamTree s ≠ Omega := by
  intro h
  have equation := streamTree_unfold s
  rw [h] at equation
  have right := (node_inj (omega_node.symm.trans equation)).2
  have tag := congrArg (fun X => (PFunctor.M.dest X).1) right
  conv_lhs at tag => rw [omega_node]
  simp [leaf, node] at tag

private theorem completed_not_countable : ¬ Countable CompletionTree := by
  classical
  intro h
  letI := h
  obtain ⟨encode, hinj⟩ := Countable.exists_injective_nat CompletionTree
  let characteristic : Set Nat → Nat → Bool := fun S n => decide (n ∈ S)
  have hc : Function.Injective characteristic := by
    intro S T hST
    ext n
    exact of_decide_eq_decide (congrFun hST n)
  exact Function.cantor_injective (encode ∘ streamTree ∘ characteristic)
    (hinj.comp (streamTree_injective.comp hc))

/-- Arbitrary binary streams have distinct native completed realizations and
actual atomic right subtrees at every left-spine depth. Every such realization
differs from the leafless completion. No countable parameter type can enumerate
the complete native solution domain of the retained definition X = X. -/
theorem free_state_cardinality :
    (∀ s, streamTree s = node (streamTree (tail s)) (leaf (!(s 0)))) ∧
    (∀ s j, subtree (bitAddress j) (streamTree s) = some (leaf (!(s j)))) ∧
    Function.Injective streamTree ∧
    (∀ s, streamTree s ≠ Omega) ∧
    (∀ (A : Type) [Countable A] (decode : A → CompletionTree),
      ¬ Function.Surjective decode) := by
  refine ⟨streamTree_unfold, streamTree_subtree, streamTree_injective,
    streamTree_ne_omega, ?_⟩
  intro A _ decode surj
  exact completed_not_countable surj.countable

#print axioms free_state_cardinality

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFreeStateCardinality
