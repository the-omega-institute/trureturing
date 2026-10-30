/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeImageSaturationInterface
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact recursive decomposition of unrestricted native image languages. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints

/-! The unrestricted image grammar used by finite-exception saturation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeImageSaturationInterface

open CompletionHomogeneousFixedPoints
open NativeCompletionPrefixLifting

/-- Membership in an actual unrestricted native image. -/
def NativeImage (k : Nat) (X : CompletionTree) : Prop :=
  ∃ Y, rho^[k] Y = X

/-- The image language has exactly its two atomic terminals and its recursive
pair closure.  This is the semantic split used by finite-exception forcing;
it keeps the unrestricted completed domain and does not enumerate finite trees. -/
theorem native_image_iff (k : Nat) (X : CompletionTree) :
    NativeImage k X ↔
      X = atomic k ∨ X = atomic (k + 1) ∨
        ∃ U V, X = node U V ∧ NativeImage k U ∧ NativeImage k V := by
  have leaf_false_iterate :
      rho^[k] (leaf false) = atomic (k + 1) := by
    rw [← rho_alpha]
    simpa [atomic, Function.iterate_succ_apply'] using
      (Function.Commute.iterate_iterate_self rho k 1 (leaf true))
  constructor
  · rintro ⟨Y, rfl⟩
    induction Y using tree_cases with
    | leaf_case b =>
        cases b
        · right
          left
          exact leaf_false_iterate
        · left
          rfl
    | node_case l r =>
        right
        right
        refine ⟨rho^[k] l, rho^[k] r, ?_, ⟨l, rfl⟩, ⟨r, rfl⟩⟩
        exact iterate_node k l r
  · intro h
    rcases h with h | h | ⟨U, V, rfl, hU, hV⟩
    · exact ⟨leaf true, h.symm⟩
    · exact ⟨leaf false, by
        rw [h]
        exact leaf_false_iterate⟩
    · obtain ⟨u, hu⟩ := hU
      obtain ⟨v, hv⟩ := hV
      refine ⟨node u v, ?_⟩
      rw [iterate_node]
      exact congrArg₂ node hu hv

end D5.S3.Arith.FibonacciAtomic.Observer.NativeImageSaturationInterface
