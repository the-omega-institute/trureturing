/- GID: D5/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Four-message window computation forces complementary peeling spines. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.Arith.FibonacciAtomic.TreeMessageRealization

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FourMessageTreeRigidity

open TreeMessageRealization
open FirstRejectionCutCapacity (interval boolean d epsilon crossings internals Cross Internal left right)
open LiteralWindowEnd (Window)
open D5.S3.Observer.Separation.SurjectiveColumnSharpWidth (capacity)

/-- Global proper prefixes, global proper suffixes, and internal singleton blocks. -/
def SmallBlock {k : ℕ} (A : Finset (Fin (k+1))) : Prop :=
  (∃ j, 0 < j ∧ j < k+1 ∧ A = interval k 0 j) ∨
  (∃ j, 0 < j ∧ j < k+1 ∧ A = interval k j (k+1)) ∨
  (∃ i : Fin (k+1), 0 < i.val ∧ i.val < k ∧ A = {i})

/-- A prefix spine peels its highest remaining coordinate at each fork.
The two constructors allow the actual children to be exchanged independently. -/
inductive PrefixSpine (k : ℕ) : ℕ → Tree (Fin (k+1)) → Prop
  | one : PrefixSpine k 1 (leaf ⟨0, Nat.zero_lt_succ k⟩)
  | peel {j : ℕ} {t : Tree (Fin (k+1))} (hj : j < k+1)
      (h : PrefixSpine k j t) : PrefixSpine k (j+1) (fork t (leaf ⟨j,hj⟩))
  | peel_swap {j : ℕ} {t : Tree (Fin (k+1))} (hj : j < k+1)
      (h : PrefixSpine k j t) : PrefixSpine k (j+1) (fork (leaf ⟨j,hj⟩) t)

/-- A suffix spine peels its lowest remaining coordinate at each fork. -/
inductive SuffixSpine (k : ℕ) : ℕ → Tree (Fin (k+1)) → Prop
  | one : SuffixSpine k k (leaf (Fin.last k))
  | peel {j : ℕ} {t : Tree (Fin (k+1))} (hj : j < k)
      (h : SuffixSpine k (j+1) t) : SuffixSpine k j (fork (leaf ⟨j,by omega⟩) t)
  | peel_swap {j : ℕ} {t : Tree (Fin (k+1))} (hj : j < k)
      (h : SuffixSpine k (j+1) t) : SuffixSpine k j (fork t (leaf ⟨j,by omega⟩))

/-- Exact child-swap freedom at all forks is built into the two spine predicates. -/
def DoubleComb {k : ℕ} (t : Tree (Fin (k+1))) : Prop :=
  ∃ j, 0 < j ∧ j < k+1 ∧ ∃ l r, PrefixSpine k j l ∧ SuffixSpine k j r ∧
    (t = fork l r ∨ t = fork r l)

end D5.S3.Arith.FibonacciAtomic.FourMessageTreeRigidity
