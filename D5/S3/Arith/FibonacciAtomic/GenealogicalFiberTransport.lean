/- GID: D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordered source fibers and injective Fibonacci genealogical transport. -/

import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import D5.S3.TotalVariation.Pinsker
import Mathlib.Algebra.Free
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Data.Finset.Powerset
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport

open scoped BigOperators
open GraftAffineClosure (step quantity)

/-- Actual nonempty ordered binary trees; true labels alpha and false labels beta. -/
abbrev Source := FreeMagma Bool

/-- Leaf substitution, extended by the universal property of the free magma. -/
def substitution : Source →ₙ* Source :=
  FreeMagma.lift fun b => if b then .of false else .mul (.of false) (.of true)

/-- Numbers of alpha and beta leaves. -/
def composition : Source → ℕ × ℕ
  | .of true => (1, 0)
  | .of false => (0, 1)
  | .mul s t => composition s + composition t

/-- A fiber is a subset of the actual source algebra. -/
def Fiber (v : ℕ × ℕ) := {t : Source // composition t = v}

/-- The Catalan and binomial expression for a composition fiber. -/
def fiberCount (v : ℕ × ℕ) : ℕ :=
  catalan (v.1 + v.2 - 1) * Nat.choose (v.1 + v.2) v.1

#check FreeMagma.lift
#check FreeMagma.hom_ext
#check FreeMagma.length
#check FreeMagma.rec
#check BinaryTree.treesOfNumNodesEq_card_eq_catalan
#check BinaryTree.mem_treesOfNumNodesEq
#check catalan_eq_centralBinom_div
#check succ_mul_catalan_eq_centralBinom
#check Finset.card_powersetCard
#check Nat.choose_symm_add
#check Nat.choose_le_add
#check PMF.uniformOfFinset
#check Nat.fib_mono
#check Nat.le_fib_add_two
#check Fin.sum_univ_add
#check Fin.addCases
#check Fin.addCases_left
#check Fin.addCases_right

end D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
