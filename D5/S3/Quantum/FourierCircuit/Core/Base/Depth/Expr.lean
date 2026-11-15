/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Depth/Expr
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Depth/Expr
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Quantum/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Core/Base/Depth/Expr.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod

/-!
# Formal circuit-history expressions with cost and depth evaluators

`DepthExpr U` is a syntactic construction tree for a circuit whose atoms carry a
symbolic *resource unit* drawn from a label type `U` (units are symbolic labels,
never matrices).  It mirrors the shape of a circuit construction history:
identity, a unit-labelled atom, sequential and parallel (tensor) composition,
inverse, a controlled block, a fixed repetition (`iterate`), and an indexed
finite product of blocks.

The indexed product keeps its step blocks as a genuine index family
`step : Fin count → DepthExpr U` rather than as a list.  With this shape each
`step j` is a structural subterm, so both evaluators below are accepted by
Lean's structural recursion with no auxiliary termination measure, every
defining equation holds by `rfl` (hence the constructor `simp` lemmas and closed
`decide`/`rfl` computations), and the default `induction` principle exposes the
per-index hypothesis `∀ j, motive (step j)` directly.

Two evaluators interpret the *same* tree, differing only in how parallel
composition combines its branches:

* `costEval` is **linear**: it aggregates a per-unit weight `assign : U → M`
  into any additive commutative monoid `M`.  Sequential and parallel
  composition both add, `iterate n` scales by `n`, an indexed product sums its
  start block and all of its step blocks, and `inverse`/`controlled` pass their
  body through unchanged.  This is the total-work reading.
* `depthEval` is **max-plus** over `ℕ`: sequential composition adds, but
  parallel composition takes the `max`; `iterate n` multiplies by `n`; an
  indexed product — a sequential composition of its steps — adds; `inverse` and
  `controlled` pass through.  This is the critical-path reading.

The pass-through readings of `inverse` and `controlled` are the neutral
baseline; a genuine control-cost transform is a separate refinement.

`queryDepthEval focus` reads the **query depth** relative to a distinguished unit
`focus`: it is `depthEval` under the indicator weight sending `focus` to `1` and
every other unit to `0`, so it counts the longest sequential chain of focus-unit
occurrences and discounts everything else.
-/

section

namespace QuantumAlg

open scoped BigOperators
ount : Nat) (start : DepthExpr U)
      (step : Fin count → DepthExpr U)

namespace DepthExpr

variable {U : Type} {M : Type} [AddCommMonoid M]
 start + ∑ j, costEval assign (step j)
start + ∑ j, depthEval assign (step j)
l
 : U) :
    costEval assign (.atom u) = assign u := rfl
l assign (.seq l r) = costEval assign l + costEval assign r := rfl
l assign (.tensor l r) = costEval assign l + costEval assign r := rfl
xpr U) :
    costEval assign (.inverse b) = costEval assign b := rfl
costEval assign b := rfl
xpr U) :
    costEval assign (.iterate count b) = count • costEval assign b := rfl
   costEval assign start + ∑ j, costEval assign (step j) := rfl
l
 : U) :
    depthEval assign (.atom u) = assign u := rfl
 assign (.seq l r) = depthEval assign l + depthEval assign r := rfl
n (.tensor l r) = max (depthEval assign l) (depthEval assign r) := rfl
pr U) :
    depthEval assign (.inverse b) = depthEval assign b := rfl
epthEval assign b := rfl
pr U) :
    depthEval assign (.iterate count b) = count * depthEval assign b := rfl
  depthEval assign start + ∑ j, depthEval assign (step j) := rfl
set.sum_le_sum fun index _ => stepLe index)
: U) : U → ℕ :=
  fun u => if u = focus then 1 else 0
s focus = 1 := by
  simp [indicator]
 = 0 := by
  simp [indicator, h]
 U] (focus : U) (e : DepthExpr U) : ℕ :=
  depthEval (indicator focus) e
s (.atom focus) = 1 := by
  simp [queryDepthEval]
0 := by
  simp [queryDepthEval, indicator, h]

      exact Nat.add_le_add ihs (Finset.sum_le_sum fun j _ => ihf j)

/-- A two-layer circuit of parallel pairs.  Two `H`/`H` tensor layers composed in
sequence have linear cost `4` (every atom counts) but max-plus depth `2` (each
parallel branch shares a layer), so the critical path is strictly shorter than
the total work. -/
example :
    costEval (fun _ : String => (1 : ℕ))
      (.seq (.tensor (.atom "H") (.atom "H")) (.tensor (.atom "H") (.atom "H"))) = 4 := by
  decide

example :
    depthEval (fun _ : String => 1)
      (.seq (.tensor (.atom "H") (.atom "H")) (.tensor (.atom "H") (.atom "H"))) = 2 := by
  decide

/-- Query-depth projection reads the number of sequential focus-unit occurrences.
With unit `0` the queried unit and unit `1` any other, running one hundred
sequential queries in parallel with a seven-fold non-queried repetition has query
depth `100`: the parallel branch is discounted by the `max`. -/
example : queryDepthEval (0 : ℕ)
    (.tensor (.iterate 100 (.atom 0)) (.iterate 7 (.atom 1))) = 100 := by
  decide

/-- A worked indexed-product cost: a start identity followed by three unit-`0`
atoms, each of weight `1`, has linear cost `3`. -/
example : costEval (fun _ : ℕ => (1 : ℕ))
    (.indexedProduct "product" 3 .id (fun _ => .atom 0)) = 3 := by
  simp

end DepthExpr

end QuantumAlg

end
