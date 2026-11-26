# Pinned real algebraic source: TauCeti.Data.Fintype.Fiber.

## Abstract

Pinned real algebraic source: TauCeti.Data.Fintype.Fiber.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Data/Fintype/Fiber.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For any types X,S and f:X→S, the occurrence count at y is Nat.card {x | f x=y}. With Fintype X it is the finite filter cardinality and the sum of equality indicators. A value-preserving embedding induces an embedding of these fibers, and if it misses a target occurrence it gives strict cardinal inequality under the original finite-fiber assumption. Fin.cases and Fin.lastCases split off the first or last index. For a finite family and commutative multiplicative weights, grouping the product by its value gives ∏y w(y)^count(y); its additive form weights by natural scalar multiplication. Pinned Finset.sum_fiberwise_of_maps_to' gives the constant-weight total equal to card X. For finite types, equal counts supply the actual commuting permutation by Equiv.ofFiberEquiv; no order, injectivity or simple-root premise is implicit.
