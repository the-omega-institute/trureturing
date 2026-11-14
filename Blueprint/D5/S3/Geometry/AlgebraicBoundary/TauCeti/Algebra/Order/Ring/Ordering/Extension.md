# Pinned real algebraic source: TauCeti.Algebra.Order.Ring.Ordering.Extension.

## Abstract

Pinned real algebraic source: TauCeti.Algebra.Order.Ring.Ordering.Extension.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Order/Ring/Ordering/Extension.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For every field K and preordering P, adjoin P a consists of u+a*v with u,v∈P under the original admissibility condition; its ring-cone laws are preordering closure and field normalization. Directed chain union is pinned Subsemiring iSup, and zorn_le_nonempty_Ici₀ gives a maximal preordering. Adjoining any element whose negative is absent proves totality. This base extension supplies exists_linearOrder, with nonnegativity literally membership in the associated ring cone. If the original a can be adjoined, applying the same extension to adjoin P a yields an ordering extending P and containing a. The real-closure proof uses the base extension; no prescribed-element or total-order assumption is imposed on P.
