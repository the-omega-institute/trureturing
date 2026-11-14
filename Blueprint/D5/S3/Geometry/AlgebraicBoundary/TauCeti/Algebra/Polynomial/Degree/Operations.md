# Pinned real algebraic source: TauCeti.Algebra.Polynomial.Degree.Operations.

## Abstract

Pinned real algebraic source: TauCeti.Algebra.Polynomial.Degree.Operations.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/Degree/Operations.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For n greater than one over the original nontrivial semiring, X^n-X has natural degree n. Pinned natDegree_X_pow and natDegree_sub_eq_left_of_natDegree_lt apply because the degree of X is one. The n=0 and n=1 cancellations are excluded by precisely this inequality, rather than by an implicit generic-degree convention.
