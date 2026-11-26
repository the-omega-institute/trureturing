# Pinned real algebraic source: TauCeti.Algebra.Polynomial.Eval.Sign.

## Abstract

Pinned real algebraic source: TauCeti.Algebra.Polynomial.Eval.Sign.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/Eval/Sign.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For the original ordered ring homomorphism f and every polynomial p and evaluation point x, evaluation of the mapped polynomial at f(x) is f(p(x)). Pinned Polynomial.eval₂_at_apply and order-compatible sign transport identify the two signs. The order preservation condition belongs to f; it is not inferred from a bare coefficient map.
