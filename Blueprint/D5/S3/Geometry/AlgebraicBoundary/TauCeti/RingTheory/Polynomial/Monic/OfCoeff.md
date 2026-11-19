# Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Monic.OfCoeff.

## Abstract

Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Monic.OfCoeff.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/RingTheory/Polynomial/Monic/OfCoeff.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

monicOfCoeff c is X^n plus the sum of the lower coefficient monomials. Evaluation is therefore x^n plus that finite coefficient sum, coefficient maps act coordinatewise, and equality of these monic polynomials is equality of all lower coefficients. Pinned Polynomial.coeff_sum, coeff_monomial, eval_add and eval_finset_sum prove all three identities, including n=0.
