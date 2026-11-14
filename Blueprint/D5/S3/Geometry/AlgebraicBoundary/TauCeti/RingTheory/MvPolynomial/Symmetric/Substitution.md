# Pinned real algebraic source: TauCeti.RingTheory.MvPolynomial.Symmetric.Substitution.

## Abstract

Pinned real algebraic source: TauCeti.RingTheory.MvPolynomial.Symmetric.Substitution.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For a symmetric polynomial on Fin n, pinned MvPolynomial.esymmAlgHom_fin_bijective supplies a polynomial in the elementary symmetric generators. The inverse direction follows from the symmetry of each generator. Substitution through bind and aeval is pinned algebra-hom composition checked on variables. Applying this to a family of symmetric coordinate polynomials gives the same simultaneous parameter polynomial; it does not add an analytic hypothesis or choose separate incompatible tuples.
