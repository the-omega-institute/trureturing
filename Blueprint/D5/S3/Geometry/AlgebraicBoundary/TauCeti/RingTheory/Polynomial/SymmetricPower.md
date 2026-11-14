# Pinned real algebraic source: TauCeti.RingTheory.Polynomial.SymmetricPower.

## Abstract

Pinned real algebraic source: TauCeti.RingTheory.Polynomial.SymmetricPower.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/RingTheory/Polynomial/SymmetricPower.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For an n-element multiset s, toMonic s is the product of X-C(a) over its entries, including the empty product one; append, cons and repeated entries give multiplication, a linear factor and its powers. Coefficientwise equality recovers the monic polynomial and its multiset of roots with the original splitting hypotheses. The coefficient chart deletes the monic leading term and records the n lower coefficients, with inverse X^n plus that coefficient sum. Elementary symmetric coordinate j has sign (-1)^(j+1) and reversed coefficient index. Pinned symmetric-polynomial bijectivity and aeval/rename composition therefore express every symmetric root operation as a polynomial in these coefficients. The actual forward chart, norm bound, cocompact properness and nearby tuple matching remain the continuous common-root route, including n=0 and repeated roots; analytic or open-embedding readouts are separate applications.

## References

- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/Data/Sym/Basic](../../Data/Sym/Basic.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/MvPolynomial/Symmetric/Substitution](../MvPolynomial/Symmetric/Substitution.md)
- Dependency: [D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Monic/OfCoeff](Monic/OfCoeff.md)
