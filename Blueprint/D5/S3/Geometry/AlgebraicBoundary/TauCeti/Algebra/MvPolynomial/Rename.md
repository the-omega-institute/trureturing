# Pinned real algebraic source: TauCeti.Algebra.MvPolynomial.Rename.

## Abstract

Pinned real algebraic source: TauCeti.Algebra.MvPolynomial.Rename.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/MvPolynomial/Rename.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

For an injective variable map, the rename homomorphism has the coefficientwise inverse on its range given by killCompl; the two RingHom inverse-pair records assert exactly the generator equations. Outside the range, a variable is sent to zero. For every commutative coefficient ring, vanishing after killing a distinguished variable is equivalent to divisibility by that variable: split a polynomial into its constant coefficient and the variable multiple through the polynomial-variable equivalence. Pinned MvPolynomial rename, aeval and polynomial X-divisibility equations give both implications without a domain or nonzero premise.
