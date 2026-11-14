# Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Roots.

## Abstract

Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Roots.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/RingTheory/Polynomial/Roots.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

Translation by X+C(a) gives the actual bijection between roots, with inverse subtracting a. Evaluation and composition show both directions and preserve separability. For split inputs the roots of products and gcd are respectively multiset union and multiset intersection; passing to root sets removes multiplicity. Dividing by X-C(a) deletes precisely one occurrence under the original divisibility premise. The derivative-gcd formula subtracts its degree from natDegree to count distinct roots under the original characteristic/separability assumptions. Pinned roots, gcd and composition equations supply these applications; repeated and zero-root branches keep their explicit hypotheses.
