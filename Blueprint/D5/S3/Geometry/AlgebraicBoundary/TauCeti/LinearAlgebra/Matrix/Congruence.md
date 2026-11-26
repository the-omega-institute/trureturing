# Pinned real algebraic source: TauCeti.LinearAlgebra.Matrix.Congruence.

## Abstract

Pinned real algebraic source: TauCeti.LinearAlgebra.Matrix.Congruence.

This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/LinearAlgebra/Matrix/Congruence.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.

Deleting rows and columns through submatrices of the identity is exactly Matrix.submatrix multiplication, under the original NonAssocSemiring hypotheses. For a commutative coefficient ring, trace of a congruence is the finite diagonal sum after expanding matrix multiplication. The rank-one determinant formula det(1+r vvᵀ)=1+r(vᵀv), and its minus version, are pinned determinant-update identities after the same entrywise multiplication. No invertibility or positivity assumption is inferred from this algebraic normalization.
