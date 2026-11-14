using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_LinearAlgebra_Matrix_CornerMinorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.LinearAlgebra.Matrix.CornerMinor.",
        H("Pinned real algebraic source: TauCeti.LinearAlgebra.Matrix.CornerMinor."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/LinearAlgebra/Matrix/CornerMinor.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("Delete the last coordinate by the rectangular submatrix of the identity and include it by its transpose-shaped counterpart. Under Zero and One these have Kronecker-delta entries; under NonAssocSemiring their products with a matrix are the prescribed row/column deletions. Replacing the identity last row by w or last column by u gives framing matrices whose corner is the identity. If wA=0 and Au=0 these frames factor A through the corner index Fin n. Over a commutative ring, pinned Matrix.det_succ_row gives the sparse last-row determinant as its corner entry times the corner minor; transpose gives the column formula, including n=0. The frame determinants are their last entries. For a conjugating matrix fixing u and w with the original unit last-coordinate conditions, determinant multiplicativity cancels the two frame factors and the conjugating determinant, proving equality of corner minors. Replacing the last column by a basis vector or a stated linear combination is the corresponding determinant linearity application. The retained sparse-row lemma remains the actual coefficient-minor step.")))));
}
