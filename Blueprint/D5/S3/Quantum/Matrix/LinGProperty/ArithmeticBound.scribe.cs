using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinGProperty;

internal sealed class ArithmeticBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic spectral bound retains the deficit in the normalized block overlap.",
        H("The trace-corrected arithmetic bound"), Blocks(
            Describe.Lean(DescribeId.Create("normalized-arithmetic-bound"),
                DeclarationHandle.Create(Owner + "normalized_arithmetic_bound"),
                H("An indexed arithmetic bound with trace deficit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(
                    Paragraph(Text("Let [A X; X-adjoint B] be positive semidefinite, with tr A=tr B=1. Every decreasingly ordered singular value satisfies 2 s_j(X) <= lambda_j(A+B)+1-|tr X|. All finite dimensions and singular blocks are included.")),
                    Paragraph(Text("A unit phase makes the trace of X real and nonnegative without changing block positivity or any singular value. The Hermitian dilation [0 X; X-adjoint 0] has leading eigenvalues s_j(X). An explicit similarity from a singular value decomposition proves this identity, while Loewner monotonicity compares twice this dilation with the original positive block matrix.")),
                    Paragraph(Text("Write the positive block matrix as Z Z-adjoint and partition its rows into U and V. Its eigenvalues agree with those of U-adjoint U+V-adjoint V. The latter matrix is one half of the sum Gram plus one half of the difference Gram. A positive matrix is bounded above by its trace times the identity, so the difference Gram contributes exactly 1-Re tr X.")),
                    Paragraph(Text("The leading eigenvalues of rectangular row and column Grams agree after zero padding. Finally, the row sum Gram (U+V)(U+V)-adjoint is bounded above by 2(A+B). Combining these comparisons gives the indexed inequality."))),
                DescribeRole.Theorem))));
}
