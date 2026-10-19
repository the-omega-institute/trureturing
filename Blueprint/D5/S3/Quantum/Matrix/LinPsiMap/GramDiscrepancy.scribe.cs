using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinPsiMap;

internal sealed class GramDiscrepancyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinPsiMap/GramDiscrepancy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Loewner bound on Gram discrepancy yields an indexed singular-value estimate.",
        H("The Gram-discrepancy spectral estimate"), Blocks(
            Describe.Lean(DescribeId.Create("lin-gram-discrepancy-bound"),
                DeclarationHandle.Create(Owner + "gram_discrepancy_bound"),
                H("An indexed spectral estimate from discrepancy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016psimap")),
                Blocks(
                    Paragraph(Text("For a positive semidefinite block matrix [P Y; Y-adjoint Q], assume P+Q−Y−Y-adjoint is at most delta I in Loewner order, with delta nonnegative. Then every decreasing singular value satisfies 2 s_j(Y) <= lambda_j(P+Q)+delta/2. The statement includes singular matrices and repeated eigenvalues.")),
                    Paragraph(Text("In a Gram factorization, write the row blocks as U and V and put F=U+V and E=U−V. The discrepancy is E E-adjoint. Its scalar identity bound also bounds E-adjoint E. The full column Gram is one half F-adjoint F plus one half E-adjoint E, while F F-adjoint is at most twice P+Q.")),
                    Paragraph(Text("The existing row-column Gram spectral correspondence and eigenvalue monotonicity bound the leading eigenvalues of the original block. Its signed off-diagonal dilation is bounded by that positive block and has leading eigenvalues twice the singular values of Y. Combining the comparisons gives the stated estimate."))),
                DescribeRole.Theorem))));
}
