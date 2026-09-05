using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class DiagonalSignNegativeIndexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inertia of a real diagonal Hermitian form is exactly its coordinate sign count.",
        H("Diagonal Sign Inertia"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("real-diagonal"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/DiagonalSignNegativeIndex.realDiagonal"),
                H("Real diagonal Hermitian form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Real coefficients are embedded as the diagonal entries of a complex Hermitian matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-weight-count"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/DiagonalSignNegativeIndex.positiveWeightCount"),
                H("Positive coordinate count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This finite count records diagonal entries that are strictly positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("negative-weight-count"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/DiagonalSignNegativeIndex.negativeWeightCount"),
                H("Negative coordinate count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This finite count records diagonal entries that are strictly negative."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("real-diagonal-inertia-eq-sign-counts"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/DiagonalSignNegativeIndex.real_diagonal_inertia_eq_sign_counts"),
                H("Diagonal inertia equals coordinate sign counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Coordinate projectors give lower bounds for both signs, and the rank partition forces both bounds to be equalities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-diagonal-negative-index"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/DiagonalSignNegativeIndex.real_diagonal_negIndex_eq_negative_count"),
                H("Diagonal negative index counts negative weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The negative component of the inertia package is exposed as a direct consumer theorem."))),
                DescribeRole.Theorem)
        ),
        []));
}
