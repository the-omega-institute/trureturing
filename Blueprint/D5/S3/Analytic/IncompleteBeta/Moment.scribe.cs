using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.IncompleteBeta;

internal sealed class MomentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite convolution and beta moment kernel for incomplete beta coefficients.",
        H("Moment kernel"), Blocks(
            Describe.Lean(DescribeId.Create("incomplete-beta-convolution"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta.convolution"),
                H("Finite coefficient convolution"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The convolution sums products of the Gamma coefficients at complementary indices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incomplete-beta-w"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta.W"),
                H("Symmetric beta kernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite kernel is the sum of the two powered factors divided by the corresponding Gamma factors."))),
                DescribeRole.Definition))));
}
