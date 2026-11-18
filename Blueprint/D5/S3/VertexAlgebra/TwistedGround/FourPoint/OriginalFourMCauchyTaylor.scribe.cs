using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMCauchyTaylorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCauchyTaylor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Taylor coefficients of the original same-puncture free subtraction",
        H("Same-Puncture Cauchy Taylor Coefficients"),
        Blocks(Describe.Lean(DescribeId.Create("fourm-chart-free-correction-coefficient"),
            DeclarationHandle.Create(Prefix + "chart_free_correction_coefficient"),
            H("Taylor coefficient of the chart subtraction"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The analytic binomial roots and the inverse of their sum have the same "
                + "ordinary Taylor coefficients as the regular Laurent-chamber expression. "
                + "Consequently each pair of indices gives the finite lowering contraction "
                + "with its full power of the chart parameter."))), DescribeRole.Theorem))));
}
