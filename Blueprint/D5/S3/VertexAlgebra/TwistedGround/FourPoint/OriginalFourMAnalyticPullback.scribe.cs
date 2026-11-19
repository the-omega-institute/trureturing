using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMAnalyticPullbackDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAnalyticPullback.";

    private static DocumentBlock Result(string id, string declaration, string heading, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic half-current Taylor coefficients in the original local coordinates",
        H("Analytic Half-Current Pullback"),
        Blocks(
            Result("fourm-analytic-half-pullback-coefficient", "analytic_half_pullback_coefficient",
                "Taylor coefficient of a half-current pullback",
                "The analytic Taylor remainder shows that the coefficient of the pulled-back "
                + "source uses only the finite binomial creator terms up to its mode."),
            Result("fourm-inverse-physical-source-coefficient", "inverse_physical_source_coefficient",
                "Taylor coefficient in the original inverse coordinate",
                "At each physical puncture the chosen lift gives the inverse scale at the full "
                + "incoming doubled oscillator degree. Each lower mode carries the corresponding "
                + "power of the negative lowering parameter."))));
}
