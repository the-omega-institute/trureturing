using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class WeightedFilterLeadingModeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leading exponential in the weighted correction",
        H("The leading exponential in the weighted correction"),
        Blocks(Describe.Lean(
            DescribeId.Create("norm-leading-mode-error-le"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/WeightedFilterLeadingMode.norm_leading_mode_error_le"),
            H("The leading exponential in the weighted correction"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The first Laplace moment bounds the error between the weighted response to a decaying complex mode and the Robin weight times that mode."))),
            DescribeRole.Theorem))));
}
