using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class PositiveAverageCosineWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite signs from compact probability averages",
        H("Opposite signs from compact probability averages"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-signed-values"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/PositiveAverageCosineWindow.exists_signed_values"),
            H("Opposite signs from compact probability averages"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("If the probability averages stay within half the cosine amplitude, a window containing a full period and the forward support contains a raw value of each sign. The measures may vary with the base point."))),
            DescribeRole.Theorem))));
}
