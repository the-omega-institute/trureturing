using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class WeightedFilterStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stability of the corrected average under a decaying remainder",
        H("Stability of the corrected average under a decaying remainder"),
        Blocks(Describe.Lean(
            DescribeId.Create("abs-laplace-sub-re-response-le"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/WeightedFilterStability.abs_laplace_sub_re_response_le"),
            H("Stability of the corrected average under a decaying remainder"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A decaying real remainder in the averaged unweighted primitive contributes at most twice its initial envelope times the Robin weight."))),
            DescribeRole.Theorem))));
}
