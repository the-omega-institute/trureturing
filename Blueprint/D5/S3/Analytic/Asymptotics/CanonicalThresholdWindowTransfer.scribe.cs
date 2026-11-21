using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class CanonicalThresholdWindowTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite limits on two integer grids",
        H("Opposite limits on two integer grids"),
        Blocks(Describe.Lean(
            DescribeId.Create("threshold-grids-of-two-signed-samplings"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/CanonicalThresholdWindowTransfer.threshold_grids_of_two_signed_samplings"),
            H("Opposite limits on two integer grids"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Uniform sampling carries signed tail excursions into fixed power thresholds. Two increasing enumerations yield opposite infinite limits for the specified weighted margins."))),
            DescribeRole.Theorem))));
}
