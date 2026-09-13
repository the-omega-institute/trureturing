using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WeightedCapacity;

internal sealed class SummabilityContinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Summability and continuity of weighted dyadic readout.",
        H("Summability and continuity of weighted dyadic readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("summabilitycontinuity-summable-iff-continuous"),
                DeclarationHandle.Create("D5/S3/Analytic/WeightedCapacity/SummabilityContinuity.summable_iff_continuous"),
                H("Finite capacity and continuous real extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every capacity function, finite total dyadic mass is equivalent to continuity "
                    + "of the finite-support readout at zero, to its continuity everywhere, and to "
                    + "the existence of a continuous real extension to the full coordinate product."))),
                DescribeRole.Theorem))));
}
