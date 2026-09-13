using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WeightedCapacity;

internal sealed class SummabilityContinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Summability and continuity of weighted dyadic readout.",
        H("Summability and continuity of weighted dyadic readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("summabilitycontinuity-divergent-capacity-tail-mass"),
                DeclarationHandle.Create("D5/S3/Analytic/WeightedCapacity/SummabilityContinuity.divergent_capacity_tail_mass"),
                H("Divergent capacity leaves mass in every finite tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the total dyadic capacity is infinite, every finite set of coordinates has a "
                    + "disjoint finite complement carrying at least one unit of weighted mass."))),
                DescribeRole.Theorem))));
}
