using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class LocalMarginalRunningIntersectionDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Quantum/Entanglement/Marginals/LocalMarginalRunningIntersection.finrank_add_adjacentOverlap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ranks for ordered families of regional partial traces with running intersection.",
        H("Local marginal ranks with running intersection"),
        Blocks(
            Describe.Lean(DescribeId.Create("local-marginal-running-intersection"),
                DeclarationHandle.Create(Result), H("Subtract adjacent overlap counts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Consider downward-closed legal binary words on a finite set of sites. "
                    + "Order the measured regions so that each site's occurrences are consecutive. "
                    + "For any region, count the ordered legal pairs whose occupied union lies "
                    + "entirely within it. The rank over a field of the collected partial traces "
                    + "plus these counts on adjacent intersections equals the sum of the counts "
                    + "on the individual regions.")),
                    Paragraph(Text(
                    "By the covered-pair rank formula, it suffices to count the union of the "
                    + "sets of pairs supported on each region. The pairs supported on the first "
                    + "region that also occur in a later region are exactly those supported on "
                    + "the intersection with the second region. Indeed, every site of such a pair "
                    + "must occur in the second region by running intersection. Removing the "
                    + "first region and repeating the argument charges each adjacent overlap once."))),
                DescribeRole.Theorem))));
}
