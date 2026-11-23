using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class LocalMarginalRunningIntersectionDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Quantum/Entanglement/Marginals/LocalMarginalRunningIntersection.finrank_add_adjacentOverlap_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact condition for computing regional partial-trace ranks from adjacent overlaps.",
        H("Local marginal ranks with running intersection"),
        Blocks(
            Describe.Lean(DescribeId.Create("local-marginal-running-intersection"),
                DeclarationHandle.Create(Result), H("Subtract adjacent overlap counts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Consider downward-closed legal binary words on a finite set of sites. "
                    + "For any region, count the ordered legal pairs whose occupied union lies "
                    + "entirely within it. The rank over a field of the collected partial traces "
                    + "plus these counts on adjacent intersections equals the sum of the counts "
                    + "on the individual regions exactly when each site with a legal singleton "
                    + "word occurs in a consecutive block of regions.")),
                    Paragraph(Text(
                    "By the covered-pair rank formula, it suffices to count the union of the "
                    + "sets of pairs supported on each region. When the first region meets the "
                    + "union of the remaining pair sets, its intersection can contain additional "
                    + "pairs beyond those shared with the second region. Equality holds exactly "
                    + "when these intersections coincide at every suffix. Every occupied site "
                    + "of a legal pair has a legal singleton word by downward closure, so "
                    + "consecutive site occurrences ensure consecutive pair occurrences. "
                    + "Conversely, the pair formed by taking a legal singleton word twice "
                    + "detects every interruption in that site's occurrences."))),
                DescribeRole.Theorem))));
}
