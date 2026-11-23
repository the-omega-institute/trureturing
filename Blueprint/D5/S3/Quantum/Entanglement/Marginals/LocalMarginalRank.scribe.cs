using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class LocalMarginalRankDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Quantum/Entanglement/Marginals/LocalMarginalRank.finrank_marginalMap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rank of collected binary marginals with downward-closed support.",
        H("Rank of local marginals on legal binary words"),
        Blocks(
            Describe.Lean(DescribeId.Create("local-marginal-rank"),
                DeclarationHandle.Create(Result), H("Covered ordered pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A legal word is a subset of a finite site set. Assume any subset of a legal "
                    + "word is legal. Take matrix entries over a field, indexed by ordered legal "
                    + "word pairs, and an arbitrary family of measured regions. A regional "
                    + "partial trace sums entries whose words agree outside that region and have "
                    + "the specified restrictions inside it. The rank of the collected map equals "
                    + "the number of ordered legal pairs whose union lies in a measured region.")),
                    Paragraph(Text(
                    "At a pair, form a coordinate by keeping the words fixed on their union "
                    + "and summing over simultaneous added occupancies outside that union. "
                    + "The resulting change of coordinates is triangular with diagonal entry one. "
                    + "Applying a regional trace preserves this coordinate when the region "
                    + "contains the union and sends it to zero otherwise. The two-step sum "
                    + "groups terms by the unique restrictions to the region, which remain "
                    + "legal by downward closure. The collected traces therefore have the same "
                    + "kernel as the projection onto all covered coordinates."))),
                DescribeRole.Theorem))));
}
