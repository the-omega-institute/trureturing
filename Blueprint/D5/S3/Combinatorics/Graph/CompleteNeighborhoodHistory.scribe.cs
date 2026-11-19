using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class CompleteNeighborhoodHistoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete neighborhood transcripts on finite named simple graphs.",
        H("Replay of complete neighborhood queries"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-neighborhood-history"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/CompleteNeighborhoodHistory.history_eq_iff_extension"),
            H("Edge inclusion and degree saturation characterize replay"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G and H be simple graphs on the same finite vertex set. A fixed "
                    + "deterministic adaptive protocol queries labelled vertices and receives "
                    + "their complete unordered neighbor sets. In the run on H, let F be the "
                    + "graph of all edges returned by the replies.")),
                Paragraph(Text(
                    "The run on G has exactly the transcript of the run on H if and only if "
                    + "G contains F and, at every recorded query, the degree in G is at most "
                    + "the number of neighbors in that reply. The degree comparison occurs "
                    + "only at labels queried in the actual run on H.")),
                Paragraph(Text(
                    "For a candidate containing F, the first recorded neighbor set is "
                    + "contained in the corresponding set in G. Its finite cardinality "
                    + "saturates the upper bound, so the first reply agrees. Induction through "
                    + "the same continuation after that reply gives the complete transcript. "
                    + "Conversely, identical recorded replies supply the edges and the degree "
                    + "bounds.")),
                Paragraph(Text(
                    "For a distribution supported on graphs with the same degree as H "
                    + "at each named vertex, the transcript event coincides with the event "
                    + "that every returned edge is present. Conditioning on a positive-mass "
                    + "transcript is therefore conditioning on that edge-extension event."))),
            DescribeRole.Theorem))));
}
