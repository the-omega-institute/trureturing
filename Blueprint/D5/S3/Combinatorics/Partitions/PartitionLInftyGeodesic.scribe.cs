using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class PartitionLInftyGeodesicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/PartitionLInftyGeodesic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-mass antitone partition vectors admit shortest coordinate-confined paths in the d-infinity metric, and every unit-step path has at least that many steps.",
        H("Endpoint-confined geodesics of partitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partition-l-infty-geodesic-result"),
                DeclarationHandle.Create(Prefix + "partition_lInf_geodesic"),
                H("A shortest path between partitions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every n and every pair of partitions λ and μ of n, let d∞(λ, μ) be the maximum coordinate difference. There is a path of exactly d∞(λ, μ) adjacent steps through partitions of n. Every coordinate of every vertex lies between the corresponding coordinates of λ and μ. The displayed greedy algorithm starts at the source and, at each of the d∞ steps, fills the source-defined lower bounds from the smallest index up to the source-defined upper bounds; its output is such a path and has the same confinement properties. Conversely, any path through partitions of n whose adjacent steps have d∞ at most one has at least d∞(λ, μ) steps."))),
                DescribeRole.Theorem)),
        []));
}
