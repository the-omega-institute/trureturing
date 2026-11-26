using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent;

internal sealed class Q9LaurentTransverseFibersDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Owner = Boundary + "Laurent/Q9LaurentTransverseFibers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Neighbor partitions stay constant on transverse paths.",
        H("Shared-triple deletion and transverse fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-laurent-transverse-partition"),
                DeclarationHandle.Create(Owner + "neighborPartition_eq_of_transverse_path"),
                H("Neighbor partitions stay constant on transverse paths"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After deleting edges in the common triple, every two-step move retains a nonshared block. Two distinct realized partitions have only the deleted block in common, so the partition is constant along the resulting paths."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Laurent/Q9LaurentDirectionTypes")),
         DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Laurent/Q9LaurentCommonTriple"))]));
}
