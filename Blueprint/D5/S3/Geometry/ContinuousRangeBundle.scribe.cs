using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class ContinuousRangeBundleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real bundles on actual continuously varying subspaces", H("Real bundles on actual continuously varying subspaces"), Blocks(
        Describe.Lean(DescribeId.Create("chart"),
            DeclarationHandle.Create("D5/S3/Geometry/ContinuousRangeBundle.Chart"), H("Actual local linear coordinates"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("A chart consists of an open base set, forward maps into the actual submodules and backward maps from the ambient Euclidean space. Both map families are continuous on the open set. Both inverse laws hold on that set. This is constructed local data, not an additional premise of the projection-range theorem."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("exists-chart"),
            DeclarationHandle.Create("D5/S3/Geometry/ContinuousRangeBundle.exists_chart"), H("Projection continuity constructs charts"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For a family of actual real submodules of fixed finite rank, continuity of their orthogonal projections constructs a chart neighborhood at every base point. Project a fixed basis of the reference fiber. Injectivity is open. The projected maps remain injective on a neighborhood; equality of dimensions gives equality with the whole actual range. Their invertible Gram operators give continuous coordinate inverses.")))),
        Describe.Lean(DescribeId.Create("prebundle"),
            DeclarationHandle.Create("D5/S3/Geometry/ContinuousRangeBundle.prebundle"), H("The genuine real vector prebundle"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("All constructed local linear coordinates form a VectorPrebundle on the actual submodules. The overlap map is the second chart coordinate map composed with the first chart reconstruction map, and is continuous in operator norm. The standard VectorPrebundle construction provides the real vector bundle."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("topology-eq-induced"),
            DeclarationHandle.Create("D5/S3/Geometry/ContinuousRangeBundle.topology_eq_induced"), H("Exactly the ambient range graph topology"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The generated bundle topology equals the topology induced by the actual inclusion into X times H. Local reconstruction proves continuity of the ambient inclusion, and local coordinates prove continuity of the inverse from the range graph. This is equality of total topologies, not only pointwise agreement of fiber topologies."))))) ));
}
