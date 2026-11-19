using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class MetricRangeChartDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous metric-normalized local range products", H("Continuous metric-normalized local range products"), Blocks(
        Describe.Lean(DescribeId.Create("normalized-chart"),
            DeclarationHandle.Create("D5/S3/Geometry/MetricRangeChart.NormalizedChart"), H("Metric-normalized actual linear charts"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("A normalized chart is an actual local linear chart whose reconstruction map pulls the supplied positive range metric back to the fixed Euclidean inner product."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("exists-normalized-chart"),
            DeclarationHandle.Create("D5/S3/Geometry/MetricRangeChart.exists_normalized_chart"), H("Continuous normalization"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("A continuous positive ambient operator that is positive definite on each actual submodule normalizes every actual local chart. Pull the metric back by the chart, take its unique positive square root and compose reconstruction with the inverse square root. The inverse coordinate map uses the square root. Positivity on the actual range proves invertibility locally. All map families and their inverses are continuous on the same open neighborhood.")))),
        Describe.Lean(DescribeId.Create("normalized-chart-disc-homeomorph"),
            DeclarationHandle.Create("D5/S3/Geometry/MetricRangeChart.discHomeomorph"), H("The exact closed disc product"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The actual range-restricted metric disc over a chart neighborhood is homeomorphic to that neighborhood times the closed Euclidean unit ball. The maps are the normalized linear coordinates and reconstruction. The inverse identities and continuity are proved for the entire local product."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("normalized-chart-sphere-homeomorph"),
            DeclarationHandle.Create("D5/S3/Geometry/MetricRangeChart.sphereHomeomorph"), H("The actual sphere product"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The actual range-restricted metric unit sphere has the corresponding local product with the Euclidean unit sphere, using the same normalized linear coordinates and continuous inverse."))), DescribeRole.Definition)) ));
}
