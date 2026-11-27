using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class GraphSubdivisionIntervalsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intervals in ordinary graph subdivisions",
        H("Intervals in ordinary graph subdivisions"),
        Blocks(Describe.Lean(
            DescribeId.Create("graph-subdivision-intervals"),
            DeclarationHandle.Create(
                "D5/S3/Topology/GraphSubdivisionIntervals.graph_subdivision_intervals_oriented"),
            H("Every oriented edge has an interval chart of length two to the subdivision depth"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "A subdivision replaces each path segment by two. Singleton faces and edge faces give the even and odd coordinates. At every depth the chart describes the entire subdivided edge, its endpoints are the retained old vertices, and interior vertices belong to just one chart. Every subdivided face is in a chart or is an isolated old vertex."))),
            DescribeRole.Theorem))));
}
