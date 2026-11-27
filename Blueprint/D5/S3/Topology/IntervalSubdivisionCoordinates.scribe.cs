using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class IntervalSubdivisionCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinates along subdivided edges",
        H("Coordinates along subdivided edges"),
        Blocks(Describe.Lean(
            DescribeId.Create("intervalsubdivisioncoordinates-result"),
            DeclarationHandle.Create("D5/S3/Topology/IntervalSubdivisionCoordinates.iterate_eq_chart_index"),
            H("Coordinates along subdivided edges"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Iterating the interval coordinate recovers the index of a graph subdivision chart when the old edge is oriented from zero to one."))),
            DescribeRole.Theorem))));
}
