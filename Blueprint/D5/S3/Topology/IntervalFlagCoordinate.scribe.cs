using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class IntervalFlagCoordinateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinates of interval faces",
        H("Coordinates of interval faces"),
        Blocks(Describe.Lean(
            DescribeId.Create("intervalflagcoordinate-result"),
            DeclarationHandle.Create("D5/S3/Topology/IntervalFlagCoordinate.list_coordinate"),
            H("Coordinates of interval faces"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Taking the least and greatest indices of a nonempty interval face and adding them gives its coordinate in the bisected interval. Duplicate list entries give the same coordinate."))),
            DescribeRole.Theorem))));
}
