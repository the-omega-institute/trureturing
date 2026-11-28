using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class GraphSubdivisionPositionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric positions on graph subdivisions",
        H("Geometric positions on graph subdivisions"),
        Blocks(Describe.Lean(
            DescribeId.Create("graphsubdivisionpositions-result"),
            DeclarationHandle.Create("D5/S3/Topology/GraphSubdivisionPositions.exists_positions"),
            H("Geometric positions on graph subdivisions"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Each vertex of an ordinary graph subdivision has a compatible position in the simplex of its original support. The diameter of a subdivided face is at most the dyadic mesh in each coordinate."))),
            DescribeRole.Theorem))));
}
