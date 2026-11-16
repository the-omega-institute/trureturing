using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.KingFiniteReplay;

internal sealed class KingFiniteReplayDataLozinThirdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal finite graph states 26 through 30", H("Literal finite graph states 26 through 30"), Blocks(
        Describe.Lean(DescribeId.Create("states"),
            DeclarationHandle.Create("D5/S3/Geometry/KingFiniteReplay/DataLozinThird.graph26"),
            H("Exact finite edge-list graphs"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts")),
            Blocks(Paragraph(Text("The literal finite natural-labeled vertex and edge lists specify states 26 through 30 of the forty suspension moves. Every cached adjacency row is proved equal to the row computed from its actual edge list. The graph definition uses that original list."))),
            DescribeRole.Definition))));
}
