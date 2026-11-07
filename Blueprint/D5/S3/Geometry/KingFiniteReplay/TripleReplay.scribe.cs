using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KingFiniteReplayTripleReplayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ten literal triple subdivisions", H("The seed and the first ten moves"), Blocks(
        Describe.Lean(DescribeId.Create("triples"),
            DeclarationHandle.Create("D5/S3/Geometry/KingFiniteReplay/TripleReplay.chain10"),
            H("The ten-move chain"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts")),
            Blocks(Paragraph(Text("The actual eleven-vertex seed graph is the complement of graph6 JEhbtj{rve?. Its labels and adjacency agree with the initial edge-list graph. Ten literal triple subdivisions, with exact old and fresh natural labels, form the first ten constructors of the forty-move chain."))),
            DescribeRole.Definition))));
}
