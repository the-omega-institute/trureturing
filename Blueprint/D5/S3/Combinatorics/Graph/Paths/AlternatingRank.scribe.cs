using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Paths;

internal sealed class AlternatingRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Boolean edge word selects a spanning subgraph of a path over the binary field.",
        H("Alternating path ranks"),
        Blocks(Paragraph(Text("The path has n+1 distinct vertices and n possible edges between consecutive vertices. Each Boolean word selects the edges with value true. The adjacency matrix is symmetric with zero diagonal over ZMod 2. The alternating rank sum uses integer signs, so the signs do not disappear in characteristic two.")))));
}
