using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphLargeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict event counting supplies AR-labelings of large cubic graphs.",
        H("The large cubic graph construction"),
        Blocks(Describe.Lean(DescribeId.Create("large-cubic-ar-labeling"),
            DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphLarge.ar_graph_large"),
            H("An AR-labeling with the exact interval of labels"),
            StatementSource.FromAuthor(Disp(Seq(
                Call("Cubic", F.Id("G")), Sp, Land, Sp, D(1, 2), Sp, Le, Sp,
                Call("EdgeCount", F.Id("G")), Sp, Implies, Sp,
                Call("IsARGraph", F.Id("G"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every finite simple cubic graph having at least twelve edges, there "
                + "is an AR-labeling onto the integer interval from one through the edge count. "
                + "Choose a vertex v and two of its incident edges p and q, with opposite "
                + "endpoints u and w. Simplicity makes v,u,w distinct. Give p and q the labels "
                + "one and two. Enumerate every vertex's three incident edges, placing both "
                + "marks first at v and the respective mark first at u and w. All other "
                + "vertices have three free edges. The cardinalities of their additive "
                + "collision events satisfy the four corresponding marked-event bounds. "
                + "The cubic degree-sum identity supplies the arithmetic hypothesis making "
                + "the sum of these bounds strictly smaller than the marked sample space. "
                + "An outcome avoiding every collision is the required exact AR-labeling."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphEvents"))]));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
