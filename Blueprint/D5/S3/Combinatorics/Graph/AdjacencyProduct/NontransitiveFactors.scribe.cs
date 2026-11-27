using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.AdjacencyProduct;

internal sealed class NontransitiveFactorsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/akbari2025primematrixproduct");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete graph on 17 vertices has an ordinary integer adjacency-matrix factorization with both factors non-vertex-transitive.",
        H("Non-vertex-transitive adjacency factors"),
        Blocks(Describe.Lean(
            DescribeId.Create("nontransitive-factors"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/AdjacencyProduct/NontransitiveFactors.result"),
            H("Two non-vertex-transitive factors of the complete graph"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Section 5, item 2 of Akbari, Elahimanesh and Miraftab asks for two non-transitive graphs H and K whose adjacency matrices B and C satisfy BC = J − I. The two graphs share the labelled vertex set Fin 17. A(G) is the integer adjacency matrix, J has every entry equal to one, I is the identity, and the product is ordinary matrix multiplication. VT(G) means that for every two vertices there is a graph automorphism sending the first vertex to the second.")),
                Paragraph(Text("The two graphs are defined by literal neighbor lists. The kernel checks symmetry, looplessness and the product entry at each ordered pair of vertices. Its value is zero on the diagonal and one off the diagonal.")),
                Paragraph(Text("Reindexing an adjacency matrix by a graph automorphism fixes the matrix and commutes with powers. The third power of B has diagonal entries 2 and 0 at vertices 0 and 1. The fourth power of C has diagonal entries 40 and 42 at vertices 0 and 2. These entries count walks that return to their starting vertex at the specified length. Each pair of differing entries rules out an automorphism between the corresponding vertices."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Statement()
    {
        Formula h = F.Id("H"), k = F.Id("K");
        return Disp(Seq(Exists, Sp, h, Comma, k, Sp, Colon, Sp,
            Call("SimpleGraph", Call("Fin", D(17))), Comma, Sp,
            Call("A", h), Sp, Call("A", k), Sp, Eq, Sp, F.Id("J"), Sp, Minus, Sp, F.Id("I"),
            Sp, Land, Sp, new Formula.Not(Call("VT", h)),
            Sp, Land, Sp, new Formula.Not(Call("VT", k))));
    }
}
