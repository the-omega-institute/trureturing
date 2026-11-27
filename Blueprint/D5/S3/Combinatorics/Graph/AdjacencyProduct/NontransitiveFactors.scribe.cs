using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.AdjacencyProduct;

internal sealed class NontransitiveFactorsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/AdjacencyProduct/akbari2025primematrixproduct");

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
                Paragraph(Text("In Section 5, item 2 of arXiv:2512.24864v1, Akbari, Elahimanesh and Miraftab ask for two non-transitive graphs H and K whose adjacency matrices B and C satisfy BC = J − I. The question is at https://arxiv.org/html/2512.24864v1#S5.I1.i2")),
                Paragraph(Text("The two graphs share the labelled vertex set Fin 17. They have decidable adjacency, and adjMatrix uses integer entries. Matrix.of(1) has every entry equal to one, the subtracted 1 is the identity, and the product is ordinary matrix multiplication.")),
                Paragraph(Text("The two graphs are defined by literal neighbor lists. The kernel checks symmetry, looplessness and the product entry at each ordered pair of vertices. Its value is zero on the diagonal and one off the diagonal.")),
                Paragraph(Text("Reindexing an adjacency matrix by a graph automorphism fixes the matrix and commutes with powers. The third power of B has diagonal entries 2 and 0 at vertices 0 and 1. The fourth power of C has diagonal entries 40 and 42 at vertices 0 and 2. These entries count walks that return to their starting vertex at the specified length. Each pair of differing entries rules out an automorphism between the corresponding vertices."))),
            DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("akbari-elahimanesh-miraftab-nontransitive-adjacency-factors"),
                ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula QualifiedCall(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name)))), [.. arguments]);

    private static Formula Nontransitive(Formula graph, Formula vertices)
    {
        Formula i = F.Id("i"), j = F.Id("j"), e = F.Id("e");
        return Seq(Neg, Open, Forall, Sp, i, Comma, j, Colon, Sp, vertices, Comma, Sp,
            Exists, Sp, e, Colon, Sp, QualifiedCall("SimpleGraph", "Iso", graph, graph),
            Comma, Sp, new Formula.Apply(e, [i]), Sp, Eq, Sp, j, Close);
    }

    private static Formula Statement()
    {
        Formula h = F.Id("H"), k = F.Id("K");
        Formula vertices = Call("Fin", D(1, 7)), integers = Seq(Mathbb, Grp(F.Id("Z")));
        return Disp(Seq(Exists, Sp, h, Comma, k, Sp, Colon, Sp,
            Call("SimpleGraph", vertices), Comma, Sp,
            Call("adjMatrix", h, integers), Sp, Call("adjMatrix", k, integers), Sp, Eq, Sp,
            QualifiedCall("Matrix", "of", D(1)), Sp, Minus, Sp, D(1),
            Sp, Land, Sp, Nontransitive(h, vertices), Sp, Land, Sp, Nontransitive(k, vertices)));
    }
}
