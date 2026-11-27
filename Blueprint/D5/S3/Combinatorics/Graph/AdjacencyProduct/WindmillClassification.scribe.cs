using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.AdjacencyProduct;

internal sealed class WindmillClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/AdjacencyProduct/akbari2025primematrixproduct");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A windmill admits an ordinary product of two simple graph adjacency matrices over the integers exactly when it has one blade and its blade order is one modulo four.",
        H("Adjacency-matrix factorization of windmill graphs"),
        Blocks(
            Describe.Lean(DescribeId.Create("windmill-graph"), DeclarationHandle.Create(Prefix + "windmill"),
                H("Windmill graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The vertex set is Option (Fin d × Fin (t − 1)). The none vertex is the hub and is adjacent to every blade vertex. Two blade vertices are adjacent exactly when their first coordinates agree and their second coordinates differ. The graph is loopless."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("windmill-classification"), DeclarationHandle.Create(Prefix + "result"),
                H("Which windmills factor"), StatementSource.FromAuthor(Classification()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("In Section 5, item 1 of arXiv:2512.24864v1, Akbari, Elahimanesh and Miraftab ask which pairs (d, t) give a windmill that admits a factorization. The question is at https://arxiv.org/html/2512.24864v1#S5.I1.i1")),
                    Paragraph(Text("The quantifier ranges over all pairs of simple undirected graphs on the windmill's labelled vertex set. The notation A(G) denotes the integer adjacency matrix of G, and juxtaposition denotes ordinary matrix multiplication.")),
                    Paragraph(Text("Symmetry reverses the product and makes both factors commute with the windmill adjacency matrix. The product at a blade vertex and the hub supplies a non-hub intermediate neighbor. Commutation at that entry then forces each factor to join the hub to every blade. Distinct blades would therefore give a positive product entry at a nonedge.")),
                    Paragraph(Text("A single blade is a complete graph. Commutation gives constant degrees for the two factors, whose product is t − 1. The second factor induces a graph of degree one on the first factor's neighbors of any vertex. The degree-sum formula gives even degree for the first factor, and reversing the factors gives even degree for the second. For t = 4k + 1 the cyclic steps of the first factor are ±1. Those of the second factor are 4j + 2 and 4j + 3 for 0 ≤ j < k. The sums partition the nonzero residues into blocks of four, with one representation per residue."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("akbari-elahimanesh-miraftab-windmill-factorization"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Classification()
    {
        Formula d = F.Id("d"), t = F.Id("t"), b = F.Id("B"), c = F.Id("C");
        Formula vertices = Call("Option", Seq(Call("Fin", d), Sp, Times, Sp,
            Call("Fin", Seq(t, Minus, D(1)))));
        Formula factors = Seq(Exists, Sp, b, Comma, c, Sp, Colon, Sp,
            Call("SimpleGraph", vertices), Comma, Sp,
            Call("A", b), Sp, Call("A", c), Sp, Eq, Sp, Call("A", Call("windmill", d, t)));
        return Disp(Seq(Forall, Sp, d, Comma, t, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp, D(1), Sp, Leq, Sp, d, Sp, Land, Sp, D(3), Sp, Leq, Sp, t,
            Sp, Implies, Sp, Open, Open, factors, Close, Sp, Iff, Sp,
            Open, d, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            t, Sp, Equiv, Sp, D(1), Sp, Pmod, Grp(D(4)), Close, Close));
    }
}
