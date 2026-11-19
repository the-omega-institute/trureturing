using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Spectral;

internal sealed class CollinsScirihaMainSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/Spectral/CollinsScirihaMainSpectrum.";
    private static readonly LibraryNoteRef Question =
        LibraryNoteRef.Create("D5/L/GraphSpectra/collinssciriha2019main");
    private static readonly LibraryNoteRef Method =
        LibraryNoteRef.Create("D5/L/GraphSpectra/yanwang2022bethetrees");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite simple graphs with isomorphic bipartite double covers have the same main eigenvalues.",
        H("Main eigenvalues and bipartite double covers"),
        Blocks(
            Describe.Lean(DescribeId.Create("main-eigenvalue"), DeclarationHandle.Create(Prefix + "IsMain"),
                H("Main adjacency eigenvalues"), StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromLiterature(Question),
                Blocks(Paragraph(Text(
                    "The coordinate sum is the inner product with the all-ones vector. "
                    + "Its nonvanishing guarantees that the real adjacency eigenvector is nonzero. "
                    + "The predicate takes a finite vertex type and decidable adjacency."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-spectrum"), DeclarationHandle.Create(Prefix + "result"),
                H("Isomorphic double covers preserve the main spectrum"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Question, Method),
                Blocks(Paragraph(Text(
                    "Question 5.8 asks, “Let G and H be two graphs with CDC(G) ≃ CDC(H). "
                    + "Do G and H have the same main eigenvalues?” The same question is Question 16, "
                    + "p. 522, in the journal version. The Mathlib cover uses the disjoint sum "
                    + "of two copies of the vertex type. Only cross-layer pairs are adjacent, and they "
                    + "are adjacent exactly when the corresponding base vertices are adjacent. "
                    + "The vertex types have independent universes. The graphs may be empty or "
                    + "disconnected, and the real parameter includes zero.")),
                    Paragraph(Text(
                    "Each base vertex has a two-vertex fiber in its double cover. The equitable quotient "
                    + "is the base graph. Duplicating an eigenvector into the two layers doubles its "
                    + "coordinate sum. Adding the two layers of a cover eigenvector preserves its "
                    + "coordinate sum. Both operations preserve the eigenvector equation at the same "
                    + "eigenvalue. Reindexing by a cover isomorphism preserves both adjacency "
                    + "multiplication and the coordinate sum. Using the isomorphism and its inverse "
                    + "gives the two implications."))),
                DescribeRole.Theorem)), []));

    private static Formula MainFormula()
    {
        var vertices = F.Id("V");
        var graph = F.Id("G");
        var x = F.Id("x");
        var v = F.Id("v");
        var lam = LambdaLower;
        var eigenEquation = Seq(
            Par(Seq(Call("adjMatrix", graph, Real()), Sp, new Formula.Subscript(Star, F.Id("v")),
                Sp, x)), Par(v), Sp, Eq, Sp, lam, Sp, Cdot, Sp, x, Par(v));
        var total = Seq(new Formula.Subscript(Sum, Seq(v, Colon, vertices)), Sp, x, Par(v));
        var witnesses = Bind(Exists, x, Seq(vertices, Sp, To, Sp, Real()),
            Seq(Par(Bind(Forall, v, vertices, eigenEquation)), Sp, Land, Sp,
                Par(Seq(total, Sp, Neq, Sp, D(0)))));
        return Disp(Bind(Forall, vertices, Universe("u"),
            Instance(Call("Fintype", vertices), Bind(Forall, graph, Call("SimpleGraph", vertices),
            Instance(Call("DecidableRel", Par(Call("Adj", graph))), Bind(Forall, lam, Real(),
            Seq(Call("IsMain", graph, lam), Sp, Iff, Sp, Par(witnesses))))))));
    }

    private static Formula ResultFormula()
    {
        var v = F.Id("V");
        var w = F.Id("W");
        var g = F.Id("G");
        var h = F.Id("H");
        var lam = LambdaLower;
        var coverIso = Call("Iso", Par(Call("bipartiteDoubleCover", g)),
            Par(Call("bipartiteDoubleCover", h)));
        var mainG = Call("IsMain", g, lam);
        var mainH = Call("IsMain", h, lam);
        var directions = Seq(Par(Seq(mainG, Sp, To, Sp, mainH)), Sp, Land, Sp,
            Par(Seq(mainH, Sp, To, Sp, mainG)));
        return Disp(Bind(Forall, v, Universe("u"), Bind(Forall, w, Universe("w"),
            Instance(Call("Fintype", v), Instance(Call("Fintype", w),
            Bind(Forall, g, Call("SimpleGraph", v), Bind(Forall, h, Call("SimpleGraph", w),
            Bind(Forall, F.Id("e"), coverIso, Bind(Forall, lam, Real(), directions)))))))));
    }

    private static Formula Bind(Formula quantifier, Formula name, Formula domain, Formula body) =>
        Seq(quantifier, Sp, Par(Seq(name, Sp, Colon, Sp, domain)), Comma, Sp, body);

    private static Formula Instance(Formula instance, Formula body) =>
        Seq(Forall, Sp, OpenBracket, instance, CloseBracket, Comma, Sp, body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Universe(string level) =>
        Seq(Operatorname, Grp(F.Id("Type")), Sp, F.Id(level));

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Par(Formula body) => Seq(Open, body, Close);
}
