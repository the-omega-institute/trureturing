using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming;

internal sealed class DaviesMariglianoCirculantOrbitsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/daviesmarigliano2021symmetries");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A graph on thirty vertices has a cyclic symmetry, at least eight orbits of unordered vertex pairs under its full automorphism group, and at most seven distinct real adjacency eigenvalues.",
        H("A circulant counterexample to the orbit–eigenvalue conjecture"),
        Blocks(
            Node("IsCirculant", "A cyclic symmetry on all vertices", CirculantFormula(),
                "Section 4, page 11: \"By definition, these are graphs that have a symmetry which is a cyclic permutation of its vertices.\" Vertices are Fin n. The positive order and the graph isomorphism G ≃g G express a symmetry on the entire vertex set; IsCycleOn is applied to its underlying permutation and Set.univ.",
                AssessedProvenance.FromLiterature(Source)),
            Node("pairOrbits", "Orbits of unordered pairs", OrbitsFormula(),
                "Corollary 3.3, page 7: \"In particular, let V * V be the set of unordered pairs of vertices of G and s the number of orbits of the entrywise action of Aut(G) on V * V.\" The proof specifies that the number of elements in V * V is binomial(n+1,2), so Sym2 retains diagonal pairs. Each inner Set.range uses every graph automorphism. The outer Set.range collects the distinct orbits.",
                AssessedProvenance.FromLiterature(Source)),
            Node("eigenvalueCount", "Distinct real adjacency eigenvalues", EigenvaluesFormula(),
                "Conjecture 4.4, page 11: \"If G is an uncoloured circulant graph, then the number of orbits of the action of Aut(G) on the set V*V of unordered pairs of vertices of G coincides with the number of distinct eigenvalues of its adjacency matrix.\" SimpleGraph.adjMatrix has entries one at adjacent vertices and zero elsewhere. Module.End.Eigenvalues is a set of scalars, and Nat.card counts its subtype without multiplicity. The real adjacency matrix of a simple undirected graph is symmetric. Classical decidability supplies the matrix for arbitrary G.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Davies–Marigliano Conjecture 4.4", Disp(Logic(F.Id("claim"),
                    FormulaLogicOperator.Iff, ClaimBody())),
                "Conjecture 4.4, page 11 of arXiv:2012.01905v5: \"If G is an uncoloured circulant graph, then the number of orbits of the action of Aut(G) on the set V*V of unordered pairs of vertices of G coincides with the number of distinct eigenvalues of its adjacency matrix.\" The universal quantifiers range over n : ℕ and every simple undirected graph on Fin n. IsCirculant includes positive order. Pair orbits include the diagonal and use the full automorphism group.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("dm2012-result"),
                DeclarationHandle.Create(Module + ".result"), H("The universal equality is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("On Fin 30, join two vertices when their residues modulo 2, 3 and 5 disagree in exactly one coordinate. Translation by one is a cyclic graph symmetry. The three edge types have respectively zero, one and three common neighbours. These intrinsic counts distinguish the types under every automorphism; paths using the other two types recover equality of each coordinate. The eight coordinate disagreement patterns therefore give at least eight distinct unordered-pair orbits. An integer circulant certificate shows that the adjacency operator is annihilated by X(X−7)(X−5)(X−4)(X−2)(X+1)(X+3). Applying this identity to an eigenvector places every real eigenvalue in {−3,−1,0,2,4,5,7}. Hence there are at most seven distinct eigenvalues, contradicting the equality. The proof uses only these bounds; exact counts and infinite families are separate assertions."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("davies-marigliano-2021-circulant-orbit-eigenvalue-conjecture"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("dm2012-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Q(params string[] names) => Seq([.. names.SelectMany(
        (name, index) => index == 0
            ? new Formula[] { Operatorname, Grp(F.Id(name)) }
            : [Dot, Operatorname, Grp(F.Id(name))])]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Logic(Formula left, FormulaLogicOperator operation, Formula right) =>
        new Formula.Logic(Parenthesized(left), operation, Parenthesized(right));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Graph(Formula n) => Call("SimpleGraph", Fin(n));
    private static Formula Automorphisms(Formula graph) =>
        App(Q("SimpleGraph", "Iso"), graph, graph);
    private static Formula GraphBinders(Formula body) => All("n", N,
        All("G", Graph(F.Id("n")), body));

    private static Formula CirculantFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), s = F.Id("s");
        Formula cycle = App(Q("Equiv", "Perm", "IsCycleOn"),
            Seq(s, Dot, Q("toEquiv")), Q("Set", "univ"));
        Formula exists = Seq(Exists, Sp,
            Parenthesized(Seq(s, Colon, Sp, Automorphisms(g))), Comma, Sp, cycle);
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
        return Disp(GraphBinders(Logic(Call("IsCirculant", g), FormulaLogicOperator.Iff,
            Logic(positive, FormulaLogicOperator.And, exists))));
    }

    private static Formula OrbitsFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), p = F.Id("p"), s = F.Id("s");
        Formula orbit = App(Q("Set", "range"), Lambda("s", Automorphisms(g),
            App(Q("Sym2", "map"), s, p)));
        Formula collection = App(Q("Set", "range"),
            Lambda("p", Call("Sym2", Fin(n)), orbit));
        return Disp(GraphBinders(Eq(Call("pairOrbits", g), collection)));
    }

    private static Formula EigenvaluesFormula()
    {
        Formula g = F.Id("G");
        Formula matrix = App(Seq(g, Dot, Q("adjMatrix")), R);
        Formula linearMap = Seq(Parenthesized(matrix), Dot, Q("mulVecLin"));
        Formula eigenvalues = App(Q("Module", "End", "Eigenvalues"), linearMap);
        return Disp(GraphBinders(Eq(Call("eigenvalueCount", g),
            App(Q("Nat", "card"), eigenvalues))));
    }

    private static Formula ClaimBody()
    {
        Formula g = F.Id("G");
        Formula equality = Eq(App(Q("Nat", "card"), Call("pairOrbits", g)),
            Call("eigenvalueCount", g));
        return GraphBinders(Logic(Call("IsCirculant", g), FormulaLogicOperator.Implies, equality));
    }
}
