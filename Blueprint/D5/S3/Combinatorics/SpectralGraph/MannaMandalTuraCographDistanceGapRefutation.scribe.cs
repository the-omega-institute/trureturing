using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class MannaMandalTuraCographDistanceGapRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.";
    private const string Question =
        "Open Problem 14.2(i), printed p. 22, asks “Is there ε > 0 such that (−2 − ε, −2) contains no distance eigenvalue of any connected cograph?”";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mannamandaltura2026cographdistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected cographs have distance eigenvalues arbitrarily close to −2 from below.",
        H("Open Problem 14.2(i): no uniform left gap at −2"),
        Blocks(
            Node("Vertex", "Vertices of the counterexample family", VertexFormula(),
                "The two Boolean vertices on the left are the universal vertex (false) and the initially isolated vertex (true). On the right, an index selects one of the matching edges, and a Boolean selects its endpoint.",
                AssessedProvenance.FromRepo()),
            Node("family", "Join with a singleton and a matching", FamilyFormula(),
                "The graph is K₁ joined to the disjoint union of one singleton and r independent copies of K₂. Distinct singleton vertices are adjacent. Across the sum, only the universal vertex is adjacent to matching endpoints. Matching endpoints are adjacent exactly when their indices agree and their Booleans differ.",
                AssessedProvenance.FromRepo(Source)),
            Node("P4Free", "No induced four-vertex path", P4FreeFormula(),
                "Section 1, printed p. 2, defines a cograph as “a finite simple graph containing no induced path on four vertices P₄.” A graph embedding preserves and reflects adjacency, so the predicate excludes exactly induced copies of the native four-vertex path.",
                AssessedProvenance.FromLiterature(Source)),
            Node("distanceMatrix", "Shortest-path distance matrix", DistanceFormula(),
                "The real matrix casts the native shortest-path edge count, including the diagonal zero. For a connected cograph on at least two vertices, Proposition 2.6 (printed p. 5 of arXiv:2611.06981v1) gives diameter at most two. Section 6 (printed p. 14) states the identity D = 2J − 2I − A.",
                AssessedProvenance.FromLiterature(Source)),
            Node("registered_family_counters_gap", "An eigenvalue in every open left neighborhood", CounterexampleFormula(),
                "The universal vertex gives connectedness and a walk of length two between distinct nonadjacent vertices. Each vertex of an induced P₄ has a nonneighbor among the other three, so the path avoids the universal vertex. The remaining vertices have at most one neighbor each. On the orbit-constant subspace, the distance quotient has rows (0, 1, 2r), (1, 0, 4r), and (1, 2, 4r−3). For t = λ + 2 its characteristic determinant is (t+1)(t−1)(t−3) + (6−4t)rt. At t = 0 this is 3. With r = q > 0 and t = −1/q it is −((1+1/q)³+2). Continuity gives a root in the strict interior. Choose 1/q < ε and lift a nonzero quotient kernel vector to the three nonempty orbits.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("claim", "The proposed uniform gap", Eqn(Call("claim"), Par(ClaimBody())),
                Question + " The graph ranges over all connected finite simple graphs with no induced four-vertex path. A real eigenvalue means that the distance matrix sends some nonzero real vector v to λv. The same positive ε must work for every graph, and both inequalities are strict.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation of the uniform gap", new Formula.Not(Par(ClaimBody())),
                "For every proposed ε, the joined matching family supplies a finite connected cograph and a real distance eigenvalue strictly inside the proposed interval. Open Problem 14.2(ii) asks separately about attaining the multiplicity bound.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("manna-mandal-tura-2026-cograph-distance-left-gap"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mmt-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Symbol(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula fn, params Formula[] args) =>
        new Formula.Apply(fn, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Symbol(name) : App(Symbol(name), args);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        App(Seq(Symbol(owner), Dot, Symbol(name)), args);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));

    private static Formula MinusTwo() => Seq(Minus, D(2));
    private static Formula Lower(Formula epsilon) => Seq(MinusTwo(), Sp, Minus, Sp, epsilon);
    private static Formula Positive(Formula value) => Less(D(0), value);
    private static Formula Conn(Formula graph) => Qualified("SimpleGraph", "Connected", graph);
    private static Formula Free(Formula graph) => Call("P4Free", graph);
    private static Formula Eigenvalue(Formula graph, Formula lam) =>
        App(Seq(Symbol("Module"), Dot, Symbol("End"), Dot, Symbol("HasEigenvalue")),
            Qualified("Matrix", "mulVecLin", Call("distanceMatrix", graph)), lam);

    private static Formula ClaimBody()
    {
        Formula epsilon = F.Id("epsilon"), v = F.Id("V"), graph = F.Id("G"), lam = F.Id("lambda");
        Formula exclusion = new Formula.Not(Par(And(Less(Lower(epsilon), lam), Less(lam, MinusTwo()))));
        Formula graphs = All("G", Call("SimpleGraph", v), Imp(Conn(graph),
            Imp(Free(graph), All("lambda", R(), Imp(Eigenvalue(graph, lam), exclusion)))));
        Formula finite = Seq(OpenBracket, Call("Fintype", v), CloseBracket, Comma, Sp, graphs);
        return Ex("epsilon", R(), And(Positive(epsilon), All("V", Call("Type"), finite)));
    }

    private static Formula CounterexampleFormula()
    {
        Formula epsilon = F.Id("epsilon"), r = F.Id("r"), lam = F.Id("lambda");
        Formula graph = Call("family", r);
        return All("epsilon", R(), Imp(Positive(epsilon), Ex("r", N(), And(Positive(r),
            Ex("lambda", R(), And(Less(Lower(epsilon), lam), And(Less(lam, MinusTwo()),
                And(Conn(graph), And(Free(graph), Eigenvalue(graph, lam))))))))));
    }

    private static Formula VertexFormula()
    {
        Formula r = F.Id("r");
        return All("r", N(), Eqn(Call("Vertex", r),
            Call("Sum", Call("Bool"), Par(Seq(Call("Fin", r), Sp, Times, Sp, Call("Bool"))))));
    }

    private static Formula FamilyFormula()
    {
        Formula r = F.Id("r"), a = F.Id("a"), b = F.Id("b"), i = F.Id("i"), j = F.Id("j");
        Formula Adjacency(Formula x, Formula y) => Qualified("SimpleGraph", "Adj", Call("family", r), x, y);
        Formula Same(Formula x, Formula y) => Seq(Par(x), Sp, Iff, Sp, Par(y));
        Formula Different(Formula x, Formula y) => Seq(x, Sp, Neq, Sp, y);
        Formula Pair(Formula x, Formula y) => Par(Seq(x, Comma, Sp, y));
        Formula LeftVertex(Formula x) => Qualified("Sum", "inl", x);
        Formula RightVertex(Formula x, Formula y) => Qualified("Sum", "inr", Pair(x, y));

        Formula bothLeft = Same(Adjacency(LeftVertex(a), LeftVertex(b)), Different(a, b));
        Formula fromLeft = All("j", Call("Fin", r),
            Same(Adjacency(LeftVertex(a), RightVertex(j, b)), Eqn(a, Call("false"))));
        Formula fromRight = All("i", Call("Fin", r),
            Same(Adjacency(RightVertex(i, a), LeftVertex(b)), Eqn(b, Call("false"))));
        Formula bothRight = All("i", Call("Fin", r), All("j", Call("Fin", r),
            Same(Adjacency(RightVertex(i, a), RightVertex(j, b)), And(Eqn(i, j), Different(a, b)))));
        return All("r", N(), All("a", Call("Bool"), All("b", Call("Bool"),
            And(bothLeft, And(fromLeft, And(fromRight, bothRight))))));
    }

    private static Formula P4FreeFormula()
    {
        Formula v = F.Id("V"), graph = F.Id("G");
        Formula path = Qualified("SimpleGraph", "pathGraph", D(4));
        Formula embedding = Qualified("SimpleGraph", "Embedding", path, graph);
        return All("V", Call("Type"), All("G", Call("SimpleGraph", v),
            Seq(Free(graph), Sp, Iff, Sp, Call("IsEmpty", embedding))));
    }

    private static Formula DistanceFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), x = F.Id("x"), y = F.Id("y");
        Formula entry = Par(Seq(Qualified("SimpleGraph", "dist", g, x, y), Colon, Sp, R()));
        return All("V", Call("Type"), All("G", Call("SimpleGraph", v), All("x", v, All("y", v,
            Eqn(Call("distanceMatrix", g, x, y), entry)))));
    }
}
