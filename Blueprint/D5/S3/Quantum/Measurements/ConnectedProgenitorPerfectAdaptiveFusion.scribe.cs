using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class ConnectedProgenitorPerfectAdaptiveFusionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/goodenough2026fusion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Goodenough, Landahl, Lee, Russo and Thompson (arXiv:2609.02559) conjecture that every [[n, 1, d]] graph code with a connected progenitor graph has a perfect adaptive fusion strategy: the physical fusions can be attempted in an order, with failure axes chosen from the earlier outcomes, so that a single successful physical fusion always gives a successful logical fusion. With the paper's failure criterion (Proposition 3.1), this holds: attempt the vertices farthest from the encoding vertex first with failure axis Z, and after the first success use axis X on the internal vertices of a shortest path from the encoding vertex to the successful vertex.",
        H("Connected progenitor graphs give perfect adaptive fusion"),
        Blocks(
            Node("pauli", "Pauli letters up to phase", PauliFormula(),
                "A single-qubit Pauli operator up to phase is recorded by its two bits (x, z): I = (false, false), X = (true, false), Z = (false, true), Y = (true, true).",
                "Pauli", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("identity", "The identity letter", IdentityFormula(),
                "The identity letter has both bits false.",
                "pauliI", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("generator", "Products of canonical generators", GeneratorFormula(),
                "For a finite simple graph G on a type V with decidable equality and decidable adjacency, the product over a set U of the canonical generators X_u times the product of Z_w over the neighbours w of u has, up to phase, the letter at w with x-bit 'w is in U' and z-bit 'w has an odd number of neighbours in U'. These products are, up to phase, all stabilizers of the graph state.",
                "genProduct", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("logical", "Non-trivial logical operators", LogicalFormula(),
                "For the progenitor graph G with encoding vertex e, a Pauli string P on the physical vertices is a non-trivial logical operator when it is the restriction to the vertices other than e of a graph-state stabilizer that is not the identity at e.",
                "IsNontrivialLogical", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("strategy", "Adaptive fusion strategies", StrategyFormula(),
                "An adaptive strategy attempts the physical vertices in increasing rank, the rank being injective on the vertices other than e, and gives each vertex a non-identity failure axis that depends only on the outcomes o (true for a successful fusion) of the physical vertices of smaller rank.",
                "AdaptiveStrategy", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("failure", "Logical failure", FailureFormula(),
                "Proposition 3.1 of the paper: the outcome o leads to a logical failure when some non-trivial logical operator is, at every failed vertex, the identity or the realized failure axis, and is the identity at every vertex whose fusion succeeded.",
                "LogicalFailure", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("perfect", "Perfect adaptive strategies", PerfectFormula(),
                "Some adaptive strategy avoids a logical failure for every outcome with at least one successful physical fusion.",
                "HasPerfectAdaptiveStrategy", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "Every graph code whose progenitor graph is a connected finite simple graph, with the encoding vertex incident to an edge, has a perfect adaptive strategy.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Attempt the physical vertices in order of decreasing graph distance from e, with failure axis Z until the first success. If the first success is at v, at distance l from e, fix a shortest path e = p(l), ..., p(1), p(0) = v that steps from each vertex to a neighbour one closer to e; its internal vertices are closer to e than v, so they have not been attempted, and from then on the axis is X on them and Z elsewhere. This choice uses only earlier outcomes. Adjacent vertices have distances differing by at most 1, so p(i) and p(j) are adjacent only when |i - j| = 1. Suppose a stabilizer product over U gives a logical failure. Off the path the vertex failed in Z or succeeded, so its x-bit is 0 and it is not in U; hence U lies on the path. At an internal path vertex the letter is I or X, and at v it is I, so each of these has an even number of neighbours in U. Since U lies on the path, the neighbours of p(i) in U are among p(i - 1) and p(i + 1). At v this gives p(1) not in U, and at p(i) for 1 <= i < l it gives that p(i + 1) is in U exactly when p(i - 1) is. Starting from p(0) and p(1) not in U, induction gives that no path vertex is in U. So U is empty and the stabilizer is the identity at e, a contradiction.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("goodenough-landahl-2026-connected-progenitor-adaptive-fusion"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("fusion-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Integers() => new Formula.Integers();
    private static Formula Bool() => Named("Bool");
    private static Formula True() => Named("true");
    private static Formula False() => Named("false");
    private static Formula PauliType() => Named("Pauli");
    private static Formula IdentityLetter() => Named("pauliI");
    private static Formula Adj(Formula a, Formula b) => Call("Adj", F.Id("G"), a, b);
    private static Formula Gen(Formula u, Formula w) => Call("genProduct", F.Id("G"), u, w);

    private static Formula GraphContext(Formula body) =>
        All("V", Named("Type"), Implies(Call("DecidableEq", F.Id("V")),
            All("G", Call("SimpleGraph", F.Id("V")),
                Implies(Call("DecidableRel", Call("Adj", F.Id("G"))), body))));

    private static Formula PauliFormula() =>
        Disp(Equal(PauliType(), Seq(Bool(), Sp, Times, Sp, Bool())));

    private static Formula IdentityFormula() =>
        Disp(Equal(IdentityLetter(), Pair(False(), False())));

    private static Formula GeneratorFormula()
    {
        Formula u = F.Id("U"), w = F.Id("w");
        Formula neighbours = Call("filter", Call("Adj", F.Id("G"), w), u);
        Formula value = Pair(Call("decide", Member(w, u)),
            Call("decide", Call("Odd", Call("card", neighbours))));
        return Disp(GraphContext(All("U", Call("Finset", F.Id("V")),
            All("w", F.Id("V"), Equal(Gen(u, w), value)))));
    }

    private static Formula LogicalFormula()
    {
        Formula e = F.Id("e"), p = F.Id("P"), u = F.Id("U"), w = F.Id("w");
        Formula agrees = All("w", F.Id("V"), Implies(NotEqual(w, e),
            Equal(new Formula.Apply(p, [w]), Gen(u, w))));
        Formula body = Some("U", Call("Finset", F.Id("V")),
            And(agrees, NotEqual(Gen(u, e), IdentityLetter())));
        return Disp(GraphContext(All("e", F.Id("V"), All("P", Arrow(F.Id("V"), PauliType()),
            Iff(Call("IsNontrivialLogical", F.Id("G"), e, p), body)))));
    }

    private static Formula StrategyFormula()
    {
        Formula e = F.Id("e"), s = F.Id("S"), a = F.Id("a"), b = F.Id("b"), w = F.Id("w"), u = F.Id("u");
        Formula o = F.Id("o"), o2 = F.Id("r");
        Formula rank(Formula x) => Call("rank", s, x);
        Formula axis(Formula x, Formula outcome) => Call("axis", s, x, outcome);
        Formula outcomes = Arrow(F.Id("V"), Bool());
        Formula injective = All("a", F.Id("V"), All("b", F.Id("V"), Implies(NotEqual(a, e),
            Implies(NotEqual(b, e), Implies(Equal(rank(a), rank(b)), Equal(a, b))))));
        Formula nonIdentity = All("w", F.Id("V"), All("o", outcomes,
            NotEqual(axis(w, o), IdentityLetter())));
        Formula earlier = All("u", F.Id("V"), Implies(NotEqual(u, e),
            Implies(Less(rank(u), rank(w)),
                Equal(new Formula.Apply(o, [u]), new Formula.Apply(o2, [u])))));
        Formula causal = All("w", F.Id("V"), All("o", outcomes, All("r", outcomes,
            Implies(earlier, Equal(axis(w, o), axis(w, o2))))));
        Formula fields = And(And(Member(Call("rank", s), Arrow(F.Id("V"), Integers())),
            Member(Call("axis", s), Arrow(F.Id("V"), Arrow(outcomes, PauliType())))),
            And(injective, And(nonIdentity, causal)));
        return Disp(All("V", Named("Type"), All("e", F.Id("V"),
            All("S", Call("AdaptiveStrategy", e), fields))));
    }

    private static Formula FailureFormula()
    {
        Formula e = F.Id("e"), s = F.Id("S"), o = F.Id("o"), p = F.Id("P"), w = F.Id("w");
        Formula pw = new Formula.Apply(p, [w]);
        Formula ow = new Formula.Apply(o, [w]);
        Formula atVertex = Implies(NotEqual(w, e), And(
            Implies(Equal(ow, False()), Or(Equal(pw, IdentityLetter()),
                Equal(pw, Call("axis", s, w, o)))),
            Implies(Equal(ow, True()), Equal(pw, IdentityLetter()))));
        Formula body = Some("P", Arrow(F.Id("V"), PauliType()),
            And(Call("IsNontrivialLogical", F.Id("G"), e, p), All("w", F.Id("V"), atVertex)));
        return Disp(GraphContext(All("e", F.Id("V"), All("S", Call("AdaptiveStrategy", e),
            All("o", Arrow(F.Id("V"), Bool()),
                Iff(Call("LogicalFailure", F.Id("G"), e, s, o), body))))));
    }

    private static Formula PerfectFormula()
    {
        Formula e = F.Id("e"), s = F.Id("S"), o = F.Id("o"), w = F.Id("w");
        Formula success = Some("w", F.Id("V"),
            And(NotEqual(w, e), Equal(new Formula.Apply(o, [w]), True())));
        Formula body = Some("S", Call("AdaptiveStrategy", e), All("o", Arrow(F.Id("V"), Bool()),
            Implies(success, new Formula.Not(Call("LogicalFailure", F.Id("G"), e, s, o)))));
        return Disp(GraphContext(All("e", F.Id("V"),
            Iff(Call("HasPerfectAdaptiveStrategy", F.Id("G"), e), body))));
    }

    private static Formula ClaimFormula()
    {
        Formula e = F.Id("e"), w = F.Id("w"), v = F.Id("V"), g = F.Id("G");
        Formula hypotheses = Implies(Call("Connected", g),
            Implies(Some("w", v, Adj(e, w)), Call("HasPerfectAdaptiveStrategy", g, e)));
        Formula body = All("V", Named("Type"), Implies(Call("Fintype", v),
            Implies(Call("DecidableEq", v), All("G", Call("SimpleGraph", v),
                Implies(Call("DecidableRel", Call("Adj", g)), All("e", v, hypotheses))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
