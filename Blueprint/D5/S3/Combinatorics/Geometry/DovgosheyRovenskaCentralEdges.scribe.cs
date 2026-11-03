using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class DovgosheyRovenskaCentralEdgesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/dovgosheyrovenska2026centraledges");
    private const string CenterQuote = """Let (Y,ρ) be a metric space. The center of distances of (Y,ρ) is the subset C(Y)⊆ℝ⁺, such that t∈ C(Y) if and only if the equation ρ(y,p)=t has a solution for every p∈ Y.""";
    private const string CentralQuote = """Let (Y,ρ) be a metric space and let C(Y) be the center of distances of (Y,ρ). The central graph CG_Y of (Y,ρ) is a simple graph such that V(CG_Y)=Y and {u,v}∈ E(CG_Y) ⇔ ρ(u,v)∈ C(Y) for all u,v∈ Y. We will write that the central graph CG_Y is k-central if k=|C(Y)|.""";
    private const string DiameterQuote = """Let (Y,ρ) be a finite metric space with |Y|≥ 2. The diametrical graph G_Y of (Y,ρ) is a graph such that V(G)=Y and, for all u,v∈ Y, {u,v}∈ E(G_{Y}) ⇔ ρ(u,v)=diamY.""";
    private const string ConjectureQuote = """Let (X,d) be a finite ultrametric space with |X|≥ 4, let the central graph CG_X be 3-central, and let G_X be the diametrical graph of (X,d). Then the following statements are equivalent. (i) The diametrical graph G_X is complete bipartite with parts X_1, X_2 satisfying the equality min{|X_1|,|X_2|}=2, and the central graph CG_X is the union G_X with star graphs S_1 and S_2, CG_X=G_X∪ S_1 ∪ S_2, such that V(S_1)=X_1 and V(S_2)=X_2. (ii) The inequality |E(CG_X)| ≤ |E(CG_Y)| holds for all metric spaces (Y,ρ) which have 3-central CG_Y and satisfy |Y|=|X|.""";
    private const string ConditionQuote = """The diametrical graph G_X is complete bipartite with parts X_1, X_2 satisfying the equality min{|X_1|,|X_2|}=2, and the central graph CG_X is the union G_X with star graphs S_1 and S_2, CG_X=G_X∪ S_1 ∪ S_2, such that V(S_1)=X_1 and V(S_2)=X_2.""";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-point ultrametric has more central edges than a three-central metric.",
        H("Three central distances do not give the proposed edge minimum"),
        Blocks(
            Node("distance-center", "The center of distances", "center", CenterFormula(),
                "Definition 1.1 (p. 1): “" + CenterQuote + "” The source uses the nonnegative reals, including zero. The real variable t is realized as a distance from every p; the realizing point y may depend on p.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("central-graph", "The central graph", "centralGraph", GraphFormula(false),
                "Definition 1.2 (p. 1): “" + CentralQuote + "” SimpleGraph.fromRel removes loops and symmetrizes the relation. Symmetry of distance gives precisely the displayed adjacency for distinct vertices. Edge sets contain unordered pairs, counted once.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("diametrical-graph", "The diametrical graph", "diametricalGraph", GraphFormula(true),
                "Definition 2.14 (p. 4): “" + DiameterQuote + "” The diameter is Metric.diam of the whole carrier; only finite carriers with at least four points occur in the conjecture.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bipartite-stars", "The bipartite graph with two stars", "conditionI", ConditionFormula(),
                "Conjecture 4.2(i) (p. 13): “" + ConditionQuote + "” Here A and B are the two parts. Their subtype elements a and b are star centers and ensure that both parts are nonempty. Sum.elim embeds the bipartite carrier into X. The two subtype stars are mapped into X, and Max.max is the graph join, with the union of edge sets.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("central-edges-claim", "Conjecture 4.2", "claim",
                Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, ClaimBody())),
                "Conjecture 4.2 (p. 13): “" + ConjectureQuote + "” X and Y are finite carriers, each equipped with its quantified metric. IsUltrametricDist is assumed only for X. The center has exactly three values, and Nat.card on edgeSet counts unordered edges. The equality of carrier cardinalities imposes no ultrametric restriction on Y.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("central-edges-result", "Conjecture 4.2 is false", "result",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "On Fin 4, pull back the 2-adic metric along the values 0,1,2,3. Distinct vertices of the same parity have distance 1/2; opposite parities have distance 1. The center is {0,1/2,1}, the central graph is complete, and its six edges are the union of the diametrical bipartite graph with parts {0,2}, {1,3} and the two single-edge stars. For the comparator, pull back the real metric along 0,4,5,9. Its center is exactly {0,4,5}; its four central edges are {0,1}, {0,2}, {1,3}, {2,3}. The asserted inequality would be 6 ≤ 4. This refutes the implication from (i) to (ii). The comparison restricted to ultrametrics is a separate question.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("central-edges"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula Inst(string name, Formula carrier, Formula body) =>
        Seq(OpenBracket, Call(name, carrier), CloseBracket, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, F.Id(name), Colon, type, Sp, Mapsto, Sp, body));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula EdgeCount(Formula carrier) =>
        App(Q("Nat", "card"), Seq(Parenthesized(Call("centralGraph", carrier)), Dot, F.Id("edgeSet")));
    private static Formula CenterCount(Formula carrier) => App(Q("Nat", "card"), Call("center", carrier));
    private static Formula Card(Formula carrier) => App(Q("Fintype", "card"), carrier);

    private static Formula CenterFormula()
    {
        Formula x = F.Id("X"), t = F.Id("t"), p = F.Id("p"), y = F.Id("y");
        Formula members = Seq(OpenBrace, t, Colon, Real(), Sp, Mid, Sp,
            And(Le(D(0), t), All("p", x, Ex("y", x, Eq(Call("dist", y, p), t)))), CloseBrace);
        return Disp(All("X", F.Id("Type"), Inst("MetricSpace", x, Eq(Call("center", x), members))));
    }

    private static Formula GraphFormula(bool diametrical)
    {
        Formula x = F.Id("X"), u = F.Id("u"), v = F.Id("v");
        Formula relation = diametrical
            ? Eq(Call("dist", u, v), App(Q("Metric", "diam"),
                Parenthesized(Seq(Q("Set", "univ"), Colon, Call("Set", x)))))
            : new Formula.Relation(Call("dist", u, v), FormulaRelationOperator.MemberOf, Call("center", x));
        return Disp(All("X", F.Id("Type"), Inst("MetricSpace", x,
            Eq(Call(diametrical ? "diametricalGraph" : "centralGraph", x),
                App(Q("SimpleGraph", "fromRel"), Lam("u", x, Lam("v", x, relation)))))));
    }

    private static Formula ConditionBody(Formula x)
    {
        Formula a = F.Id("A"), b = F.Id("B"), ca = F.Id("a"), cb = F.Id("b");
        Formula cast = Parenthesized(Seq(F.Id("z"), Colon, x));
        Formula ia = Lam("z", a, cast), ib = Lam("z", b, cast);
        Formula bipartite = App(Q("SimpleGraph", "map"), App(Q("Sum", "elim"), ia, ib),
            Call("completeBipartiteGraph", a, b));
        Formula stars = App(Q("Max", "max"),
            App(Q("Max", "max"), Call("diametricalGraph", x),
                App(Q("SimpleGraph", "map"), ia, App(Q("SimpleGraph", "starGraph"), ca))),
            App(Q("SimpleGraph", "map"), ib, App(Q("SimpleGraph", "starGraph"), cb)));
        Formula predicates = And(Call("Disjoint", a, b),
            And(Eq(App(Q("Set", "union"), a, b), Q("Set", "univ")),
                And(Eq(Call("min", App(Q("Nat", "card"), a), App(Q("Nat", "card"), b)), D(2)),
                    And(Eq(Call("diametricalGraph", x), bipartite), Eq(Call("centralGraph", x), stars)))));
        return Ex("A", Call("Set", x), Ex("B", Call("Set", x), Ex("a", a, Ex("b", b, predicates))));
    }

    private static Formula ConditionFormula()
    {
        Formula x = F.Id("X");
        return Disp(All("X", F.Id("Type"), Inst("MetricSpace", x,
            new Formula.Logic(Call("conditionI", x), FormulaLogicOperator.Iff, ConditionBody(x)))));
    }

    private static Formula ClaimBody()
    {
        Formula x = F.Id("X"), y = F.Id("Y");
        Formula comparators = All("Y", F.Id("Type"), Inst("Fintype", y, Inst("MetricSpace", y,
            Imp(Eq(CenterCount(y), D(3)), Imp(Eq(Card(y), Card(x)), Le(EdgeCount(x), EdgeCount(y)))))));
        return All("X", F.Id("Type"), Inst("Fintype", x, Inst("MetricSpace", x,
            Imp(Call("IsUltrametricDist", x), Imp(Le(D(4), Card(x)), Imp(Eq(CenterCount(x), D(3)),
                new Formula.Logic(Call("conditionI", x), FormulaLogicOperator.Iff, comparators)))))));
    }
}
