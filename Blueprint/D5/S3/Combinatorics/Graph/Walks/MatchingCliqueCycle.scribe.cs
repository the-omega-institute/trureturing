using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class MatchingCliqueCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clique fibers joined by arbitrary perfect matchings have the maximal-independent-set spectrum of the preceding cycle power and diameter one greater than the cycle diameter.",
        H("Matching-twisted clique cycles"),
        Blocks(
            Paragraph(Text("The construction, spectrum shift and sharp diameter follow the mathematical argument supplied by Thanh Vu. Literature priority is unassessed. Each successive pair of clique fibers is joined by a bijective matching. The closing matching is unrestricted, so the accumulated twist can be arbitrary.")),
            Paragraph(Text("All parameters m and t are natural numbers: the cycle length is m+3 and the fiber order is t+3. Arithmetic on a base position is modulo m+3. Write applyMatching(M,i,a) for M(i)(a), imageFst(I) for the image of I under the first-coordinate projection, and NatDiv(a,b) for natural-number division. The symbol d denotes the graph-power exponent, while k in the spectrum definition denotes a cardinality. For the connected graphs here, power(G,d) joins distinct vertices at distance at most d; power(G,0) is edgeless. IsMaximalIndep(G,I) means that I is independent and every omitted vertex has a neighbor in I.")),
            Node("vertices", "Vertex fibers", "Vertex", DescribeRole.Definition,
                "The offsets express every fiber order and cycle length at least three. A vertex consists of its base position and its fiber label."),
            Node("matchings", "The matching family", "Matchings", DescribeRole.Definition,
                "One arbitrary permutation of the labels is specified for each oriented successor edge, including the edge closing the cycle."),
            Node("transport", "Matching transport", "forward", DescribeRole.Definition,
                "Forward transport advances the base position and applies that position's matching. Its inverse retreats and applies the inverse matching."),
            Node("graph", "The actual finite graph", "graph", DescribeRole.Definition,
                "Within a fiber all distinct vertices are adjacent. Between fibers the only edges are the specified matchings and their reverse orientations."),
            Node("spectrum", "The maximal-independent-set spectrum", "spectrum", DescribeRole.Definition,
                "The spectrum records cardinalities of actual finite independent vertex sets that dominate every omitted vertex. It uses the existing maximal-independent-set predicate."),
            Node("cycle-distance", "Distance in the base cycle", "cycle_distance", DescribeRole.Lemma,
                "The distance between two cycle vertices is the smaller of their two circular separations."),
            Node("distance-bounds", "Projection and matching lifts bound distances", "distance_bounds", DescribeRole.Theorem,
                "Projecting a walk discards internal fiber steps. Conversely, a shortest cycle walk transports a vertex along its matchings; at most one final step inside the destination clique reaches the desired endpoint."),
            Node("projection", "Maximal independent sets project", "maximal_projection", DescribeRole.Theorem,
                "An independent set in a positive graph power contains at most one point per fiber. If an omitted base fiber could extend the projected set, shortest matching paths in the two cyclic directions would forbid at most two labels there. The fiber has at least three labels, so the original set could be extended."),
            Node("lift", "Lawful maximal lifts exist", "maximal_lift", DescribeRole.Theorem,
                "Among independent vertex sets supported over a given base independent set, choose one of maximal cardinality. The same two-label bound forces a representative in every specified fiber. Base maximality and the distance bound then dominate every omitted vertex. The projection is injective and preserves cardinality."),
            Node("power-spectrum", "All positive powers have the shifted spectrum", "spectrum_power", DescribeRole.Theorem,
                "Projection and lawful lift give both inclusions of the spectrum equality. At power one the base exponent is zero: the connected cycle has an edgeless zero-th power. The argument also applies when either power has become complete."),
            Node("diameter", "The diameter is sharp", "diameter", DescribeRole.Theorem,
                "Let D be the cycle diameter, half its length rounded down. Choose base vertices i and j at distance D and start at x=(i,0). Exclude from fiber j the second coordinates of the D-fold forward and inverse transports of x. At most two labels are excluded, so a label a remains. A walk from x to (j,a) of length at most D would project to a shortest cycle walk and end at one of those two excluded transports. Thus this actual vertex has distance greater than D, and the distance bound makes it exactly D+1.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Statement(declaration))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Id(string x) => F.Id(x);
    private static Formula Call(string x, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. args]);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Ex(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula TypedAll(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(Id(x), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Type() => new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
    private static Formula Params(Formula body) => All("m", Nat(), All("t", Nat(), body));
    private static Formula Family(Formula body) => Params(All("M", Call("Matchings", Id("m"), Id("t")), body));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);

    private static Formula Statement(string name)
    {
        var m = Id("m"); var t = Id("t"); var M = Id("M"); var d = Id("d");
        var x = Id("x"); var y = Id("y"); var I = Id("I"); var S = Id("S");
        var V = Call("Vertex", m, t);
        var B = Call("Fin", Add(m, D(3)));
        var C = Call("cycleGraph", Add(m, D(3)));
        var G = Call("graph", M);
        var GP = Call("power", G, d);
        var CP = Call("power", C, Sub(d, D(1)));
        var image = Call("imageFst", I);
        var positive = Le(D(1), d);
        var projected = And(Call("IsMaximalIndep", CP, image), Eq(Call("card", image), Call("card", I)));
        var lifted = Ex("I", Call("Finset", V),
            And(Call("IsMaximalIndep", GP, I),
                And(Eq(image, S), Eq(Call("card", I), Call("card", S)))));
        var familyType = Seq(B, Sp, Rightarrow, Sp, Call("Perm", Call("Fin", Add(t, D(3)))));
        var endpoint = Call("pair", Add(Call("fst", x), D(1)),
            Call("applyMatching", M, Call("fst", x), Call("snd", x)));
        var cliqueEdge = And(Eq(Call("fst", x), Call("fst", y)), Ne(x, y));
        var matchingEdge = Or(Eq(Call("forward", M, x), y), Eq(Call("forward", M, y), x));
        var adjacency = Iff(Call("Adj", G, x, y), Or(cliqueEdge, matchingEdge));
        var member = Iff(Call("mem", Id("k"), Call("spectrum", Id("G"))),
            Ex("I", Call("Finset", Id("V")),
                And(Call("IsMaximalIndep", Id("G"), I), Eq(Call("card", I), Id("k")))));
        var graphBinder = All("G", Call("SimpleGraph", Id("V")), All("k", Nat(), member));
        var sandwich = And(
            Le(Call("dist", C, Call("fst", x), Call("fst", y)), Call("dist", G, x, y)),
            Le(Call("dist", G, x, y), Add(Call("dist", C, Call("fst", x), Call("fst", y)), D(1))));
        return name switch
        {
            "Vertex" => Params(Eq(V, Call("Prod", B, Call("Fin", Add(t, D(3)))))),
            "Matchings" => Params(Eq(Call("Matchings", m, t), familyType)),
            "forward" => Family(All("x", V, Eq(Call("forward", M, x), endpoint))),
            "graph" => Family(All("x", V, All("y", V, adjacency))),
            "spectrum" => All("V", Type(), Instance(Call("Fintype", Id("V")),
                Instance(Call("DecidableEq", Id("V")), graphBinder))),
            "cycle_distance" => TypedAll("m", Nat(), TypedAll("i", B, TypedAll("j", B,
                Eq(Call("dist", C, Id("i"), Id("j")),
                    new Formula.Apply(Seq(Operatorname, Grp(Seq(Id("WellCoveredPowerCliqueProduct"), Dot, Id("cycleMetric")))),
                        [Add(m, D(3)), Id("i"), Id("j")]))))),
            "distance_bounds" => Family(All("x", V, All("y", V, sandwich))),
            "maximal_projection" => Family(All("d", Nat(), All("I", Call("Finset", V),
                Imp(And(positive, Call("IsMaximalIndep", GP, I)), projected)))),
            "maximal_lift" => Family(All("d", Nat(), All("S", Call("Finset", B),
                Imp(And(positive, Call("IsMaximalIndep", CP, S)), lifted)))),
            "spectrum_power" => Family(All("d", Nat(), Imp(positive,
                Eq(Call("spectrum", GP), Call("spectrum", CP))))),
            "diameter" => Family(Eq(Call("diam", G), Add(Call("NatDiv", Add(m, D(3)), D(2)), D(1)))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name))
        };
    }
}
