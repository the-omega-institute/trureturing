using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.NoisyVoter;

internal sealed class RepetitionVarianceLinearDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Noisy voter repetition counts have a positive linear variance lower bound.",
        H("The repetition variance of the noisy voter model"),
        Blocks(
            Node("coordinates", "Independent space-time coordinates", "Coord", CoordFormula(),
                "Four constructors index initial opinions, fresh opinions, refresh controls and neighbour choices. Initial coordinates use only a vertex; the other three use a natural time and a vertex.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("values", "The value at each coordinate", "Value", ValueFormula(),
                "Opinions and refresh controls are Bool-valued. A choice at v takes values in the subtype G.neighborSet(v), so it always selects an actual neighbour. Each value type has the discrete measurable space.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("laws", "Fair opinions, Bernoulli controls and uniform choices", "coordinateLaw", LawFormula(),
                "Section 1, p. 2: “Initially, at time t = 0, all vertices are assigned with independent Bernoulli random variables X₀(u) ∼ Bern(1/2), u ∈ V(G). Then, for every t ∈ ℕ, every u ∈ V(G) (independently of all the other vertices), with probability ε, gets a random opinion Y_t(u) ∼ Bern(1/2), or, with probability 1 − ε, chooses an opinion of one of its neighbors chosen uniformly at random.” The noise parameter e is a member of unitInterval; true means refresh. The neighbour-existence proof supplies the Nonempty argument of PMF.uniformOfFintype. The displayed half is a member of unitInterval.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("model", "The probability model and all its fields", "Model", ModelFormula(),
                "Section 1, p. 2: “Consider a connected graph G (not necessarily finite) and a real number ε ∈ (0, 1).” Model.mk lists, in order, the probability-measure proof, connectivity proof, neighbour-existence proof, noise parameter, its strict bounds, the coordinate family, measurability of each coordinate, independence of the whole family and its marginal laws. Local finiteness supplies finite neighbour types. A one-vertex graph with no neighbour is excluded because its uniform copying law is undefined.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("process", "The synchronous noisy voter recursion", "nvm", NvmFormula(),
                "At time zero the process reads the initial opinion. At time k+1 it reads the fresh opinion when the refresh control is true; otherwise it reads the previous opinion at the selected neighbour. This is the Bool form of Section 1's displayed recursion on p. 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The unnormalised repetition count", "W", WFormula(),
                "Section 2.2, p. 5: “For every t, consider ζ_t = I(X_t = X_{t+d}).” W counts these equalities for 1 ≤ i ≤ t. The observation window therefore extends to time t+d. The summand is a real indicator, and no factor 1/t is present.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Sublinear variance is impossible", "claim", ClaimFormula(),
                "Section 2.2, p. 6: “May Var(ζ₁ + … + ζ_t) be sublinear? We do not have an answer. However, we prove that it is either linear in t or O(ln t).” The answer is encoded by negating little-o of the real sequence t. V is any vertex type, G any connected locally finite graph with a neighbour at every vertex, P any probability model with the stated independent coordinate laws, u any vertex and d any positive natural lag.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "A linear variance contribution at regularly spaced times", "result", ResultFormula(),
                "A refresh at u followed by refreshes at every neighbour isolates one fair opinion. Only the repetition terms at r−d and r contain it. Centres r = k(d+1) do not differ by d. Flipping the isolated fair opinions yields orthogonal covariance projections. Requiring one additional refresh at r+d gives a cylinder of probability e^(degree(u)+2); the future fair opinion makes exactly half of this cylinder contribute. Summing gives Var(W) ≥ (e^(degree(u)+2)/2) floor(t/(d+1)), and this contradicts little-o along multiples of d+1. The floor uses natural-number division. The proof works directly with Measure.infinitePi, including infinite locally finite graphs.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("benjamini-helman-tov-zhukovskii-2023-noisy-voter-repetition-variance"),
                    ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bhz-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Some(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula PlusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Lam(string x, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(x), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula DepArrow(string x, Formula type, Formula body) =>
        Seq(Parenthesized(Seq(F.Id(x), Colon, type)), Sp, To, Sp, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula AsType(Formula value, Formula type) => Seq(value, Colon, type);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula CoordType() => Call("Coord", F.Id("V"));
    private static Formula ValueType(Formula i) => Call("Value", F.Id("G"), i);
    private static Formula Neighbor(Formula v) => App(Seq(F.Id("G"), Dot, Named("neighborSet")), v);
    private static Formula Coordinate(string kind, params Formula[] args) => QCall("Coord", kind, args);
    private static Formula Family() => DepArrow("i", CoordType(), Arr(F.Id("O"), ValueType(F.Id("i"))));
    private static Formula HasNeighbor() => All("v", F.Id("V"), Some("w", F.Id("V"),
        App(Seq(F.Id("G"), Dot, Named("Adj")), F.Id("v"), F.Id("w"))));
    private static Formula GraphParameters(Formula body) => All("V", Named("Type"),
        All("G", Call("SimpleGraph", F.Id("V")), body));
    private static Formula Graph(Formula body) =>
        GraphParameters(Instance(Seq(F.Id("G"), Dot, Named("LocallyFinite")), body));
    private static Formula ProbabilitySpace(Formula body) => All("O", Named("Type"),
        Instance(Call("MeasurableSpace", F.Id("O")), All("P", Call("Measure", F.Id("O")), body)));
    private static Formula FamilyParameters(Formula body) => GraphParameters(All("O", Named("Type"), All("x", Family(), body)));
    private static Formula VertexTime(Formula body) => All("t", Nat(), All("v", F.Id("V"), body));
    private static Formula Rows(params Formula[] rows) => Disp(new Formula.Aligned([.. rows]));

    private static Formula CoordFormula() => Rows(
        All("V", Named("Type"), AsType(CoordType(), Named("Type"))),
        All("V", Named("Type"), All("v", F.Id("V"), AsType(Coordinate("initial", F.Id("v")), CoordType()))),
        All("V", Named("Type"), VertexTime(AsType(Coordinate("fresh", F.Id("t"), F.Id("v")), CoordType()))),
        All("V", Named("Type"), VertexTime(AsType(Coordinate("refresh", F.Id("t"), F.Id("v")), CoordType()))),
        All("V", Named("Type"), VertexTime(AsType(Coordinate("choice", F.Id("t"), F.Id("v")), CoordType()))));

    private static Formula ValueFormula() => Rows(
        GraphParameters(All("v", F.Id("V"), Eqn(ValueType(Coordinate("initial", F.Id("v"))), Named("Bool")))),
        GraphParameters(VertexTime(Eqn(ValueType(Coordinate("fresh", F.Id("t"), F.Id("v"))), Named("Bool")))),
        GraphParameters(VertexTime(Eqn(ValueType(Coordinate("refresh", F.Id("t"), F.Id("v"))), Named("Bool")))),
        GraphParameters(VertexTime(Eqn(ValueType(Coordinate("choice", F.Id("t"), F.Id("v"))), QCall("Set", "Elem", Neighbor(F.Id("v")))))));

    private static Formula LawParameters(Formula body) => Graph(All("e", Named("unitInterval"),
        All("hNbr", HasNeighbor(), body)));
    private static Formula Law(Formula i) => Call("coordinateLaw", F.Id("G"), F.Id("e"), F.Id("hNbr"), i);
    private static Formula Bernoulli(Formula p) => Call("bernoulliMeasure", Named("true"), Named("false"), p);
    private static Formula Half() => Parenthesized(AsType(new Formula.Fraction(D(1), D(2)), Named("unitInterval")));
    private static Formula LawFormula() => Rows(
        LawParameters(All("v", F.Id("V"), Eqn(Law(Coordinate("initial", F.Id("v"))), Bernoulli(Half())))),
        LawParameters(VertexTime(Eqn(Law(Coordinate("fresh", F.Id("t"), F.Id("v"))), Bernoulli(Half())))),
        LawParameters(VertexTime(Eqn(Law(Coordinate("refresh", F.Id("t"), F.Id("v"))), Bernoulli(F.Id("e"))))),
        LawParameters(VertexTime(Eqn(Law(Coordinate("choice", F.Id("t"), F.Id("v"))),
            Seq(Parenthesized(QCall("PMF", "uniformOfFintype", QCall("Set", "Elem", Neighbor(F.Id("v"))))), Dot, Named("toMeasure"))))));

    private static Formula ModelFormula()
    {
        Formula O = F.Id("O"), P = F.Id("P"), e = F.Id("e"), x = F.Id("x"), i = F.Id("i");
        Formula measurable = All("i", CoordType(), Call("Measurable", App(x, i)));
        Formula laws = All("i", CoordType(), Call("HasLaw", App(x, i), Law(i), P));
        Formula constructor = AsType(QCall("Model", "mk", F.Id("p"), F.Id("c"), F.Id("hNbr"), e,
            F.Id("hp"), F.Id("hb"), x, F.Id("hm"), F.Id("hi"), F.Id("hl")), Call("Model", F.Id("G"), P));
        return Disp(Graph(ProbabilitySpace(All("p", Call("IsProbabilityMeasure", P),
            All("c", Seq(F.Id("G"), Dot, Named("Connected")), All("hNbr", HasNeighbor(),
            All("e", Named("unitInterval"), All("hp", Less(D(0), Parenthesized(AsType(e, Real()))),
            All("hb", Less(Parenthesized(AsType(e, Real())), D(1)), All("x", DepArrow("i", CoordType(), Arr(O, ValueType(i))),
            All("hm", measurable, All("hi", Call("iIndepFun", x, P), All("hl", laws, constructor)))))))))))));
    }

    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), condition, Sp, Named("then"), yes, Sp, Named("else"), no);
    private static Formula NvmFormula()
    {
        Formula x = F.Id("x"), v = F.Id("v"), w = F.Id("w"), k = F.Id("k"), next = PlusOf(k, D(1));
        Formula readInitial = App(x, Coordinate("initial", v), w);
        Formula readRefresh = App(x, Coordinate("refresh", next, v), w);
        Formula readFresh = App(x, Coordinate("fresh", next, v), w);
        Formula selected = QCall("Subtype", "val", App(x, Coordinate("choice", next, v), w));
        return Rows(
            FamilyParameters(All("v", F.Id("V"), All("w", F.Id("O"), Eqn(Call("nvm", x, D(0), v, w), readInitial)))),
            FamilyParameters(All("k", Nat(), All("v", F.Id("V"), All("w", F.Id("O"),
                Eqn(Call("nvm", x, next, v, w), IfThenElse(readRefresh, readFresh, Call("nvm", x, k, selected, w))))))));
    }

    private static Formula WFormula()
    {
        Formula x = F.Id("x"), u = F.Id("u"), d = F.Id("d"), t = F.Id("t"), i = F.Id("i"), w = F.Id("w");
        Formula indicator = IfThenElse(Eqn(Call("nvm", x, i, u, w), Call("nvm", x, PlusOf(i, d), u, w)), D(1), D(0));
        Formula sum = App(Qualified("Finset", "sum"), QCall("Finset", "Icc", D(1), t),
            Lam("i", Nat(), Parenthesized(AsType(indicator, Real()))));
        return Disp(FamilyParameters(All("u", F.Id("V"), All("d", Nat(), All("t", Nat(),
            Eqn(Call("W", x, u, d, t), Lam("w", F.Id("O"), sum)))))));
    }

    private static Formula ClaimBody()
    {
        Formula M = F.Id("M"), u = F.Id("u"), d = F.Id("d"), t = F.Id("t");
        Formula coordinate = Seq(M, Dot, Named("coordinate"));
        Formula variances = Lam("t", Nat(), Call("variance", Call("W", coordinate, u, d, t), F.Id("P")));
        Formula times = Lam("t", Nat(), Parenthesized(AsType(t, Real())));
        Formula littleO = QCall("Asymptotics", "IsLittleO", Qualified("Filter", "atTop"), variances, times);
        Formula conclusion = All("M", Call("Model", F.Id("G"), F.Id("P")),
            All("u", F.Id("V"), All("d", Nat(), Imp(LessEq(D(1), d), new Formula.Not(Parenthesized(littleO))))));
        return All("V", Named("Type"), Instance(Call("DecidableEq", F.Id("V")),
            All("G", Call("SimpleGraph", F.Id("V")), Instance(Seq(F.Id("G"), Dot, Named("LocallyFinite")),
                ProbabilitySpace(conclusion)))));
    }

    private static Formula ClaimFormula() => Disp(Eqn(Named("claim"), ClaimBody()));
    private static Formula ResultFormula() => Disp(Named("claim"));
}
