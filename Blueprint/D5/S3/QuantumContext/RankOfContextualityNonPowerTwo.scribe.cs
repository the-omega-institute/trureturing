using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class RankOfContextualityNonPowerTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumContext/RankOfContextualityNonPowerTwo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/horodecki2022rank");
    private const string Question = "Finally, it would be interesting to construct a quantum behavior having the rank of contextuality different from the power of 2 (the power of 2 is achieved by a tensor product of the Peres-Mermin behaviors).";
    private const string OutcomeQuote = "We refer to output A given input X as an ordered list of outcomes (a₁, a₂, . . . , a|X|)), that is, it assigns a value to every observable in the context corresponding to X.";
    private const string NCQuote = "In other words: a non-contextual behavior PNC is a probabilistic mixture of deterministic behaviors that have fixed values of outcomes to any observable beforehand.";
    private const string RankQuote = "Let P be a behavior. Let N be the set of all non-contextual behaviors, each of the form Nᵢ(A | X). Then we define the rank of contextuality denoted as RC in the following way";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantum behavior has rank of contextuality three.",
        H("A quantum behavior with rank of contextuality three"),
        Blocks(
            Paragraph(Text("Fin n consists of the n labels starting at zero. A context C(x) is an ordered list of observable labels; its outcome is a function Fin (List.length (C(x))) → Bool. The bit true means eigenvalue −1. Behavior is the real table carrier; IsQuantum supplies the quantum probabilities. The real weights mu correspond to μ and the matrix rho to ρ. All matrix traces are complex traces; ofReal explicitly embeds each real probability into Complex. Finite sets count distinct behaviors, rather than labels of models that happen to agree.")),
            Node("Behavior", "Behavior tables", BehaviorFormula(), AssessedProvenance.FromRepo(Source),
                "The carrier consists of real-valued tables indexed by contexts and outcomes, on which IsQuantum and NonContextual impose the source's probability conditions."),
            Node("restrict", "Restriction of a global assignment", RestrictFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 2, PDF page 4: “" + OutcomeQuote + "” The i-th output is the predetermined value of the observable at position i in C(x)."),
            Node("NonContextual", "Noncontextual distributions", NCFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 2, PDF page 4, equation (2): “" + NCQuote + "” The weight mu is nonnegative and has total mass one. The fiber sum is over all assignments g whose restriction equals a."),
            Node("coverSizes", "Cardinalities of noncontextual covers", CoverFormula(), AssessedProvenance.FromLiterature(Source),
                "Definition 3.1, PDF page 5: “" + RankQuote + "” “where |S| denotes the cardinality of the set S.” A single member must reproduce all outcomes at a given context; the member may depend on the context."),
            Node("IsRankOfContextuality", "The least cover cardinality", RankFormula(), AssessedProvenance.FromLiterature(Source),
                "Definition 3.1, PDF page 5, equation (3): “" + RankQuote + "” “where |S| denotes the cardinality of the set S.” IsLeast expresses membership and the lower bound on every cover cardinality."),
            Node("IsQuantum", "Quantum realization", QuantumFormula(), AssessedProvenance.FromLiterature(Source),
                "Section 2, PDF page 4: “With any set of observables V = {Vᵢ}, we can identify their commutation relations and represent them by a hypergraph H on this set where hyperedges are subsets of the powerset of V that denote contexts, i.e. sets of mutually commuting observables.” Binary observables are Hermitian involutions. Their spectral projections are multiplied in the list order, and the Born probability is the trace against the density matrix."),
            Node("claim", "The construction question", Seq(N("claim"), Sp, Iff, Sp, Existence()), AssessedProvenance.FromLiterature(Source),
                "Section 9 (Section IX in the arXiv source), PDF page 19: “" + Question + "” The observable and context counts m and k, their lists C, the behavior P and its integer rank r are all existential. The final universal quantifier excludes every power 2^n, including n = 0."),
            Describe.Lean(DescribeId.Create("rank-three-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A quantum rank that is not a power of two"), StatementSource.FromAuthor(Disp(N("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The behavior is the product of two Peres–Mermin squares: 18 observable labels, 36 paired contexts, and the maximally mixed state on Fin 16. Each square has five positive parity contexts and one negative parity context. For every context c, the uniform weight on the 16 assignments with the sole parity defect at c agrees with the square away from c. The three products with matching row defects cover every paired context, since at most two of the three rows occur in that pair. For the lower bound, each noncontextual product-scenario model has noncontextual copy marginals. One bad first-copy context for one model and one bad second-copy context for another produce a paired context that neither model reproduces. Thus every cover has at least three distinct members, and the displayed three-member cover is optimal. The rank is 3, which is odd and greater than one, so it is not 2^n for any natural n."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("horodecki-2022-rank-of-contextuality-non-power-of-two"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("rank-context-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula N(string name) => F.Id(name);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(N(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(N(owner)), Dot, Operatorname, Grp(N(name)));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(N(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(N(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Fn(string name, Formula type, Formula body) => Seq(N("fun"), Sp, Parenthesized(Seq(N(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula CX() => App(N("C"), N("x"));
    private static Formula Outcome() => Arrow(Fin(App(Q("List", "length"), CX())), N("Bool"));
    private static Formula Scenario() => Arrow(Fin(N("k")), Call("List", Fin(N("m"))));
    private static Formula Global() => Arrow(Fin(N("m")), N("Bool"));
    private static Formula Setup(Formula body) => All("k", N("Nat"), All("m", N("Nat"), All("C", Scenario(), body)));
    private static Formula WithP(Formula body) => Setup(All("P", Call("Behavior", N("C")), body));
    private static Formula SumOf(string name, Formula type, Formula body) => Seq(Sum, Underscore, Grp(N(name), Colon, Sp, type), Sp, body);
    private static Formula Fiber(Formula mu) => Seq(new Formula.Subscript(Sum, Seq(N("g"), Colon, Sp, Global(), Sp, N("with"), Sp, Eqn(Call("restrict", N("C"), N("x"), N("g")), N("a")))), Sp, App(mu, N("g")));
    private static Formula BehaviorFormula() => Setup(Eqn(Call("Behavior", N("C")),
        Seq(Parenthesized(Seq(N("x"), Colon, Sp, Fin(N("k")))), Sp, To, Sp, Arrow(Outcome(), N("Real")))));
    private static Formula RestrictFormula() => Setup(All("x", Fin(N("k")), All("g", Global(),
        Eqn(Call("restrict", N("C"), N("x"), N("g")), Fn("i", Fin(App(Q("List", "length"), CX())),
            App(N("g"), App(Q("List", "get"), CX(), N("i"))))))));
    private static Formula NCFormula() => Setup(All("N", Call("Behavior", N("C")),
        Seq(Call("NonContextual", N("C"), N("N")), Sp, Iff, Sp,
            Ex("mu", Arrow(Global(), N("Real")), And(
                All("g", Global(), new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, Call("mu", N("g")))),
                And(Eqn(SumOf("g", Global(), Call("mu", N("g"))), D(1)),
                    All("x", Fin(N("k")), All("a", Outcome(), Eqn(App(N("N"), N("x"), N("a")), Fiber(N("mu")))))))))));
    private static Formula CoverFormula()
    {
        var same = All("a", Outcome(), Eqn(Call("N", N("x"), N("a")), Call("P", N("x"), N("a"))));
        var member = Seq(N("N"), Sp, InMacro, Sp, N("S"));
        var cover = All("x", Fin(N("k")), Ex("N", Call("Behavior", N("C")), And(member, same)));
        var nc = All("N", Call("Behavior", N("C")), Seq(member, Sp, Implies, Sp, Call("NonContextual", N("C"), N("N"))));
        var set = Ex("S", Call("Finset", Call("Behavior", N("C"))),
            And(Eqn(App(Q("Finset", "card"), N("S")), N("n")), And(nc, cover)));
        return WithP(Eqn(Call("coverSizes", N("C"), N("P")),
            Seq(OpenBrace, N("n"), Colon, Sp, N("Nat"), Sp, Mid, Sp, set, CloseBrace)));
    }
    private static Formula RankFormula() => WithP(All("r", N("Nat"), Seq(Call("IsRankOfContextuality", N("C"), N("P"), N("r")), Sp, Iff, Sp,
        Call("IsLeast", Call("coverSizes", N("C"), N("P")), N("r")))));
    private static Formula Mat() => Call("Matrix", Fin(N("d")), Fin(N("d")), N("Complex"));
    private static Formula OAt(Formula index) => App(N("O"), index);
    private static Formula Observable(string name) => OAt(App(Q("List", "get"), CX(), N(name)));
    private static Formula Projection() => App(Q("HSMul", "hSMul"), Parenthesized(Seq(new Formula.Fraction(D(1), D(2)), Colon, Sp, N("Complex"))),
        Add(D(1), App(Q("HSMul", "hSMul"), Parenthesized(Seq(N("if"), Sp, App(N("a"), N("i")), Sp, N("then"), Sp, Minus, D(1), Sp, N("else"), Sp, D(1), Colon, Sp, N("Complex"))), Observable("i"))));
    private static Formula QuantumFormula()
    {
        var probability = App(Q("Complex", "ofReal"), Call("P", N("x"), N("a")));
        var effect = App(Q("List", "prod"), App(Q("List", "ofFn"),
            Fn("i", Fin(App(Q("List", "length"), CX())), Projection())));
        var born = All("x", Fin(N("k")), All("a", Outcome(),
            Eqn(probability, App(Q("Matrix", "trace"), Mul(N("rho"), effect)))));
        var commute = All("x", Fin(N("k")), All("i", Fin(App(Q("List", "length"), CX())),
            All("j", Fin(App(Q("List", "length"), CX())), Call("Commute", Observable("i"), Observable("j")))));
        var involution = All("v", Fin(N("m")),
            And(App(Q("Matrix", "IsHermitian"), OAt(N("v"))), Eqn(Mul(OAt(N("v")), OAt(N("v"))), D(1))));
        var state = And(App(Q("Matrix", "PosSemidef"), N("rho")),
            And(Eqn(App(Q("Matrix", "trace"), N("rho")), D(1)), And(involution, And(commute, born))));
        var realization = Ex("d", N("Nat"), Ex("rho", Mat(), Ex("O", Arrow(Fin(N("m")), Mat()), state)));
        return WithP(Seq(Call("IsQuantum", N("C"), N("P")), Sp, Iff, Sp, realization));
    }
    private static Formula Existence()
    {
        var nonpower = All("n", N("Nat"), new Formula.Relation(N("r"), FormulaRelationOperator.NotEqual, new Formula.Power(D(2), N("n"))));
        var body = And(Call("IsQuantum", N("C"), N("P")), And(Call("IsRankOfContextuality", N("C"), N("P"), N("r")), nonpower));
        body = Ex("r", N("Nat"), body);
        body = Ex("P", Call("Behavior", N("C")), body);
        body = Ex("C", Scenario(), body);
        body = Ex("k", N("Nat"), body);
        return Ex("m", N("Nat"), body);
    }
}
