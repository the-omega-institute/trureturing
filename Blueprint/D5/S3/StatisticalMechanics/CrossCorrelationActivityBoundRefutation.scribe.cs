using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class CrossCorrelationActivityBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/gu2024crosscorrelationactivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sixteen-state network contradicts the proposed general-network activity bound on cross-correlation asymmetry.",
        H("An equilibrium complete graph defeats the activity bound"), Blocks(
            Paragraph(Text(
                "Fin(N) consists of the states 0 through N − 1. The array w(m,n) gives the transition "
                    + "rate from n to m when m and n differ, and p is a real-valued column vector. "
                    + "Every sum includes all states in Fin(N). All quotients are real quotients, "
                    + "and natural numbers in real expressions are coerced to the reals. "
                    + "The functions flux, activity, entropyRate, scaleRatio, asym and diffusion denote "
                    + "the quantities T, A, σ, γ, α and D of Eqs. (2)–(7), respectively.")),
            Node("flux", "One-way flux", FluxFormula(),
                "Off the diagonal, the one-way flux is T_mn = w(m,n) p(n), as in Eq. (2). "
                    + "Its diagonal is zero, so unrestricted double sums of fluxes equal sums over distinct states. "
                    + "The expression is defined for arbitrary real arrays w and p."),
            Node("activity", "Total dynamical activity", ActivityFormula(),
                "Equation (4) sums the one-way fluxes to obtain the total transition activity A. "
                    + "Both orientations of each transition are included."),
            Node("entropyRate", "Entropy production", EntropyFormula(),
                "Equation (4) weights each positive one-way flux by the logarithm of its ratio to "
                    + "the reverse flux. Terms with nonpositive forward flux are zero. "
                    + "For a bidirectional network in a steady state, every positive forward flux has positive reverse flux. "
                    + "The logarithm is the real natural logarithm."),
            Node("scaleRatio", "Scale separation of positive fluxes", RatioFormula(),
                "Equation (3) divides the largest positive one-way flux by the smallest. "
                    + "The displayed set consists exactly of the positive flux values. "
                    + "The real supremum and infimum give a total expression even when that set is empty; "
                    + "when it is nonempty, it is finite and its extrema are attained."),
            Node("asym", "The antisymmetric correlation slope", AsymFormula(),
                "Equation (7) gives α_ab, half the difference of the two cross-correlation slopes "
                    + "at zero time lag. Its sign uses the transition convention n to m. "
                    + "The observables a and b are arbitrary real-valued functions on the state space."),
            Node("diffusion", "The autocorrelation slope", DiffusionFormula(),
                "The quantity D_a is half the flux-weighted sum of squared changes in a. "
                    + "Adding the corresponding expression for b and dividing by two gives Eq. (7). "
                    + "Equation (6) normalizes α_ab by the square root of D_a D_b."),
            Node("IsStationaryNetwork", "A bidirectional network in a steady state", StationaryFormula(),
                "The transition array is nonnegative and a transition is present exactly when its reverse is present. "
                    + "The probability vector has nonnegative entries with total mass one; these are the two "
                    + "conditions of the finite probability predicate. The last equality balances incoming and "
                    + "outgoing probability at each state, as in Eq. (1). Diagonal terms of w cancel from that equality. "
                    + "Equivalently, the generator has off-diagonal entries w(m,n) and diagonal entry "
                    + "−Σ_(k ≠ m) w(k,m)."),
            Node("claim", "The proposed activity bound for every network", ClaimFormula(),
                "The conjecture after Eq. (9) extends Eq. (8) from a single cycle to arbitrary networks. "
                    + "It quantifies over every N at least three, every bidirectional network in a steady state "
                    + "with a positive one-way flux, and every pair of real observables with D_a D_b positive. "
                    + "The left side is the absolute normalized asymmetry |χ_ab| of Eq. (6)."),
            Describe.Lean(
                DescribeId.Create("cross-correlation-activity-bound-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A sixteen-state counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(N("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take the states 0 through 15. Along the oriented hexagon 0 → 1 → 2 → 3 → 4 → 5 → 0, "
                            + "give each forward transition rate 201/200 and each reverse transition rate 199/200. "
                            + "Join every pair of distinct states in {0,6,7,8,9,10,11,12,13,14,15} by a transition "
                            + "of rate one in each direction. All remaining entries of w are zero. "
                            + "At every state the total incoming and outgoing transition rate agree, "
                            + "so p(m) = 1/16 is a steady state.")),
                    Paragraph(Text(
                        "On states 0 through 5, respectively, take a = (1,1/2,−1/2,−1,−1/2,1/2) and "
                            + "b = (0,√3/2,√3/2,0,−√3/2,−√3/2), the coordinates of a regular hexagon. "
                            + "On each state k from 6 through 15, take a(k) = (1005 − k)/1000 and b(k) = 0. "
                            + "Thus these last ten a-values are 999/1000 through 990/1000.")),
                    Paragraph(Text(
                        "The positive fluxes have minimum 199/3200 and maximum 201/3200. "
                            + "The finite sums give γ = 201/199, A = 61/8, σ = (3/800) log(201/199), "
                            + "α_ab = 3√3/3200, D_a = 300121/1600000 and D_b = 3/16. "
                            + "Consequently χ_ab² = 45/600242 and both required diffusion factors are positive.")),
                    Paragraph(Text(
                        "Since tan(π/16) > π/16 > 3/16, its reciprocal cot(π/16) is less than 16/3. "
                            + "Also log(201/199) < 2/199. If B is the right side of Eq. (8) for this network, "
                            + "these inequalities give B² < (1072/199)² · (3/12200) · (2/199) "
                            + "= 62055936/865289770200 < 45/600242 = χ_ab². "
                            + "The last comparison is the integer inequality "
                            + "37248579136512 < 38938039659000. Both sides of Eq. (8) are nonnegative, "
                            + "so this contradicts its proposed upper bound.")),
                    Paragraph(Text(
                        "The complete graph contributes equal flux in both directions and hence no entropy production "
                            + "or antisymmetric correlation slope. It raises the activity from 3/4 to 61/8, "
                            + "while its nearly equal a-values add only 121/1600000 to D_a and leave D_b unchanged. "
                            + "The factor involving total activity therefore makes the proposed bound too small. "
                            + "This counterexample concerns the extension to arbitrary networks; the complete graph "
                            + "introduces cycles beyond the hexagon."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gu-2023-cross-correlation-activity-bound-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("cross-correlation-activity-bound-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(N(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Different(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Naturals() => Seq(Mathbb, Grp(N("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(N("R")));
    private static Formula States() => Call("Fin", N("N"));
    private static Formula Vector() => new Formula.TypeArrow(States(), Reals());
    private static Formula RateArray() => new Formula.TypeArrow(States(), Vector());
    private static Formula NetworkBinders(Formula body) =>
        All("N", Naturals(), All("w", RateArray(), All("p", Vector(), body)));
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(N(name), Colon, States())), Sp, Parenthesized(body));
    private static Formula DoubleSum(Formula body) => SumOver("m", SumOver("n", body));
    private static Formula Flux(Formula m, Formula n) => Call("flux", N("w"), N("p"), m, n);
    private static Formula Quantity(string name) => Call(name, N("w"), N("p"));
    private static Formula Diffusion(Formula observable) => Call("diffusion", N("w"), N("p"), observable);
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp, yes,
            Sp, Named("else"), Sp, no);

    private static Formula FluxFormula() => NetworkBinders(
        All("m", States(), All("n", States(),
            Equal(Flux(N("m"), N("n")), Conditional(Equal(N("m"), N("n")), D(0),
                Mul(At(N("w"), N("m"), N("n")), At(N("p"), N("n"))))))));

    private static Formula ActivityFormula() => NetworkBinders(
        Equal(Quantity("activity"), DoubleSum(Flux(N("m"), N("n")))));

    private static Formula EntropyFormula()
    {
        var forward = Flux(N("m"), N("n"));
        var reverse = Flux(N("n"), N("m"));
        return NetworkBinders(Equal(Quantity("entropyRate"), DoubleSum(
            Conditional(Less(D(0), forward), Mul(forward, Call("log", Div(forward, reverse))), D(0)))));
    }

    private static Formula RatioFormula()
    {
        var values = Seq(OpenBrace, N("x"), Colon, Reals(), Sp, Mid, Sp,
            Some("m", States(), Some("n", States(),
                And(Equal(N("x"), Flux(N("m"), N("n"))), Less(D(0), N("x"))))), CloseBrace);
        return NetworkBinders(Equal(Quantity("scaleRatio"), Div(Call("sSup", values), Call("sInf", values))));
    }

    private static Formula AsymFormula() => NetworkBinders(All("a", Vector(), All("b", Vector(),
        Equal(Call("asym", N("w"), N("p"), N("a"), N("b")), Mul(Div(D(1), D(2)), DoubleSum(
            Mul(Parenthesized(Subtract(Mul(At(N("a"), N("n")), At(N("b"), N("m"))),
                Mul(At(N("a"), N("m")), At(N("b"), N("n"))))), Flux(N("m"), N("n")))))))));

    private static Formula DiffusionFormula() => NetworkBinders(All("a", Vector(),
        Equal(Diffusion(N("a")), Mul(Div(D(1), D(2)), DoubleSum(
            Mul(Square(Subtract(At(N("a"), N("m")), At(N("a"), N("n")))), Flux(N("m"), N("n"))))))));

    private static Formula StationaryFormula()
    {
        var nonnegative = All("m", States(), All("n", States(), Le(D(0), At(N("w"), N("m"), N("n")))));
        var bidirectional = All("m", States(), All("n", States(),
            IffFormula(Different(At(N("w"), N("m"), N("n")), D(0)),
                Different(At(N("w"), N("n"), N("m")), D(0)))));
        var probability = And(All("m", States(), Le(D(0), At(N("p"), N("m")))),
            Equal(SumOver("m", At(N("p"), N("m"))), D(1)));
        var balance = All("m", States(), Equal(
            SumOver("n", Mul(At(N("w"), N("m"), N("n")), At(N("p"), N("n")))),
            Mul(Parenthesized(SumOver("k", At(N("w"), N("k"), N("m")))), At(N("p"), N("m")))));
        return NetworkBinders(IffFormula(Quantity("IsStationaryNetwork"),
            And(nonnegative, And(bidirectional, And(probability, balance)))));
    }

    private static Formula ClaimFormula()
    {
        var product = Mul(Diffusion(N("a")), Diffusion(N("b")));
        var positiveFlux = Some("m", States(), Some("n", States(), Less(D(0), Flux(N("m"), N("n")))));
        var left = Div(new Formula.Absolute(Call("asym", N("w"), N("p"), N("a"), N("b"))), Root(product));
        var right = Mul(Div(Quantity("scaleRatio"), Call("tan", Div(Seq(Pi), N("N")))),
            Root(Div(Quantity("entropyRate"), Mul(D(2), Quantity("activity")))));
        return IffFormula(N("claim"), All("N", Naturals(), Imp(Le(D(3), N("N")),
            All("w", RateArray(), All("p", Vector(), All("a", Vector(), All("b", Vector(),
                Imp(Quantity("IsStationaryNetwork"), Imp(positiveFlux,
                    Imp(Less(D(0), product), Le(left, right)))))))))));
    }
}
