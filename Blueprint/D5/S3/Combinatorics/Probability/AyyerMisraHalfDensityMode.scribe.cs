using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class AyyerMisraHalfDensityModeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ayyermisra2024kexclusion");
    private const string Question =
        "Section 4.5, page 21: “We focus on when t ≪ 1 and t ≫ 1. From the discussion in Sections 4.2 "
        + "and 4.3, we know that the most likely number of particles is either k or k + 1. "
        + "The question we want to address is which one is most likely.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The half-density K-exclusion mode for small and large positive parameters.",
        H("Half-density modes of the asymmetric K-exclusion process"),
        Blocks(
            Node("qnum", "The t-integer", All("t", R, All("k", Nat,
                Equal(Call("qnum", X("t"), X("k")),
                    SumOn("j", App(Q("Finset", "range"), X("k")), Pow(X("t"), X("j")))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 4: “We define the t-analog of a nonnegative integer k as”. Equation (4) is [k] ≡ [k]t = ∑ᵢ₌₀ᵏ⁻¹ tⁱ. The sum over range k also gives [0] = 0."),
            Node("qfact", "The t-factorial", All("t", R, All("k", Nat,
                Equal(Call("qfact", X("t"), X("k")),
                    ProductOn("j", App(Q("Finset", "range"), X("k")),
                        Call("qnum", X("t"), Add(X("j"), D(1))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 6: “The t-analogue of the factorial is given by”. Equation (8) is [k]! ≡ [k]t! = [1][2] · · · [k]. The empty product is one."),
            Node("qbinom", "The t-binomial coefficient", All("t", R, All("k", Nat, All("i", Nat,
                Equal(Call("qbinom", X("t"), X("k"), X("i")), Parenthesized(Seq(
                    Word("if"), Sp, Leq(X("i"), X("k")), Sp, Word("then"), Sp,
                    Div(Call("qfact", X("t"), X("k")),
                        Mul(Call("qfact", X("t"), Subtract(X("k"), X("i"))),
                            Call("qfact", X("t"), X("i")))),
                    Sp, Word("else"), Sp, D(0))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 6: “The t-binomial coefficient or Gaussian polynomial is”. Equation (9) is [k choose i] ≡ [k choose i]t = [k]! / ([k − i]![i]!). "
                + "It is zero when i exceeds k. All indices are natural numbers and their subtraction is truncated."),
            Node("wt", "The steady-state weight", WithConfiguration(All("t", R,
                All("eta", ConfigurationType(), Equal(Call("wt", X("K"), X("L"), X("t"), X("eta")),
                    ProductOn("i", Call("Fin", X("L")), Mul(
                        Pow(X("t"), App(Q("Nat", "div"),
                            Subtract(Add(Mul(ValAt("eta", X("i")), ValAt("eta", X("i"))), D(2)),
                                Mul(D(3), ValAt("eta", X("i")))), D(2))),
                        Call("qbinom", X("t"), X("K"), ValAt("eta", X("i"))))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 6: “We will show in Section 3 that the steady state weight is given by the formula,” "
                + "Equation (11) is wtη(t) = ∏ᵢ t^((ηᵢ−1)(ηᵢ−2)/2) [K choose ηᵢ]. "
                + "For natural a the exponent is Nat.div (a*a+2−3*a) 2; subtraction is truncated. "
                + "Its values for a = 0,1,2,3,4 are 1,0,0,1,3."),
            Node("configs", "Configurations with a fixed particle count", WithConfiguration(All("n", Nat,
                Equal(Call("configs", X("K"), X("L"), X("n")),
                    Filter(Lambda("eta", ConfigurationType(), Equal(
                        SumOn("i", Call("Fin", X("L")), ValAt("eta", X("i"))), X("n"))),
                        Typed(Q("Finset", "univ"), Call("Finset", ConfigurationType())))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 4: “We denote the set of configurations by” ΩL,n ≡ ΩK L,n = {η ∈ {0, 1, . . . , K}ᴸ | ∑ᵢ₌₁ᴸ ηᵢ = n}. "
                + "A configuration is a function from Fin L to Fin (K+1); "
                + "the sum of its natural values is n."),
            Node("occProb", "The one-site marginal", WithConfiguration(All("n", Nat, All("t", R,
                All("s", Call("Fin", X("L")), All("a", Nat, Equal(
                    Call("occProb", X("K"), X("L"), X("n"), X("t"), X("s"), X("a")),
                    Div(SumOn("eta", Filter(Lambda("eta", ConfigurationType(),
                                Equal(ValAt("eta", X("s")), X("a"))),
                            Call("configs", X("K"), X("L"), X("n"))),
                            Call("wt", X("K"), X("L"), X("t"), X("eta"))),
                        SumOn("eta", Call("configs", X("K"), X("L"), X("n")),
                            Call("wt", X("K"), X("L"), X("t"), X("eta")))))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 6: “Then the steady state probability of η is”. Equation (13) is π(η) = wtη(t) / ZL,n(t). Summing this distribution over "
                + "configurations whose s-th value is a gives the displayed marginal. The numerator and "
                + "denominator use exactly the weights of equation (11)."),
            Node("claim", "The answer to the half-density question", Equal(X("claim"), Parenthesized(ClaimBody())),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                Question + " The answer concerns L = 2r with r ≥ 2, K ≥ 1, k < K and n = (2k+1)r. "
                + "The site s is the element of Fin (2r) with value zero. For all sufficiently small positive t "
                + "and all sufficiently large t, the unique mode is k below half filling and k+1 above half filling. "
                + "At exact half filling k and k+1 tie and dominate the other occupations in these two regimes."),
            Node("result", "The modal comparisons in both parameter extremes", ClaimBody(),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "The finite t-binomial identity expresses the weights as sums over occupied slots with energy "
                + "equal to the sum of their levels. Reflecting the block of levels 0 through 2k and then "
                + "taking its complement pairs the adjacent occupations while preserving particle count and energy. "
                + "Below half filling, the first unpaired energy layer has an excess of "
                + "3*Nat.choose (2r−1) (r−2) configurations favouring k. Its positivity determines the sign "
                + "near zero. Particle-hole symmetry gives the comparison above half filling and the exact tie. "
                + "Every marginal is unchanged by replacing t by its reciprocal, so the same comparisons "
                + "hold for large t. The classification for intermediate positive t remains open."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        DescribeRole role, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("ayyer-misra-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Word(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula Q(string owner, string name) => Seq(Word(owner), Dot, Word(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Word("fun"), Sp, X(name), Colon, type, Sp, Mapsto, Sp, body));
    private static Formula SumOn(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), InMacro, Sp, domain)), Sp, body);
    private static Formula ProductOn(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(X(name), InMacro, Sp, domain)), Sp, body);
    private static Formula Filter(Formula predicate, Formula set) => App(Q("Finset", "filter"), predicate, set);
    private static Formula ConfigurationType() => new Formula.TypeArrow(Call("Fin", X("L")), Call("Fin", Parenthesized(Add(X("K"), D(1)))));
    private static Formula WithConfiguration(Formula body) => All("K", Nat, All("L", Nat, body));
    private static Formula ValAt(string name, Formula i) => Call("val", Call(name, i));

    private static Formula ClaimBody()
    {
        Formula r = X("r"), k = X("k"), cap = X("K"), t = X("t"), e = X("e"), b = X("b");
        Formula level = Add(Mul(D(2), k), D(1));
        Formula size = Mul(D(2), r);
        Formula n = Mul(Parenthesized(level), r);
        Formula lower = Imp(Less(level, cap), All("b", Nat, Imp(Leq(b, cap),
            Imp(Ne(b, k), Less(Probability(b), Probability(k))))));
        Formula upper = Imp(Less(cap, level), All("b", Nat, Imp(Leq(b, cap),
            Imp(Ne(b, Add(k, D(1))), Less(Probability(b), Probability(Add(k, D(1))))))));
        Formula middle = Imp(Equal(level, cap), And(Equal(Probability(k), Probability(Add(k, D(1)))),
            All("b", Nat, Imp(Leq(b, cap), Imp(Ne(b, k), Imp(Ne(b, Add(k, D(1))),
                Less(Probability(b), Probability(k))))))));
        Formula regimes = Some("e", R, And(Less(D(0), e), All("t", R,
            Imp(Less(D(0), t), Imp(Or(Less(t, e), Less(Div(D(1), e), t)), And(lower, And(upper, middle)))))));
        Formula site = Seq(Word("let"), Sp, X("s"), Colon, Call("Fin", size), Eq, D(0), Semi, Sp, regimes);
        return All("r", Nat, All("K", Nat, All("k", Nat, Imp(Leq(D(2), r),
            Imp(Leq(D(1), cap), Imp(Less(k, cap), Parenthesized(site)))))));

        Formula Probability(Formula a) => Call("occProb", cap, size, n, t, X("s"), a);
    }
}
