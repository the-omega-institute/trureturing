using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class StirlingTransformTotientPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/bala2018a064618");

    private static readonly LibraryNoteRef SourceA004123 =
        LibraryNoteRef.Create("D5/L/Recurrence/bala2022a004123");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Stirling transforms have totient periods, proving A064618 and A004123.",
        H("Totient Periods for Weighted Stirling Transforms"),
        Blocks(
            Paragraph(Text("Library note bala2018a064618 records the A064618 conjecture and "
                + "note bala2022a004123 the A004123 conjecture. The former has "
                + "weight k! and offset zero; the latter has weight 2^k and offset one, "
                + "so its term at index n is T(k mapped to 2^k,n-1). The proved onsets "
                + "are n at least m and n at least m+1, respectively. Neither onset "
                + "nor period is asserted to be minimal. The broader A004123 conjecture "
                + "about every e.g.f. G(exp(x)-1) is not claimed here.")),
            Paragraph(Text("All indices, range bounds, and exponent subtractions are "
                + "natural numbers. The weight w maps natural numbers to integers, and "
                + "T is integer-valued. The functions factorial, stirlingSecond, choose, "
                + "and totient denote Nat.factorial, Nat.stirlingSecond, Nat.choose, "
                + "and Nat.totient. Natural factorials and Stirling numbers in the "
                + "definition of T are cast to integers. The notation range(t) means "
                + "the natural numbers strictly below t; residue(m,t) is the cast of "
                + "the integer or natural t to ZMod m. In the exponential sum, "
                + "arithmetic outside bounds, exponents, and residue arguments is in "
                + "ZMod m. The weights in the two instances take their values in the integers.")),
            Node("T", "The weighted Stirling transform", TransformFormula(),
                "The summand is w(k) times k! times S(n,k), with no extra k^n factor.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("T_window", "A fixed modulus-sized window", WindowFormula(),
                "Terms beyond n vanish by the Stirling diagonal bound. For positive "
                + "m, terms with k at least m vanish because m divides k!. These two "
                + "facts give the fixed window for every natural index n, including zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("T_exponential_sum", "Exponential coefficients independent of n", ExponentialFormula(),
                "The public stirling2_inclusion_exclusion identity of "
                + "StirlingPowerFactorialPrimePeriod expands k! times S(n,k). "
                + "Distributing w(k) yields the displayed fixed double sum of powers of j.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("pow_add_totient", "Euler and prime-power divisibility", PowerFormula(),
                "For each prime power p^e dividing m, split according to whether p "
                + "divides j. If it does, e is at most n because e is less than p^e, "
                + "which is at most m; both powers vanish modulo p^e. Otherwise j is "
                + "a unit modulo p^e, so Euler's theorem and phi(p^e) dividing phi(m) "
                + "give the same congruence. Divisibility of the integer difference "
                + "by every prime power dividing m implies divisibility by m.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("stirling_transform_totient_period", "Totient period for every weight", PeriodFormula(),
                "Apply pow_add_totient to each base j in the fixed double sum. "
                + "The coefficients do not depend on n, so the equality survives both "
                + "finite sums for every integer weight. This is a sibling of the "
                + "prime-period theorem with the additional k^n factor: here that "
                + "factor is absent and the modulus can be composite.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bala_conjecture_a064618", "Bala's A064618 totient-period conjecture",
                InstanceFormula(false),
                "Set w(k)=k!. The finite formula in bala2018a064618 is then T(w,n), "
                + "and the general theorem supplies period phi(m) from n at least m.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a064618-stirling-transform-totient-period"),
                    ResolutionKind.Proved)),
            Node("bala_conjecture_a004123", "Bala's A004123 totient-period conjecture",
                InstanceFormula(true),
                "Set w(k)=2^k. The entry's term a(n) is T(w,n-1). If n is at least "
                + "m+1, then n-1 is at least m and n+phi(m)-1 equals (n-1)+phi(m). "
                + "The general theorem therefore gives the claimed period in the "
                + "entry's own offset-one indexing.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SourceA004123),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a004123-generalized-weak-orders-totient-period"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("stirling-totient-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula TransformFormula() => Disp(Seq(WeightBound(), Sp, Bound("n"), Sp,
        Equality(Call("T", W(), N()), Sum("k", Add(N(), D(1)), Summand()))));

    private static Formula WindowFormula() => Disp(Seq(WeightBound(), Sp, Bound("m", "n"), Sp,
        Implication(PositiveModulus(), Equality(Residue(Call("T", W(), N())),
            Sum("k", M(), Residue(Summand()))))));

    private static Formula ExponentialFormula() => Disp(Seq(WeightBound(), Sp, Bound("m", "n"), Sp,
        Implication(PositiveModulus(), Equality(Residue(Call("T", W(), N())),
            Sum("k", M(), Sum("j", Add(K(), D(1)),
                Mul(Mul(Residue(Call("w", K())),
                        Parenthesized(Mul(Power(NegativeOne(), Subtract(K(), J())),
                            Residue(Call("choose", K(), J()))))),
                    Power(Residue(J()), N()))))))));

    private static Formula PowerFormula() => Disp(Seq(Bound("j", "m", "n"), Sp,
        Implication(PositiveModulus(), Implication(AtLeast(M(), N()),
            Equality(Power(Residue(J()), Add(N(), Totient())), Power(Residue(J()), N()))))));

    private static Formula PeriodFormula() => Disp(Seq(WeightBound(), Sp, Bound("m", "n"), Sp,
        Implication(PositiveModulus(), Implication(AtLeast(M(), N()),
            Equality(Residue(Call("T", W(), Add(N(), Totient()))),
                Residue(Call("T", W(), N())))))));

    private static Formula InstanceFormula(bool offsetOne)
    {
        var weight = Parenthesized(Seq(K(), Sp, Mapsto, Sp,
            offsetOne ? Power(D(2), K()) : Call("factorial", K())));
        var shifted = offsetOne ? Subtract(Add(N(), Totient()), D(1)) : Add(N(), Totient());
        var index = offsetOne ? Subtract(N(), D(1)) : N();
        var onset = offsetOne ? Add(M(), D(1)) : M();
        return Disp(Seq(Bound("m", "n"), Sp,
            Implication(PositiveModulus(), Implication(AtLeast(onset, N()),
                Equality(Residue(Call("T", weight, shifted)), Residue(Call("T", weight, index)))))));
    }

    private static Formula Summand() => Mul(Mul(Call("w", K()), Call("factorial", K())),
        Call("stirlingSecond", N(), K()));
    private static Formula PositiveModulus() => Seq(D(0), Sp, Lt, Sp, M());
    private static Formula AtLeast(Formula lower, Formula upper) => Seq(lower, Sp, Le, Sp, upper);
    private static Formula Totient() => Call("totient", M());
    private static Formula Residue(Formula x) => Call("residue", M(), x);
    private static Formula WeightBound() => Seq(Forall, Sp, W(), Colon, Sp,
        Mathbb, Grp(F.Id("N")), Sp, To, Sp, Mathbb, Grp(F.Id("Z")), Comma);
    private static Formula W() => F.Id("w");
    private static Formula J() => F.Id("j");
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula M() => F.Id("m");
    private static Formula NegativeOne() => Parenthesized(Seq(Minus, D(1)));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Equality(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Implication(Formula x, Formula y) => Seq(x, Sp, Implies, Sp, y);
    private static Formula Power(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Subtract(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Sum(string variable, Formula bound, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id(variable), Sp, InMacro, Sp, Call("range", bound))),
        Sp, Parenthesized(body));
    private static Formula Bound(params string[] names)
    {
        List<Formula> variables = [];
        foreach (var name in names)
        {
            if (variables.Count > 0) variables.AddRange([Comma, Sp]);
            variables.Add(F.Id(name));
        }
        return Seq(Forall, Sp, Seq([.. variables]), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma);
    }
}
