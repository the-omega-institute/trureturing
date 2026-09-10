using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class AlternatingWeightStirlingPrimePeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/AlternatingWeightStirlingPrimePeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/bala2022a220181");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer-weight Stirling power sums have prime periods, proving Bala's A220181 conjecture.",
        H("Prime Periods for Integer-Weighted Stirling Sums"),
        Blocks(
            Paragraph(Text("Library note bala2022a220181 records the NAME and finite FORMULA "
                + "of OEIS A220181 and Peter Bala's June 1, 2022 conjecture. The sequence "
                + "here is defined by that finite formula. The exponential generating "
                + "function identity is not separately formalized. The period p-1 is "
                + "not asserted to be minimal.")),
            Paragraph(Text("All indices, range bounds, and subtractions in exponents are "
                + "natural numbers. The weight w maps natural numbers to integers. The "
                + "functions aw and a are integer-valued; stirlingSecond, choose, and "
                + "factorial denote Nat.stirlingSecond, Nat.choose, and Nat.factorial, "
                + "cast to the ambient ring when multiplied. The notation range(t) "
                + "means the natural numbers strictly below t, and residue(p,t) means "
                + "the cast of the integer or natural t to ZMod p. In the exponential "
                + "sum all arithmetic outside range bounds, exponents, and residue "
                + "arguments is in ZMod p. The alternating-weight identity is in the integers.")),
            Node("aw", "The arbitrary integer-weight sum", WeightedSequenceFormula(),
                "The weight depends only on the summation index k.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("aw_window", "A fixed prime-sized window", WindowFormula(),
                "Terms beyond n vanish by the Stirling diagonal bound. Terms with "
                + "k at least p vanish modulo p because p divides k!. Either zero "
                + "remains zero after multiplication by any integer weight. This "
                + "gives the same fixed window also at n=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("aw_exponential_sum", "Index-independent exponential coefficients", ExponentialFormula(),
                "The public stirling2_inclusion_exclusion identity of "
                + "StirlingPowerFactorialPrimePeriod expands the factorial-weighted "
                + "Stirling number. Distributing the weight and combining k^n with "
                + "j^n gives the base k*j and a coefficient independent of n.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("pow_add_pred_prime", "Prime periods of positive powers", PowerPeriodFormula(),
                "For a nonzero base Fermat's little theorem gives x^(p-1)=1. "
                + "For the zero base both powers vanish because n is positive.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("aw_prime_period", "Prime period for every integer weight", PeriodFormula(false, true),
                "Apply the positive-power identity to each base k*j in the fixed "
                + "double sum. Its coefficients are independent of n, so summing "
                + "preserves the equality for every integer-valued weight.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("aw_prime_period_multiple", "Every multiple for every weight", PeriodFormula(true, true),
                "Induction on m applies aw_prime_period at the positive index n+m(p-1).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a", "The finite formula for A220181", SequenceFormula(),
                "This is the offset-zero finite formula recorded in bala2022a220181, "
                + "including the sign (-1)^(n-k).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("a_eq_alternating", "The alternating-weight identity", AlternatingFormula(),
                "For k in range(n+1), k is at most n. Thus (-1)^n times (-1)^k "
                + "equals (-1)^(n-k), since the remaining factor (-1)^(2*k) is one. "
                + "Distribute (-1)^n through the finite sum.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bala_conjecture", "Bala's A220181 prime-period conjecture", PeriodFormula(false, false),
                "Use aw_prime_period with the integer weight k mapped to (-1)^k "
                + "and the alternating-weight identity. When p=2 the sign is one "
                + "in ZMod 2. For every other prime, p-1 is even, so the sign factor "
                + "is unchanged. This proves the conjecture in bala2022a220181.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a220181-alternating-weight-stirling-prime-period"),
                    ResolutionKind.Proved)),
            Node("bala_conjecture_periodic", "Every multiple of the A220181 period", PeriodFormula(true, false),
                "Induction on m applies bala_conjecture at n+m(p-1), which remains positive.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a220181-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula WeightedSequenceFormula() => Disp(Seq(WeightBound(), Sp, Bound("n"), Sp,
        Equality(Call("aw", W(), N()), Sum("k", Add(N(), D(1)), Summand(Call("w", K()))))));

    private static Formula SequenceFormula() => Disp(Seq(Bound("n"), Sp,
        Equality(Call("a", N()), Sum("k", Add(N(), D(1)),
            Summand(Power(NegativeOne(), Parenthesized(Subtract(N(), K()))))))));

    private static Formula WindowFormula() => Disp(Seq(WeightBound(), Sp, Bound("p", "n"), Sp,
        Implication(Call("Prime", P()),
            Equality(Residue(Call("aw", W(), N())),
                Sum("k", P(), Residue(Summand(Call("w", K()))))))));

    private static Formula ExponentialFormula() => Disp(Seq(WeightBound(), Sp, Bound("p", "n"), Sp,
        Implication(Call("Prime", P()),
            Equality(Residue(Call("aw", W(), N())), Sum("k", P(),
                Sum("j", Add(K(), D(1)),
                    Mul(Mul(Residue(Call("w", K())),
                            Parenthesized(Mul(Power(NegativeOne(), Parenthesized(Subtract(K(), J()))),
                                Residue(Call("choose", K(), J()))))),
                        Power(Parenthesized(Mul(Residue(K()), Residue(J()))), N()))))))));

    private static Formula PowerPeriodFormula() => Disp(Seq(Bound("p"), Sp,
        Implication(Call("Prime", P()), Seq(
            Forall, Sp, F.Id("x"), Colon, Sp, Call("ZMod", P()), Comma, Sp, Bound("n"), Sp,
            Implication(Seq(D(1), Sp, Le, Sp, N()),
                Equality(Power(F.Id("x"), Add(N(), Parenthesized(Subtract(P(), D(1))))),
                    Power(F.Id("x"), N())))))));

    private static Formula AlternatingFormula() => Disp(Seq(Bound("n"), Sp,
        Equality(Call("a", N()), Mul(Power(NegativeOne(), N()),
            Call("aw", Parenthesized(Seq(K(), Sp, Mapsto, Sp, Power(NegativeOne(), K()))), N())))));

    private static Formula PeriodFormula(bool multiple, bool weighted)
    {
        var period = Parenthesized(Subtract(P(), D(1)));
        var shift = multiple ? Mul(M(), period) : period;
        var statement = Seq(multiple ? Bound("p", "n", "m") : Bound("p", "n"), Sp,
            Implication(Call("Prime", P()),
                Implication(Seq(D(1), Sp, Le, Sp, N()),
                    Equality(Residue(SequenceAt(Add(N(), shift), weighted)),
                        Residue(SequenceAt(N(), weighted))))));
        return Disp(weighted ? Seq(WeightBound(), Sp, statement) : statement);
    }

    private static Formula SequenceAt(Formula index, bool weighted) =>
        weighted ? Call("aw", W(), index) : Call("a", index);
    private static Formula WeightBound() => Seq(Forall, Sp, W(), Colon, Sp,
        Mathbb, Grp(F.Id("N")), Sp, To, Sp, Mathbb, Grp(F.Id("Z")), Comma);
    private static Formula W() => F.Id("w");
    private static Formula J() => F.Id("j");
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula P() => F.Id("p");
    private static Formula M() => F.Id("m");
    private static Formula NegativeOne() => Parenthesized(Seq(Minus, D(1)));
    private static Formula Summand(Formula weight) => Mul(
        Mul(Mul(weight, Power(K(), N())), Call("factorial", K())),
        Call("stirlingSecond", N(), K()));
    private static Formula Residue(Formula x) => Call("residue", P(), x);
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
