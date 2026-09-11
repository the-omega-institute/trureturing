using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class TanhPowerPrimePeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/TanhPowerPrimePeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/bala2022a221077");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The double Stirling formula has period p-1 at every odd prime and fails at p=2.",
        H("Odd-Prime Periods of the A221077 Double Stirling Formula"),
        Blocks(
            Paragraph(Text("Library note bala2022a221077 quotes the exponential generating "
                + "function and Peter Bala's conjecture for OEIS A221077. The function a "
                + "here takes the derived finite formula (9) as its definition, with a(0)=1. "
                + "The link to the exponential generating function is derived in the note "
                + "but is not formalized. The period results below concern this finite "
                + "formula, and do not assert that p-1 is a minimal period.")),
            Paragraph(Text("All indices, bounds, and subtractions in exponents and factorial "
                + "arguments are natural numbers. The function a is natural-valued. "
                + "The symbols stirlingSecond, factorial, and choose denote Nat.stirlingSecond, "
                + "Nat.factorial, and Nat.choose. The set Ico(1,t) consists of 1 through t-1, "
                + "and range(t) consists of 0 through t-1. The notation residue(p,t) denotes "
                + "the cast of t through the integers to ZMod p. In the window and "
                + "exponential sum, arithmetic outside bounds, exponents, and residue "
                + "arguments is in ZMod p; inv denotes its inverse operation. "
                + "The symbol twoClaim names the proposition bala_conjecture_two.")),
            Node("a", "The defining double Stirling formula", SequenceFormula(),
                "The positive-index sum is formula (9) in bala2022a221077. "
                + "At index zero the value is one.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("a_window", "A fixed prime window", WindowFormula(),
                "When m exceeds n, stirlingSecond(n,m) vanishes. When m is at least p, "
                + "p divides factorial(m). Extending or restricting the sum therefore "
                + "leaves exactly Ico(1,p), for every prime p and positive n.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a_exponential_sum", "A fixed triple sum of powers", ExponentialFormula(),
                "For m in Ico(1,p), factorial(m-1) equals inv(residue(p,m)) times "
                + "residue(p,factorial(m)). If m is at most n, the power of two splits "
                + "into its n-th power times the m-th power of its inverse; otherwise "
                + "stirlingSecond(n,m) is zero. Expand both factorial-weighted Stirling "
                + "factors by stirling2_inclusion_exclusion, distribute both finite sums, "
                + "and combine the powers into the base 2*residue(p,j)*residue(p,k).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bala_conjecture_odd", "Bala's period at every odd prime", OddPeriodFormula(),
                "Apply the frozen pow_add_pred_prime theorem to each base in the fixed "
                + "triple sum. Its coefficients are independent of n. Thus the odd-prime "
                + "part of the conjecture in bala2022a221077 holds for formula (9).",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("bala_conjecture_two", "The named prime-two claim", TwoClaimFormula(),
                "This proposition is the p=2 instance of the conjectured period for "
                + "formula (9); the period is 2-1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bala_conjecture_two_false", "Refutation at the prime two",
                Disp(Seq(Neg, Sp, Named("twoClaim"))),
                "Specialize twoClaim to n=1. The defining sum gives a(1)=1 and a(2)=8. "
                + "Their residues modulo 2 differ, so the claimed period one fails.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a221077-tanh-power-prime-period"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a221077-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula SequenceFormula() => Disp(Seq(Bound("n"), Sp,
        Equality(Call("a", N()), Seq(Named("if"), Sp,
            Parenthesized(Equality(N(), D(0))), Sp, Named("then"), Sp, D(1), Sp,
            Named("else"), Sp, Sum("m", Call("Ico", D(1), Add(N(), D(1))),
                Product(Power(D(2), Subtract(N(), M())), Call("factorial", M()),
                    Call("factorial", Subtract(M(), D(1))),
                    Call("stirlingSecond", N(), M()),
                    Call("stirlingSecond", Add(N(), D(1)), M())))))));

    private static Formula WindowFormula() => Disp(Seq(Bound("p", "n"), Sp,
        Hypotheses(false, Equality(Residue(P(), Call("a", N())),
            Sum("m", Call("Ico", D(1), P()),
                Product(Power(D(2), Subtract(N(), M())), Residue(P(), Call("factorial", M())),
                    Residue(P(), Call("factorial", Subtract(M(), D(1)))),
                    Residue(P(), Call("stirlingSecond", N(), M())),
                    Residue(P(), Call("stirlingSecond", Add(N(), D(1)), M()))))))));

    private static Formula ExponentialFormula()
    {
        var coefficient = Product(Power(Call("inv", D(2)), M()), Call("inv", Residue(P(), M())),
            Parenthesized(Product(Power(NegativeOne(), Subtract(M(), J())),
                Residue(P(), Call("choose", M(), J())))),
            Parenthesized(Product(Power(NegativeOne(), Subtract(M(), K())),
                Residue(P(), Call("choose", M(), K())))), Residue(P(), K()));
        var body = Product(Parenthesized(coefficient),
            Power(Parenthesized(Product(D(2), Residue(P(), J()), Residue(P(), K()))), N()));
        return Disp(Seq(Bound("p", "n"), Sp, Hypotheses(true,
            Equality(Residue(P(), Call("a", N())),
                Sum("m", Call("Ico", D(1), P()),
                    Sum("j", Call("range", Add(M(), D(1))),
                        Sum("k", Call("range", Add(M(), D(1))), body)))))));
    }

    private static Formula OddPeriodFormula() => Disp(Seq(Bound("p", "n"), Sp,
        Hypotheses(true, Period(P()))));

    private static Formula TwoClaimFormula() => Disp(Seq(Named("twoClaim"), Sp, Iff, Sp,
        Parenthesized(Seq(Bound("n"), Sp,
            Implication(Seq(D(1), Sp, Le, Sp, N()), Period(D(2)))))));

    private static Formula Period(Formula p) => Equality(
        Residue(p, Call("a", Add(N(), Parenthesized(Subtract(p, D(1)))))),
        Residue(p, Call("a", N())));

    private static Formula Hypotheses(bool odd, Formula conclusion)
    {
        var positive = Implication(Seq(D(1), Sp, Le, Sp, N()), conclusion);
        if (odd) positive = Implication(Seq(P(), Sp, Neq, Sp, D(2)), positive);
        return Implication(Call("Prime", P()), positive);
    }

    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula J() => F.Id("j");
    private static Formula K() => F.Id("k");
    private static Formula P() => F.Id("p");
    private static Formula NegativeOne() => Parenthesized(Seq(Minus, D(1)));
    private static Formula Residue(Formula p, Formula x) => Call("residue", p, x);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Equality(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Implication(Formula x, Formula y) => Seq(x, Sp, Implies, Sp, y);
    private static Formula Power(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Subtract(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Product(params Formula[] factors)
    {
        var result = factors[0];
        for (int i = 1; i < factors.Length; i++)
            result = new Formula.Binary(result, FormulaBinaryOperator.Multiply, factors[i]);
        return result;
    }
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Sum(string variable, Formula set, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id(variable), Sp, InMacro, Sp, set)),
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
