using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class SinhPowerPrimePeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/SinhPowerPrimePeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/bala2022a224899");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A224899 has period p-1 modulo every odd prime, and the assertion fails at p=2.",
        H("The Prime-Period Question for OEIS A224899"),
        Blocks(
            Paragraph(Text("Library note bala2022a224899 records the exponential generating "
                + "function in OEIS A224899 and Peter Bala's May 29, 2022 conjecture. "
                + "The sequence a is defined by its finite exponential coefficient "
                + "expansion through H. The exponential generating function identity "
                + "itself is not formalized. The asserted period need not be minimal.")),
            Paragraph(Text("All indices, bounds, exponents, and subtractions in exponents "
                + "are natural numbers. The notation range(t) means the natural numbers "
                + "strictly below t. The functions H and a take integer values; choose, "
                + "factorial, and stirlingSecond denote Nat.choose, Nat.factorial, and "
                + "Nat.stirlingSecond, cast to the ambient ring when multiplied. "
                + "In H and the coefficient bridge all value arithmetic is integer "
                + "arithmetic, including 2*j-k and the negation of k. The function "
                + "div is integer division, whose exactness follows from the bridge. "
                + "The notation residue(p,t) casts t to ZMod p. In the exponential "
                + "sum all arithmetic outside indices, bounds, exponents, and residue "
                + "arguments is in ZMod p; inv denotes the field inverse.")),
            Node("H", "The finite exponential coefficient", CoefficientFormula(),
                "The coefficient expression expands the kth power of "
                + "exp(k*x)-exp(-k*x), divided by 2^k. The sign convention "
                + "(-1)^(k-j) pairs with the base k*(2*j-k).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("coefficient_bridge", "The factorial-bearing Stirling bridge", BridgeFormula(),
                "Expand (2*j-k)^n by the binomial theorem and interchange the two "
                + "finite sums. Stirling inclusion-exclusion evaluates the inner "
                + "alternating power sum as factorial(k)*stirlingSecond(r,k). "
                + "When r is less than k this vanishes; otherwise 2^r equals "
                + "2^k times 2^(r-k). Factoring out 2^k proves that the integer "
                + "division is exact and leaves the displayed factor factorial(k).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a", "The sequence A224899", SequenceFormula(),
                "Sum the finite exponential coefficients over k at most n, including "
                + "the constant contribution at n=0. This is the coefficient "
                + "expression described in bala2022a224899.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("a_window", "A fixed prime-sized window", WindowFormula(),
                "If k exceeds n, every stirlingSecond(r,k) in the bridge is zero. "
                + "If k is at least p, the prime p divides factorial(k), so the "
                + "coefficient vanishes modulo p. Extending or truncating the "
                + "finite sum therefore gives exactly range(p), even at n=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a_exponential_sum", "An exponential sum independent of the index", ExponentialFormula(),
                "For a prime p different from 2, the residue of 2 is nonzero. "
                + "Cast the exact integer division defining H into ZMod p, "
                + "invert 2^k, and distribute through the fixed window. "
                + "Both the coefficients and the index sets are independent of n.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bala_conjecture_odd", "Bala's assertion for every odd prime", OddFormula(),
                "Apply pow_add_pred_prime from AlternatingWeightStirlingPrimePeriod "
                + "to each base k*(2*j-k). Positive n ensures the power identity "
                + "also holds at the zero base. Summing proves the odd-prime "
                + "part of the conjecture recorded in bala2022a224899.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("balaConjectureTwo", "The period-one claim at two", TwoClaimFormula(),
                "This names the p=2 specialization of Bala's conjecture: "
                + "every residue from index one would equal the next residue.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bala_conjecture_two_false", "The prime two refutes the literal conjecture",
                Disp(Seq(Neg, Sp, Parenthesized(Call("balaConjectureTwo")))),
                "The defining finite sum gives a(1)=1 and a(2)=8. Their residues "
                + "modulo 2 differ, contradicting balaConjectureTwo at n=1. "
                + "This certified instance refutes the named period-one claim "
                + "in bala2022a224899; combined with the odd-prime theorem, "
                + "it identifies the only prime exception.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a224899-sinh-power-prime-period"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a224899-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", "k"), Sp,
        Equality(Call("H", N(), K()),
            Call("div", Sum("j", Add(K(), D(1)),
                Mul(Mul(Sign(), Call("choose", K(), J())),
                    Power(Parenthesized(Mul(K(),
                        Parenthesized(Subtract(Mul(D(2), J()), K())))), N()))),
                Power(D(2), K())))));

    private static Formula BridgeFormula() => Disp(Seq(Bound("n", "k"), Sp,
        Equality(Call("H", N(), K()),
            Mul(Mul(Power(K(), N()), Call("factorial", K())),
                Sum("r", Add(N(), D(1)),
                    Mul(Mul(Mul(Call("choose", N(), R()),
                                Power(Parenthesized(Seq(Minus, K())),
                                    Parenthesized(Subtract(N(), R())))),
                            Power(D(2), Parenthesized(Subtract(R(), K())))),
                        Call("stirlingSecond", R(), K())))))));

    private static Formula SequenceFormula() => Disp(Seq(Bound("n"), Sp,
        Equality(Call("a", N()), Sum("k", Add(N(), D(1)), Call("H", N(), K())))));

    private static Formula WindowFormula() => Disp(Seq(Bound("p", "n"), Sp,
        Implication(Call("Prime", P()),
            Equality(Residue(Call("a", N())),
                Sum("k", P(), Residue(Call("H", N(), K())))))));

    private static Formula ExponentialFormula() => Disp(Seq(Bound("p", "n"), Sp,
        Implication(Call("Prime", P()), Implication(Seq(P(), Sp, Neq, Sp, D(2)),
            Equality(Residue(Call("a", N())), Sum("k", P(),
                Sum("j", Add(K(), D(1)),
                    Mul(Mul(Power(Call("inv", D(2)), K()),
                            Parenthesized(Mul(Sign(), Residue(Call("choose", K(), J()))))),
                        Power(Parenthesized(Mul(Residue(K()),
                            Parenthesized(Subtract(Mul(D(2), Residue(J())), Residue(K()))))),
                            N())))))))));

    private static Formula OddFormula() => Disp(Seq(Bound("p", "n"), Sp,
        Implication(Call("Prime", P()), Implication(Seq(P(), Sp, Neq, Sp, D(2)),
            Implication(Seq(D(1), Sp, Le, Sp, N()),
                Equality(Residue(Call("a", Add(N(), Parenthesized(Subtract(P(), D(1)))))),
                    Residue(Call("a", N()))))))));

    private static Formula TwoClaimFormula() => Disp(Seq(Call("balaConjectureTwo"), Sp, Iff, Sp,
        Parenthesized(Seq(Bound("n"), Sp, Implication(Seq(D(1), Sp, Le, Sp, N()),
            Equality(Residue(Call("a", Add(N(), D(1))), D(2)),
                Residue(Call("a", N()), D(2))))))));

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula J() => F.Id("j");
    private static Formula R() => F.Id("r");
    private static Formula P() => F.Id("p");
    private static Formula Sign() =>
        Power(Parenthesized(Seq(Minus, D(1))), Parenthesized(Subtract(K(), J())));
    private static Formula Residue(Formula x, Formula? prime = null) =>
        Call("residue", prime ?? P(), x);
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
