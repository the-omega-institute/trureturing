using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class StirlingPowerFactorialPrimePeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/bala2022a122399");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala's A122399 conjecture: p - 1 is a period modulo every prime p.",
        H("Prime Periods of the Stirling Power-Factorial Sum"),
        Blocks(
            Paragraph(Text("Library note bala2022a122399 records Peter Bala's May 31, 2022 "
                + "conjecture in Vladeta Jovovic's OEIS A122399 entry. This is Tier 1 by "
                + "the conjecture's 2022 date. The asserted period need not be minimal.")),
            Paragraph(Text("All indices and subtraction in indices or exponents are natural. "
                + "The function stirlingSecond is Mathlib's Nat.stirlingSecond, factorial "
                + "is Nat.factorial, choose is Nat.choose, and range(t) is the set of "
                + "natural numbers strictly below t. The notation castZ denotes the "
                + "natural-number cast to the integers; residue(p,t) denotes the "
                + "natural-number cast of t to ZMod p. The inclusion-exclusion identity "
                + "is an integer identity, the definition of a is natural-valued, and "
                + "the last three equalities are in ZMod p.")),
            Node("stirling2_inclusion_exclusion", "Weighted Stirling inclusion-exclusion",
                InclusionExclusionFormula(),
                "The binomial theorem gives the identity at n=0. The identity "
                + "choose(k,j)(k+1)=choose(k+1,j)(k+1-j) makes the alternating sum "
                + "satisfy the factorial-weighted Stirling recurrence. Induction on n, "
                + "including the k=0 boundary, proves the formula for every n and k.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a", "The OEIS finite sum", SequenceFormula(),
                "This natural-valued finite sum is exactly the NAME in OEIS A122399, "
                + "including its offset-zero convention.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("a_eq_window", "A fixed window modulo each prime", WindowFormula(),
                "When n+1 is at most p, the added terms vanish because the Stirling "
                + "numbers vanish above the diagonal. When p is at most n+1, the "
                + "removed terms vanish modulo p because p divides k! for k at least p. "
                + "This identity holds even at n=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bala_conjecture", "Bala's prime-period conjecture", PeriodFormula(false),
                "Inclusion-exclusion turns the fixed window into a double sum whose "
                + "summands are (-1)^(k-j) choose(k,j) (k*j)^n in ZMod p. For nonzero "
                + "bases, Fermat's little theorem gives period p-1. For zero bases, "
                + "both positive powers vanish. Summing gives the conjectured equality "
                + "for every positive n and every prime p.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a122399-stirling-power-factorial-prime-period"),
                    ResolutionKind.Proved)),
            Node("bala_conjecture_periodic", "Every multiple of the period", PeriodFormula(true),
                "Induction on m repeatedly applies the prime-period theorem at the "
                + "positive index n+m(p-1). Thus the sequence is purely periodic on "
                + "positive indices with period p-1; minimality is not asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a122399-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula InclusionExclusionFormula() => Disp(Seq(Bound("n", "k"), Sp,
        Equality(Mul(CastZ(Call("factorial", K())), CastZ(Stirling())),
            Sum("j", Add(K(), D(1)),
                Mul(Mul(Power(Parenthesized(Seq(Minus, D(1))), Subtract(K(), J())),
                    CastZ(Call("choose", K(), J()))), Power(CastZ(J()), N()))))));

    private static Formula SequenceFormula() => Disp(Seq(Bound("n"), Sp,
        Equality(Call("a", N()), Sum("k", Add(N(), D(1)), Summand()))));

    private static Formula WindowFormula() => Disp(Seq(Bound("p", "n"), Sp,
        Implication(Call("Prime", P()),
            Equality(Residue(Call("a", N())), Sum("k", P(), Residue(Summand()))))));

    private static Formula PeriodFormula(bool multiple)
    {
        var period = Parenthesized(Subtract(P(), D(1)));
        var shift = multiple ? Mul(M(), period) : period;
        return Disp(Seq(multiple ? Bound("p", "n", "m") : Bound("p", "n"), Sp,
            Implication(Call("Prime", P()),
                Implication(Seq(D(1), Sp, Le, Sp, N()),
                    Equality(Residue(Call("a", Add(N(), shift))), Residue(Call("a", N())))))));
    }

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula J() => F.Id("j");
    private static Formula P() => F.Id("p");
    private static Formula M() => F.Id("m");
    private static Formula Stirling() => Call("stirlingSecond", N(), K());
    private static Formula Summand() => Mul(Mul(Power(K(), N()), Call("factorial", K())), Stirling());
    private static Formula CastZ(Formula x) => Call("castZ", x);
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
