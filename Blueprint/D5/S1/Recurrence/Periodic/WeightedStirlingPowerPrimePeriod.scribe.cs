using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class WeightedStirlingPowerPrimePeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/WeightedStirlingPowerPrimePeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/bala2022a338040");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala's A338040 conjecture: p - 1 is a period modulo every prime p.",
        H("Prime Periods of the Weighted Stirling Power Sum"),
        Blocks(
            Paragraph(Text("Library note bala2022a338040 records Peter Bala's May 31, 2022 "
                + "conjecture in Vaclav Kotesovec's OEIS A338040 entry. The entry defines "
                + "the sequence by an exponential generating function and states the finite "
                + "formula used here. The exponential generating function identity is not "
                + "separately formalized. The asserted period need not be minimal.")),
            Paragraph(Text("All indices and subtraction are natural. The function "
                + "stirlingSecond is Mathlib's Nat.stirlingSecond, factorial is Nat.factorial, "
                + "and range(t) consists of natural numbers strictly below t. The notation "
                + "residue(p,t) is the natural-number cast of t to ZMod p. The definition "
                + "of a is natural-valued; the three theorem equalities are in ZMod p.")),
            Node("a", "The OEIS finite formula", SequenceFormula(),
                "This is the entry's offset-zero finite formula, including the weight 4^k.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("a_eq_window", "A fixed weighted window modulo each prime", WindowFormula(),
                "When n+1 is at most p, the added terms vanish by the Stirling diagonal "
                + "bound. When p is at most n+1, the removed terms vanish modulo p because "
                + "p divides k! for k at least p. Multiplication by 4^k preserves these "
                + "zero terms. The result holds also at index zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bala_conjecture", "Bala's prime-period conjecture", PeriodFormula(false),
                "The inclusion-exclusion theorem in StirlingPowerFactorialPrimePeriod "
                + "turns the window into a double sum with summands "
                + "4^k (-1)^(k-j) choose(k,j) (k*j)^n in ZMod p. The weights are "
                + "independent of n. Fermat's little theorem gives period p-1 for "
                + "nonzero bases; both powers vanish for zero bases at positive indices. "
                + "Summing proves the equality for every prime p and every positive n.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a338040-weighted-stirling-power-prime-period"),
                    ResolutionKind.Proved)),
            Node("bala_conjecture_periodic", "Every multiple of the period", PeriodFormula(true),
                "Induction on m applies the prime-period equality at the positive index "
                + "n+m(p-1), proving preservation by every nonnegative multiple of p-1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a338040-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, claim);

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
    private static Formula P() => F.Id("p");
    private static Formula M() => F.Id("m");
    private static Formula Summand() => Mul(
        Mul(Mul(Power(D(4), K()), Power(K(), N())), Call("factorial", K())),
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
