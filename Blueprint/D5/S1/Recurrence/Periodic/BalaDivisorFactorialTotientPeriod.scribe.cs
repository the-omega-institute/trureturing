using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class BalaDivisorFactorialTotientPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/bala2025a258899a258903");
    private const string ConjectureSentence =
        "Conjecture: the sequence a(n) taken modulo a positive integer k is eventually "
        + "periodic with the period dividing phi(k).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Divisor-factorial tails prove Bala's A258899 and A258903 totient-period conjectures.",
        H("Totient Periods for Two Divisor-Factorial Sequences"),
        Blocks(
            Paragraph(Text("The source is the COMMENTS and FORMULA fields of OEIS A258899 "
                + "and A258903, which are not paginated. Both sequences have offset zero "
                + "and value 1 at index zero. The modulo-7 example in the A258903 comment "
                + "begins at index 1. All indices, exponents, factorials and sums here "
                + "are natural numbers. Nat.div denotes natural-number division, including "
                + "the factorial quotient; it is not rational division.")),
            Node("a258899", "The sequence A258899", SequenceFormula(false),
                "OEIS A258899, FORMULA: “For n >= 1, a(n) = Sum_{d divides n} "
                + "2^d * n!/(d!*(n/d)!).” The initial value is 1, as in the entry's "
                + "term list and offset. The sum ranges over Nat.divisors n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a258903", "The sequence A258903", SequenceFormula(true),
                "OEIS A258903, FORMULA: “For n >= 1, a(n) = Sum_{d divides n} "
                + "2^d * 3^(n/d) * n!/(d!*(n/d)!).” The initial value is 1, as in "
                + "the entry's term list and offset. The sum ranges over Nat.divisors n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Bala's two conjectures",
                Disp(IffFormula(Named("claim"), ClaimBody())),
                "The COMMENTS field of each entry states: “" + ConjectureSentence
                + "” The modulus k is written m. Each conjunct has its own natural "
                + "onset N and positive natural period T dividing Nat.totient m. "
                + "Nat.ModEq m compares the two natural terms modulo m. Modulus 1 is included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Both totient-period assertions", Disp(ClaimBody()),
                "For n at least 2*m+4 and a proper factorization n=d*e, the inequality "
                + "2*(d+e) <= n+4 gives d+e+m <= n. Factorial divisibility then makes "
                + "m divide n!/(d!*e!). Thus only the factors 1 and n survive in the "
                + "sum modulo m, giving u*v^n+v*u^n for arbitrary natural weights u,v, "
                + "including zero. The theorem "
                + "D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod.pow_add_totient "
                + "makes both powers unchanged by a shift of Nat.totient m. "
                + "Weights (2,1) and (2,3) give the two sequences. In both conjuncts "
                + "N=2*m+4 and T=Nat.totient m suffice. Neither is asserted minimal.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bala-a258899-totient-period"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("bala-divisor-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula SequenceFormula(bool weighted)
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var quotient = NatCall("div", n, d);
        var term = Pow(D(2), d);
        if (weighted) term = Mul(term, Pow(D(3), quotient));
        term = Mul(term, NatCall("div", NatCall("factorial", n),
            Mul(NatCall("factorial", d), NatCall("factorial", quotient))));
        var sum = Seq(new Formula.Subscript(F.Sum,
                Seq(d, Sp, InMacro, Sp, NatCall("divisors", n))),
            Sp, Parenthesized(term));
        var body = Seq(Named("if"), Sp, Equal(n, D(0)), Sp,
            Named("then"), Sp, D(1), Sp, Named("else"), Sp, sum);
        return Disp(All("n", Equal(Call(weighted ? "a258903" : "a258899", n), body)));
    }

    private static Formula ClaimBody() => And(PeriodBody("a258899"), PeriodBody("a258903"));

    private static Formula PeriodBody(string sequence)
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var onset = F.Id("N");
        var period = F.Id("T");
        var tail = All("n", ImpliesFormula(AtMost(onset, n),
            NatCall("ModEq", m, Call(sequence, Add(n, period)), Call(sequence, n))));
        var conditions = And(Less(D(0), period),
            And(Seq(period, Sp, Mid, Sp, NatCall("totient", m)), tail));
        return All("m", ImpliesFormula(Less(D(0), m),
            Some("N", Some("T", conditions))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp, body);
    private static Formula Some(string name, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp, body);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula NatCall(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("Nat"), Dot, F.Id(name))), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula AtMost(Formula left, Formula right) => Seq(left, Sp, Le, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
