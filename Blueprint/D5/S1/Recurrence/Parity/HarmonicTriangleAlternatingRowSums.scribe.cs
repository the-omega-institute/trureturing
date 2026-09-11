using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class HarmonicTriangleAlternatingRowSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Parity/HarmonicTriangleAlternatingRowSums.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/schulte2024a378277");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's alternating row sums of the Fibonacci harmonic triangle have the conjectured closed form.",
        H("Alternating Fibonacci Harmonic Row Sums"),
        Blocks(
            Paragraph(Text("All indices are natural numbers. F denotes Nat.fib, with F(0)=0 "
                + "and F(1)=1. Index and exponent subtraction is natural subtraction. "
                + "The denominator is natural-valued, the row sums and their differences "
                + "are rational, and the two-step Cassini identity is an integer identity. "
                + "Fibonacci values in rational or integer arithmetic are coerced into that field or ring.")),
            Node("denominator", "The moving diagonal denominator", DenominatorFormula(),
                "On the triangle, the diagonal denominator is F(n)F(n+1); each earlier "
                + "entry has denominator F(k)F(k+2). The Lean definition extends this "
                + "piecewise expression to all natural n and k.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("altRowSum", "The alternating row sum", RowSumFormula(),
                "The finite sum runs from k=1 through k=n, with a positive first term "
                + "and numerator one before applying the alternating sign.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("altRowSum_succ_sub", "The row difference", DifferenceFormula(),
                "Split each row into its unchanged prefix and diagonal. In the next row "
                + "the old diagonal acquires denominator F(n)F(n+2), and a new diagonal "
                + "appears. The Fibonacci recurrence simplifies their combined change.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("fib_cassini_two", "The two-step product identity", CassiniFormula(),
                "Specialize the repository's fib_vajda at i=1 and j=3. This is a thin "
                + "wrapper used to compute the difference of the proposed closed forms.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("schulte_conjecture", "Schulte's conjecture from row two onward", ConjectureFormula(),
                "The second row sums to zero. The row-difference identity and the "
                + "two-step product identity give identical increments for the finite "
                + "sum and the Fibonacci quotient, so induction proves every n at least two.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a378277-harmonic-triangle-alternating-row-sums"),
                    ResolutionKind.Proved)),
            Node("schulte_conjecture_one", "The first row", Disp(Equal(Row(D(1)), D(1))),
                "The first row is 1. This is the separate first-row clause of the OEIS "
                + "conjecture, whose convention is F(-1)=1; no negative natural index "
                + "is introduced in Lean.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a378277-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula DenominatorFormula() => Disp(Seq(Bound("n", "k"), Sp,
        Equal(Denominator(N(), K()), Seq(
            Named("if"), Sp, Parenthesized(Equal(K(), N())), Sp, Named("then"), Sp,
            Parenthesized(Mul(Fib(N()), Fib(Add(N(), D(1))))), Sp, Named("else"), Sp,
            Parenthesized(Mul(Fib(K()), Fib(Add(K(), D(2)))))))));

    private static Formula RowSumFormula() => Disp(Seq(Bound("n"), Sp,
        Equal(Row(N()), Seq(
            new Formula.Subscript(F.Sum, Seq(K(), Sp, InMacro, Sp, Call("Icc", D(1), N()))),
            Sp, Parenthesized(Fraction(Sign(Subtract(K(), D(1))), Denominator(N(), K())))))));

    private static Formula DifferenceFormula() => Disp(Seq(Bound("n"), Sp,
        D(2), Sp, Le, Sp, N(), Sp, Implies, Sp,
        Equal(Subtract(Row(Add(N(), D(1))), Row(N())),
            Fraction(Mul(D(2), Sign(N())), Mul(Fib(Add(N(), D(1))), Fib(Add(N(), D(2))))))));

    private static Formula CassiniFormula() => Disp(Seq(Bound("n"), Sp,
        Equal(Subtract(Mul(Fib(Add(N(), D(1))), Fib(Add(N(), D(3)))),
                Mul(Fib(N()), Fib(Add(N(), D(4))))),
            Mul(D(2), Sign(Add(N(), D(2)))))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n"), Sp,
        D(2), Sp, Le, Sp, N(), Sp, Implies, Sp,
        Equal(Row(N()), Fraction(Fib(Subtract(N(), D(2))), Fib(Add(N(), D(1)))))));

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula Fib(Formula n) => Call("F", n);
    private static Formula Row(Formula n) => Call("altRowSum", n);
    private static Formula Denominator(Formula n, Formula k) => Call("denominator", n, k);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Sign(Formula exponent) =>
        new Formula.Power(Parenthesized(Seq(Minus, D(1))), exponent);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Subtract(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Fraction(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
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
