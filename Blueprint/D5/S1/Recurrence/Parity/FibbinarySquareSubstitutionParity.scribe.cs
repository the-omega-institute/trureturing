using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class FibbinarySquareSubstitutionParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2024a374571");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd coefficients of OEIS A374571 occur exactly at Fibbinary indices.",
        H("Hanna's Fibbinary Parity Conjecture"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2024a374571 specifies "
                + "A(x)=A(x^2)-x A(x^2)^2 and conjectures that, for n>0, a(n) is odd "
                + "exactly when n is a Fibbinary number, as listed by A003714. "
                + "The normalization is A(0)=1. The functional equation alone leaves "
                + "the constant coefficient free, so uniqueness retains that hypothesis.")),
            Paragraph(Text("Indices and exponents are natural numbers. The functions div "
                + "and mod denote natural integer division and remainder; subtraction "
                + "inside an index is natural subtraction. Fin(r) consists of j with "
                + "0<=j<r, read as natural numbers in the summand. Values of a are integers. "
                + "PowerSeries(Z) is the formal power-series ring with indeterminate X; "
                + "subst(B,Q) means composition of B with Q, and mk(a) has coefficients a. "
                + "The operations land and shiftRight are natural-number bitwise "
                + "intersection and right shift, respectively.")),
            Node("a", "The integer coefficient sequence", SequenceFormula(),
                "The seed and the displayed recurrence define a by well-founded recursion. "
                + "Every recursive index in the successor clause is strictly smaller "
                + "than n+1.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The coefficient of degree n is a(n).", DescribeRole.Definition),
            Node("Fibbinary", "No adjacent one bits", FibbinaryFormula(),
                "Bit i of land(n,shiftRight(n,1)) is the conjunction of bits i and i+1 "
                + "of n. Thus the intersection vanishes exactly when the binary "
                + "representation contains no adjacent ones, including the case n=0.",
                DescribeRole.Definition),
            Node("generating_equation", "The normalized functional equation", EquationFormula(),
                "Substitution by X^2 retains coefficient n/2 at even degrees and is zero "
                + "at odd degrees. The shifted square contributes the negative convolution "
                + "at odd degrees. Coefficient comparison gives the defining recurrence "
                + "and proves the identity together with the constant coefficient."),
            Node("generating_unique", "Uniqueness with constant coefficient one", UniqueFormula(),
                "For every positive degree, the equation expresses the coefficient using "
                + "only smaller indices. Strong induction, with the prescribed constant "
                + "coefficient as base case, identifies B with generatingSeries."),
            Node("hanna_conjecture", "The A374571 parity conjecture", ConjectureFormula(),
                "Reduce the proved generating equation to ZMod(2). Frobenius identifies "
                + "the square of a series with its substitution by X^2. Consequently the "
                + "coefficient residues satisfy a(2m)=a(m), a(4m+1)=a(m), and a(4m+3)=0. "
                + "The Fibbinary predicate satisfies the same three descent rules: an "
                + "ending zero may be removed, an ending 01 may be removed, and an ending "
                + "11 is forbidden. Strong induction from a(0)=1 proves the equivalence; "
                + "the displayed theorem restricts it to the positive indices in the entry.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a374571-fibbinary-square-substitution-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a374571-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula J() => F.Id("j");
    private static Formula X() => F.Id("X");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula Generating() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) => Seq(
        Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp, yes, Sp,
        Named("else"), Sp, no);
    private static Formula A(Formula index) => Call("a", index);
    private static Formula Substituted(Formula series) => Call("subst", series, Power(X(), D(2)));
    private static Formula Equation(Formula series) => Equal(series,
        Subtract(Substituted(series), Mul(X(), Power(Parenthesized(Substituted(series)), D(2)))));

    private static Formula SequenceFormula()
    {
        Formula half = Call("div", N(), D(2));
        Formula sum = Seq(new Formula.Subscript(F.Sum,
            Seq(J(), Colon, Sp, Call("Fin", Add(half, D(1))))), Sp,
            Parenthesized(Mul(A(J()), A(Subtract(half, J())))));
        return Disp(new Formula.Aligned([
            Seq(Named("a"), Colon, Sp, Naturals(), Sp, To, Sp, Integers()),
            Equal(A(D(0)), D(1)),
            Seq(Bound("n", Naturals()), Equal(A(Add(N(), D(1))),
                IfThenElse(Equal(Call("mod", Add(N(), D(1)), D(2)), D(0)),
                    A(Call("div", Add(N(), D(1)), D(2))), Seq(Minus, Parenthesized(sum)))))
        ]));
    }

    private static Formula GeneratingFormula() => Disp(Seq(
        Generating(), Colon, Sp, Series(), Comma, Sp,
        Equal(Generating(), Call("mk", Named("a")))));

    private static Formula FibbinaryFormula() => Disp(Seq(Bound("n", Naturals()),
        Call("Fibbinary", N()), Sp, Iff, Sp,
        Parenthesized(Equal(Call("land", N(), Call("shiftRight", N(), D(1))), D(0)))));

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", Generating()), D(1)), Equation(Generating())));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(1)),
                Implication(Equation(b), Equal(b, Generating())))));
    }

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(0), Sp, Lt, Sp, N()),
            Parenthesized(Seq(Call("Odd", A(N())), Sp, Iff, Sp, Call("Fibbinary", N()))))));
}
