using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Bilateral;

internal sealed class BilateralProductModFourUnitExponentDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a380066");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A380066 bilateral product congruence.",
        H("The unit-exponent bilateral product"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A380066 gives the bilateral product equation "
                + "and conjectures that every positive coefficient is two modulo four. "
                + "The formalization uses integer power series and coefficientwise symmetric "
                + "windows for the bilateral sum.")),
            Node("IsGF", "The normalized bilateral generating equation", IsGFFormula(),
                "The OEIS A380066 name states: \"G.f. A(x) satisfies 1/2 = "
                + "Sum_{n=-oo..+oo} x^n*A(x)^n * (A(x)^n + x)^(n-1) * "
                + "(A(x) + x^n)^(n-1).\" A normalized integer power series satisfies "
                + "this literal summand equation at every coefficient and every symmetric "
                + "window whose radius is at least the coefficient index.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's A380066 coefficient conjecture", ClaimFormula(),
                "The OEIS A380066 comment states: \"Conjecture: for n > 0, "
                + "a(n) == 2 (mod 4).\" There is a normalized integer solution, and "
                + "every normalized integer solution has positive coefficients congruent "
                + "to two modulo four.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The proved A380066 congruence", ResultFormula(),
                "The contraction of the coefficientwise bilateral remainder gives a normalized "
                + "integral fixed series and identifies every normalized integral solution with it. "
                + "The fixed point identity makes the difference from twice the geometric series "
                + "minus one divisible by four, yielding the stated congruence. The same argument "
                + "works for every exponent parameter at least one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("bilateral-unit-exponent-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(DeclarationPath(name)), H(title),
        StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static string DeclarationPath(string name) => Prefix + name;

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula IntCast(Formula value) =>
        new Formula.Apply(Seq(Named("Int"), Dot, Named("ofNat")), [value]);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) =>
        Seq(left, Sp, Lt, Sp, right);
    private static Formula AtMost(Formula left, Formula right) =>
        Seq(left, Sp, Le, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name),
            Parenthesized(type), body);
    private static Formula Coeff(Formula index, Formula series) =>
        Call("coeff", index, series);
    private static Formula ConstantCoeff(Formula series) =>
        Call("constantCoeff", series);
    private static Formula Window(Formula index) =>
        Call("Icc", Seq(Minus, Parenthesized(IntCast(index))), IntCast(index));
    private static Formula LaurentTerm(Formula series, Formula index) =>
        Call("laurentTerm", D(1), series, index);
    private static Formula Half() => new Formula.Fraction(D(1), D(2));
    private static Formula IsGFBody(Formula series)
    {
        Formula n = F.Id("N");
        Formula k = F.Id("K");
        Formula j = F.Id("j");
        Formula summand = Coeff(IntCast(n), LaurentTerm(series, j));
        Formula windowSum = new Formula.Subscript(
            F.Sum, Seq(j, Sp, InMacro, Sp, Window(k)));
        Formula sum = Seq(windowSum, Sp, Parenthesized(summand));
        Formula rhs = Parenthesized(Seq(Named("if"), Sp,
            Parenthesized(Equal(n, D(0))), Sp, Named("then"), Sp, Half(), Sp,
            Named("else"), Sp, D(0)));
        Formula windowEquation = Equal(sum, rhs);
        return And(Equal(ConstantCoeff(series), D(1)),
            All("N", Naturals(), All("K", Naturals(),
                Implication(AtMost(n, k), windowEquation))));
    }
    private static Formula IsGFFormula() => Disp(All("A", Series(),
        new Formula.Logic(Call("IsGF", F.Id("A")), FormulaLogicOperator.Iff,
            Parenthesized(IsGFBody(F.Id("A"))))));
    private static Formula ClaimBody()
    {
        Formula a = F.Id("A");
        Formula n = F.Id("n");
        Formula congruence = Equal(new Formula.Modulo(Coeff(n, a), D(4)), D(2));
        return And(
            Exists("A", Series(), IsGFBody(a)),
            All("A", Series(), Implication(IsGFBody(a),
                All("n", Naturals(), Implication(Less(D(0), n), congruence)))));
    }
    private static Formula ClaimFormula()
    {
        Formula a = F.Id("A");
        Formula n = F.Id("n");
        Formula congruence = Equal(new Formula.Modulo(Coeff(n, a), D(4)), D(2));
        return Disp(And(
            Exists("A", Series(), Call("IsGF", a)),
            All("A", Series(), Implication(Call("IsGF", a),
                All("n", Naturals(), Implication(Less(D(0), n), congruence))))));
    }
    private static Formula ResultFormula() => Disp(ClaimBody());
}
