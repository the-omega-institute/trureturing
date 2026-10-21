using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaA393173PowerTwoParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2026a393173");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized inverse-diagonal equation has integral coefficients, odd exactly at powers of two in positive degrees.",
        H("Hanna's A393173 Power-of-Two Parity"),
        Blocks(
            Paragraph(Text("PowerSeries denotes formal power series. The operator coeff(n,A) extracts "
                + "coefficient n, constantCoeff extracts the constant coefficient, C embeds a scalar "
                + "as a constant series, and X is the indeterminate. The inverse is the formal "
                + "power-series inverse. The displayed rational type annotations give the natural "
                + "and integer coercions into the rational coefficient ring.")),
            Node("IsGF", "The normalized inverse-diagonal equation", IsGFFormula(),
                "The Name of the unpaginated OEIS A393173 entry reads: "
                + "\"G.f. A(x) satisfies [x^n] 1/(A(x) - n^2*x) = 0 for n >= 1.\" "
                + "The offset-zero sequence begins with a(0)=1. Thus A has constant coefficient "
                + "one, and A-C(n squared)*X has a multiplicative inverse at every natural n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The parity proposition", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "The Comments of the unpaginated OEIS A393173 entry state: "
                + "\"Conjecture: for n > 0, a(n) is odd iff n is a power of 2.\" "
                + "Here a(n) is coeff(n,A); n and the exponent k are natural numbers. "
                + "The integer m equals the rational coefficient, so the proposition asserts "
                + "integrality as well as parity for every normalized rational solution. "
                + "It also asserts that such a solution exists.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The A393173 parity theorem", Disp(ClaimBody()),
                "The degree-n coefficient of the inverse changes by the negative of the "
                + "degree-n coefficient change when all earlier coefficients agree. Adding that "
                + "inverse coefficient defines a strict coefficient contraction. "
                + "PowerSeriesNormalizedContraction supplies its normalized fixed point over the "
                + "integers and uniqueness over each commutative ring. Ring maps preserve this "
                + "fixed-point equation. Over ZMod(2), the existing powerTwoSeries satisfies "
                + "powerTwoSeries plus its square equals X. Hence one plus powerTwoSeries "
                + "satisfies every reduced equation: at positive even n its inverse coefficient "
                + "is the vanishing degree-(n+1) coefficient of powerTwoSeries; at odd n the "
                + "denominator is a square and Frobenius makes its inverse coefficient vanish. "
                + "Uniqueness identifies the reduction of the integral solution with this series. "
                + "Rational uniqueness and the integer-cast parity equivalence prove the assertion.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hanna-a393173-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Exist(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula ImpliesTo(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula IsGFFormula()
    {
        Formula a = F.Id("A"), n = F.Id("n");
        Formula denominator = new Formula.Binary(a, FormulaBinaryOperator.Subtract,
            new Formula.Binary(Call("C", Pow(Parenthesized(Seq(n, Colon, Sp, Rationals())), D(2))),
                FormulaBinaryOperator.Multiply, F.Id("X")));
        Formula equation = Seq(Bound("n", Naturals()),
            ImpliesTo(Seq(D(1), Sp, Le, Sp, n), Equal(Call("coeff", n,
                Pow(denominator, Seq(Minus, D(1)))), D(0))));
        return Disp(Seq(Bound("A", Series()), Equal(Call("IsGF", a), Parenthesized(And(
            Equal(Call("constantCoeff", a), D(1)), equation)))));
    }
    private static Formula ClaimBody()
    {
        Formula a = F.Id("A"), n = F.Id("n"), m = F.Id("m"), k = F.Id("k");
        Formula dyadic = Exist("k", Naturals(), Equal(n, Pow(D(2), k)));
        Formula parity = Seq(Parenthesized(Call("Odd", m)), Sp, Iff, Sp, Parenthesized(dyadic));
        Formula integerCoefficient = Exist("m", Integers(), And(
            Equal(Call("coeff", n, a), Parenthesized(Seq(m, Colon, Sp, Rationals()))), parity));
        Formula all = Seq(Bound("A", Series()), ImpliesTo(Call("IsGF", a),
            Seq(Bound("n", Naturals()), ImpliesTo(Seq(D(0), Sp, Lt, Sp, n), integerCoefficient))));
        return And(Exist("A", Series(), Call("IsGF", a)), all);
    }
}
