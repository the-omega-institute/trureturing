using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.LinearRows;

internal sealed class LinearExponentDyadicSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/hanna2026a397591");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer series of OEIS A397591 exists uniquely and has odd coefficients precisely at dyadic neighbors above degree three.",
        H("Linear Exponents and the Parity of OEIS A397591"),
        Blocks(
            Paragraph(Text("The source defines A over integer formal power series with constant "
                + "coefficient zero. For every m>1, [X^(m-1)](1-A)^m/(1-mX)=0. "
                + "The inverse of the constant-one denominator is expressed by invOfUnit, "
                + "and a(n) means the coefficient [X^n]A.")),
            Node("generatingSeries", "Construction over the integers",
                "Write F=1-A. At degree n>0, put e=n+1 and g=(1-eX) inverse. "
                + "Let R=[X^n](F^e g) and T=[X^(n-1)](F^(e-1) F' g+F^e g squared). "
                + "Differentiation gives nR=eT, so N=R-T satisfies R=eN. Changing the "
                + "nth coefficient of F changes N by exactly the same amount. Successive "
                + "coefficient corrections stabilize, giving an integer series F with N=0 "
                + "at every positive degree. The generating series is A=1-F.", DescribeRole.Definition),
            Node("DefiningEquation", "The exact source equation",
                "The predicate specifies integer coefficients, the zero constant term, the "
                + "linear exponent m, and all natural m>1. The power-series unit inverse "
                + "implements the division in the source NAME.", DescribeRole.Definition),
            Node("generating_equation", "Every defining row vanishes",
                "Stabilization gives N=0 at each positive index. The identity R=eN and "
                + "the equality of the geometric series with the denominator inverse "
                + "give the original defining equation."),
            Node("integer_exists_unique", "Integer existence and uniqueness",
                "The stabilized construction supplies an integer solution. If two solutions "
                + "agree below degree n, their normalized residual difference equals their "
                + "nth coefficient difference. Induction forces equality in every degree."),
            Node("a", "Coefficient indexing",
                "The source coefficient indexing is extended by a(0)=0.", DescribeRole.Definition),
            Node("hanna_conjecture", "Odd coefficients at dyadic neighbors",
                "Over ZMod 2, let U be the Catalan unit, so U=1+X U squared. "
                + "Put E=1+X, O=EU, B=E squared+X O squared, and V=1+XU. Then "
                + "B=E squared U=EO and UV=1. For each m>0, [X^m](B^m V)=0: "
                + "an odd m selects an odd coefficient of a square, while an even m "
                + "reduces to m/2 by the Catalan equation. This eliminates the even "
                + "normalized rows of B; EO=B eliminates the odd rows. Uniqueness "
                + "identifies B with the reduction of 1-A. For n>3 its coefficient is "
                + "[X^n]U+[X^(n-2)]U. The frozen binary_catalan theorem says these "
                + "summands are one when n+1 or n-1 is a power of two. They cannot "
                + "both be one here, since two powers of two greater than two cannot "
                + "differ by two. This proves the stated equivalence for every solution."))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("a397591-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Statement(name)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula SeriesType() => Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Z"))));
    private static Formula Bound(string name, Formula type) => Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Def(Formula a) => Call("DefiningEquation", a);
    private static Formula Coeff(Formula n, Formula a) => Call("coeff", n, a);

    private static Formula Definition()
    {
        var a = F.Id("A");
        var m = F.Id("m");
        var exponent = m;
        var denominator = Sub(D(1), Mul(exponent, F.Id("X")));
        var inverse = Call("invOfUnit", denominator, D(1));
        var row = Equal(Coeff(Sub(m, D(1)), Mul(Pow(Par(Sub(D(1), a)), exponent), inverse)), D(0));
        var rows = Seq(Bound("m", NatType()), D(1), Sp, Lt, Sp, m, Sp, Implies, Sp, row);
        return Seq(Bound("A", SeriesType()), Def(a), Sp, Iff, Sp,
            Par(Seq(Equal(Call("constantCoeff", a), D(0)), Sp, Land, Sp, Par(rows))));
    }

    private static Formula Conjecture()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var power = Pow(D(2), k);
        var support = Seq(Exists, Sp, k, Colon, Sp, NatType(), Comma, Sp,
            D(1), Sp, Lt, Sp, k, Sp, Land, Sp,
            Par(Seq(Equal(n, Sub(power, D(1))), Sp, Lor, Sp,
                Equal(n, new Formula.Binary(power, FormulaBinaryOperator.Add, D(1))))));
        return Seq(Bound("A", SeriesType()), Def(F.Id("A")), Sp, Implies, Sp,
            Bound("n", NatType()), D(3), Sp, Lt, Sp, n, Sp, Implies, Sp,
            Par(Seq(Call("Odd", Coeff(n, F.Id("A"))), Sp, Iff, Sp, Par(support))));
    }

    private static Formula Statement(string name) => Disp(name switch
    {
        "generatingSeries" => Equal(Call("generatingSeries"), Sub(D(1), Call("solution"))),
        "DefiningEquation" => Definition(),
        "generating_equation" => Def(Call("generatingSeries")),
        "integer_exists_unique" => Seq(Exists, Bang, Sp, F.Id("A"), Colon, Sp, SeriesType(), Comma, Sp, Def(F.Id("A"))),
        "a" => Seq(Bound("n", NatType()), Equal(Call("a", F.Id("n")), Coeff(F.Id("n"), Call("generatingSeries")))),
        "hanna_conjecture" => Conjecture(),
        _ => throw new System.ArgumentOutOfRangeException(nameof(name))
    });
}
