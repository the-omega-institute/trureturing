using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.SquareRows;

internal sealed class SquareExponentDyadicSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/SquareRows/SquareExponentDyadicSupport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/hanna2026a397902");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zero-constant integer series of OEIS A397902 exists uniquely and has the conjectured odd support at every index above two.",
        H("Square Exponents and the Parity of OEIS A397902"),
        Blocks(
            Paragraph(Text("The source defines A in the ring of integer formal power series, "
                + "with constant coefficient zero, by [X^(m-1)](1-A)^(m squared)/(1-m squared X)=0 "
                + "for every natural m>1. Here invOfUnit means the unique multiplicative inverse "
                + "of the denominator with constant coefficient one; it does not require passage "
                + "to rational coefficients. The sequence term a(n) is [X^n]A.")),
            Node("generatingSeries", "Construction over the integers",
                "Put F=1-A. For n>0 set e=(n+1) squared and g=(1-eX) inverse. Let R be "
                + "[X^n](F^e g), and T be [X^(n-1)](F^(e-1) F' g + F^e g squared). "
                + "Differentiation gives nR=eT. Since e-n(n+2)=1, the residual N=R-(n+2)T "
                + "satisfies R=eN. Changing only the nth coefficient of F changes N by exactly "
                + "that coefficient difference. Iterating the correction F_n -> F_n-N stabilizes "
                + "each coefficient and defines F over the integers, with constant coefficient one. "
                + "The displayed generatingSeries is A=1-F.", DescribeRole.Definition),
            Node("DefiningEquation", "The exact source equation",
                "The predicate includes the zero constant term, integer coefficients, the square "
                + "exponent, and every m>1. Multiplication by invOfUnit expresses precisely the "
                + "division in the OEIS NAME.", DescribeRole.Definition),
            Node("generating_equation", "The constructed series satisfies every row",
                "Coefficient stabilization makes every positive normalized residual zero. "
                + "The identity R=eN then makes every original row zero. The geometric series "
                + "used in the construction equals the denominator's unit inverse."),
            Node("integer_exists_unique", "Integer existence and uniqueness",
                "The preceding construction supplies an integer witness. For uniqueness, equality "
                + "of lower coefficients and the unit multiplier of the normalized residual force "
                + "the next coefficients to agree. Induction proves equality in all degrees. "
                + "No integrality assumption about a rational recurrence is used."),
            Node("a", "Coefficient indexing",
                "This is the source's coefficient indexing, extended by a(0)=0.", DescribeRole.Definition),
            Node("hanna_conjecture", "The complete odd-support classification",
                "Reduce the exact normalized residual to ZMod 2. For the Catalan unit U, "
                + "U=1+X U squared. Set H=U squared, O=(1+X)H, E=1+X+XO, and B=E squared+X O squared. "
                + "Then E+XO=1+X and EO=B. These identities make the odd and even normalized "
                + "rows of B vanish; repeated halving proves the needed diagonal power coefficients "
                + "vanish. Normalized uniqueness identifies B with the reduction of F. "
                + "For n>2, its nth coefficient equals the coefficient of U at floor((n-1)/4). "
                + "The existing binary_catalan theorem identifies this coefficient as one exactly "
                + "when floor((n-1)/4)+1 is a power of two. This gives precisely the four "
                + "indices 2^k, 2^k-1, 2^k-2, 2^k-3 with k>1. Integer uniqueness transfers "
                + "the conclusion to every series satisfying the original defining equation."))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("a397902-" + name.Replace('_', '-').ToLowerInvariant()),
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
        var exponent = Pow(m, D(2));
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
            Par(Seq(Equal(n, power), Sp, Lor, Sp, Equal(n, Sub(power, D(1))),
                Sp, Lor, Sp, Equal(n, Sub(power, D(2))), Sp, Lor, Sp, Equal(n, Sub(power, D(3))))));
        return Seq(Bound("A", SeriesType()), Def(F.Id("A")), Sp, Implies, Sp,
            Bound("n", NatType()), D(2), Sp, Lt, Sp, n, Sp, Implies, Sp,
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
