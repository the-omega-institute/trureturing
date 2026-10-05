using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SignedDirichletPositiveResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/SignedDirichletPositiveResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separate positive and negative divisor budgets control a signed response.",
        H("Positive Response for Signed Divisor Convolution"),
        Blocks(Describe.Lean(
            DescribeId.Create("signed-divisor-positive-response"),
            DeclarationHandle.Create(Prefix + "signedDivisor_positive_response"),
            H("Two bounds from monotone nonnegative forcing"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let b, f and g be real sequences on the natural numbers. "
                    + "Assume g(n)>=0 for every n>0 and g(m)<=g(n) whenever 0<m<=n. "
                    + "Write D(n) for the finite set of positive divisors of n, with "
                    + "D(0) defined to be empty. For every natural n, assume the sums of max(-b(d),0) and "
                    + "max(b(d),0) over divisors d of n other than 1 are at most E and P, "
                    + "respectively. Assume E+P<b(1). At every positive n the exact "
                    + "divisor convolution sum b(d) f(n/d) equals g(n). Then f(n) lies "
                    + "between (b(1)-E-P)g(n)/(b(1)(b(1)-E)) and g(n)/(b(1)-E). "
                    + "Division inside f is natural division and is exact at each divisor.")),
                Paragraph(Text("The empty tails at n=1 imply E>=0 and P>=0, so both "
                    + "denominators and the lower coefficient are positive. Strong induction "
                    + "proves both bounds together. For every divisor d>1, the earlier "
                    + "response satisfies 0<=f(n/d)<=g(n)/(b(1)-E). Consequently the signed "
                    + "tail is at least -E g(n)/(b(1)-E) and at most P g(n)/(b(1)-E). "
                    + "Splitting the head from the convolution and cancelling b(1)>0 "
                    + "gives the upper and lower bounds. Earlier positivity is derived "
                    + "from the inductive lower bound, rather than assumed.")),
                Paragraph(Text("This result allows both positive and negative tail "
                    + "coefficients, zero forcing and arbitrary values of b, f and g at "
                    + "zero. It assumes no global bound or positivity of f. It is a "
                    + "general divisor convolution estimate. Applying it to the actual "
                    + "Fibonacci logarithmic coefficients still requires their budgets "
                    + "and exact convolution identity; those analytic premises are not "
                    + "formalized here. It supplies neither an RH growth estimate nor "
                    + "control of the signed Robin tail."))),
            DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var b = F.Id("b"); var f = F.Id("f"); var g = F.Id("g");
        var e = F.Id("E"); var p = F.Id("P"); var n = F.Id("n");
        var m = F.Id("m"); var d = F.Id("d");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula b1 = Call("b", D(1));
        Formula denominator = Seq(b1, Minus, e);
        Formula tail(Formula coefficient) => Seq(
            new Formula.Subscript(Sum, Seq(d, InMacro, Sp, Call("D", n), Comma, Sp, d, Neq, Sp, D(1))),
            coefficient);
        Formula budget(Formula coefficient, Formula bound) => Seq(
            Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            tail(coefficient), Le, Sp, bound);
        Formula forcing = Seq(Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            D(0), Lt, Sp, n, Rightarrow, Sp, D(0), Le, Sp, Call("g", n));
        Formula monotone = Seq(Forall, Sp, m, Comma, n, InMacro, Sp, naturals,
            Comma, Sp, D(0), Lt, Sp, m, Le, Sp, n, Rightarrow, Sp,
            Call("g", m), Le, Sp, Call("g", n));
        Formula convolution = Seq(Forall, Sp, n, InMacro, Sp, naturals, Comma,
            Sp, D(0), Lt, Sp, n, Rightarrow, Sp,
            new Formula.Subscript(Sum, Seq(d, InMacro, Sp, Call("D", n))),
            Call("b", d), Cdot, Call("f", new Formula.Fraction(n, d)),
            Eq, Sp, Call("g", n));
        Formula conclusion = Seq(Forall, Sp, n, InMacro, Sp, naturals, Comma,
            Sp, D(0), Lt, Sp, n, Rightarrow, Sp,
            new Formula.Fraction(Seq(b1, Minus, e, Minus, p),
                Seq(b1, Cdot, Open, denominator, Close)), Cdot, Call("g", n),
            Le, Sp, Call("f", n), Le, Sp,
            new Formula.Fraction(Call("g", n), denominator));
        return Disp(Seq(Forall, Sp, b, Comma, f, Comma, g, Colon, Sp,
            naturals, To, Sp, reals, Comma, Sp, Forall, Sp, e, Comma, p,
            InMacro, Sp, reals, Comma, Sp, Open, Open, forcing, Close,
            Land, Sp, Open, monotone, Close,
            Land, Sp, Open, budget(Call("max", Seq(Minus, Call("b", d)), D(0)), e), Close,
            Land, Sp, Open, budget(Call("max", Call("b", d), D(0)), p), Close,
            Land, Sp, e, Plus, p, Lt, Sp, b1, Land, Sp, Open, convolution, Close, Close,
            Rightarrow, Sp, conclusion));
    }
}
