using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaRealExponentPositivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaRealExponentPositivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/hanna2017a281186");
    private const string SourceSentence =
        "Conjecture: if G(x) = exp( 1/G(x) * Integral G(x)^t dx ) for some fixed real t, then G(x) will consist entirely of nonnegative coefficients iff t >= 8/3.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source equation forces a negative degree-720 coefficient at t=8/3.",
        H("Hanna's real-exponent positivity threshold is false"),
        Blocks(
            Paragraph(Text("All series have real coefficients. PowerSeries.exp is the formal exponential series, PowerSeries.logOf is the formal logarithm of a series with constant coefficient one, and PowerSeries.subst is formal substitution. A real power G^t means substituting t • PowerSeries.logOf G into PowerSeries.exp ℝ. The primitive J has constant coefficient zero. PowerSeries.coeff j G is the ordinary degree-j coefficient, with j starting at zero. Multiplication by the positive EGF factor j! · 3^j preserves its sign.")),
            Node("IsSourceSeries", "The source integral equation",
                Disp(All("t", Reals(), All("G", Series(),
                    Equal(Call("IsSourceSeries", V("t"), V("G")),
                        Parenthesized(SourceBody()))))),
                "OEIS A281186, COMMENTS, revision 10 (unpaginated): \"" + SourceSentence
                    + "\" The real parameter is t. The equations for J express the zero-constant formal primitive, and the constant coefficient of G is one. The source's PARI intformal program fixes the integration constant at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The quantified positivity assertion",
                Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "OEIS A281186, COMMENTS, revision 10 (unpaginated): \"" + SourceSentence
                    + "\" The statement includes existence for each real t and the asserted equivalence for every source series G. Nonnegativity includes degree zero. The source EGF is \"E.g.f.: A(x) = Sum_{n>=0} a(n) * x^n / (n! * 3^n).\"",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation at the boundary parameter",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "At t=8/3, write y=PowerSeries.logOf G. Differentiation of the integral equation gives (1+y)y′=exp((5/3)y). An integer polynomial sequence begins with Q₀=1 and satisfies Qₙ=((5n+3)X+6−n)Qₙ₋₁+3(1+X)Q′ₙ₋₁ for n≥1. Induction on the derivative order gives (n+1)! · coeff(n+1,G)=(1/3)^n · coeff(0,Qₙ). Exact integer reduction proves coeff(0,Q₇₁₉)<0. The asserted existence supplies G, and the asserted nonnegativity at 8/3 contradicts its degree-720 coefficient. This argument does not separately establish existence, uniqueness, the least negative degree, or a corrected threshold.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("hanna-real-exponent-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Series() => Call("PowerSeries", Reals());
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));

    private static Formula SourceBody()
    {
        var g = V("G");
        var j = V("J");
        var exp = App(Qualified("PowerSeries", "exp"), Reals());
        var power = App(Qualified("PowerSeries", "subst"),
            Parenthesized(App(Qualified("HSMul", "hSMul"), V("t"),
                App(Qualified("PowerSeries", "logOf"), g))), exp);
        var inverseProduct = new Formula.Binary(new Formula.Power(g, Seq(Minus, D(1))),
            FormulaBinaryOperator.Multiply, j);
        return And(Equal(App(Qualified("PowerSeries", "constantCoeff"), g), D(1)),
            Some("J", Series(), And(Equal(App(Qualified("PowerSeries", "constantCoeff"), j), D(0)),
                And(Equal(App(Qualified("PowerSeries", "derivative"), j), power),
                    Equal(g, App(Qualified("PowerSeries", "subst"), Parenthesized(inverseProduct), exp))))));
    }

    private static Formula ClaimBody()
    {
        var source = Call("IsSourceSeries", V("t"), V("G"));
        var positive = All("j", Naturals(), Seq(D(0), Sp, Le, Sp,
            App(Qualified("PowerSeries", "coeff"), V("j"), V("G"))));
        var threshold = Seq(new Formula.Fraction(Parenthesized(Seq(D(8), Colon, Sp, Reals())), D(3)),
            Sp, Le, Sp, V("t"));
        return All("t", Reals(), And(Some("G", Series(), source),
            All("G", Series(), Seq(Parenthesized(source), Sp, Implies, Sp,
                Parenthesized(Seq(Parenthesized(positive), Sp, Iff, Sp, Parenthesized(threshold)))))));
    }
}
