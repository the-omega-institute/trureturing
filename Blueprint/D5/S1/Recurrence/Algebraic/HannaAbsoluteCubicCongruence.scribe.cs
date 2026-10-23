using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaAbsoluteCubicCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a380711");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient contraction and reduction modulo two prove Hanna's cubic congruence.",
        H("Hanna's absolute cubic congruence for A380711"),
        Blocks(
            Paragraph(Text("All series have rational coefficients. The operation absSeries takes "
                + "the absolute value of each coefficient. The inverse is the formal multiplicative "
                + "inverse. Ring.choose is the generalized binomial coefficient over the integers; "
                + "the fraction in quotient is rational division. At n = 0 it is -1.")),
            Node("absSeries", "Coefficientwise absolute value", AbsFormula(),
                "OEIS A380711, NAME (unpaginated): \"G.f. A(x) satisfies A(x) = "
                + "1 + x*A(x)*abs( 1/A(x)^3 ).\" The operation abs replaces each rational "
                + "coefficient by its absolute value.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsGF", "The generating function", GfFormula(),
                "OEIS A380711, NAME (unpaginated): \"G.f. A(x) satisfies A(x) = "
                + "1 + x*A(x)*abs( 1/A(x)^3 ).\" The offset is zero. "
                + "A is a rational formal power series and X is the series variable.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("quotient", "The generalized binomial quotient", QuotientFormula(),
                "OEIS A380711, COMMENTS (unpaginated), state \"Conjecture: a(n) == "
                + "binomial(3*n-1,n)/(3*n-1) (mod 2) for n >= 0.\" The top argument of "
                + "Ring.choose is an integer. The quotient is formed in the rationals, so its "
                + "value at n = 0 is binomial(-1,0)/(-1) = -1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The congruence conjecture", Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "OEIS A380711, COMMENTS (unpaginated): \"Conjecture: a(n) == "
                + "binomial(3*n-1,n)/(3*n-1) (mod 2) for n >= 0.\" The proposition "
                + "asserts existence and, for every solution and every natural index, integer "
                + "representatives of both rational quantities and their congruence modulo two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The cubic congruence", Disp(ClaimBody()),
                "Strict contraction of coefficients gives an integral solution and uniqueness "
                + "over the rationals. Absolute value disappears modulo two. The reduced series "
                + "satisfies F^3 = F^2 + X, so it agrees with the absolute reciprocal square-shift "
                + "series. Its known binomial coefficient congruence gives the result for positive "
                + "indices; at zero the two integer representatives are 1 and -1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a380711-hanna-absolute-cubic-congruence"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));

    private static Formula AbsFormula() => Disp(All("F", Series(), Equal(Call("absSeries", V("F")),
        new Formula.Apply(Qualified("PowerSeries", "mk"), [Parenthesized(Seq(
            V("n"), Colon, Sp, Naturals(), Sp, Mapsto, Sp,
            Lvert, Sp, Call("coeff", V("n"), V("F")), Sp, Rvert))]))));

    private static Formula GfFormula() => Disp(All("A", Series(), Equal(Call("IsGF", V("A")),
        Parenthesized(Equal(V("A"), Add(D(1), Mul(Mul(V("X"), V("A")),
            Call("absSeries", Power(Power(V("A"), D(3)), Seq(Minus, D(1)))))))))));

    private static Formula QuotientFormula() => Disp(All("n", Naturals(),
        Equal(Call("quotient", V("n")), new Formula.Fraction(
            Cast(new Formula.Apply(Qualified("Ring", "choose"), [
                Subtract(Mul(D(3), Cast(V("n"), Integers())), D(1)), V("n")]), Rationals()),
            Subtract(Mul(D(3), Cast(V("n"), Rationals())), D(1))))));

    private static Formula ClaimBody() => And(
        Some("A", Series(), Call("IsGF", V("A"))),
        All("A", Series(), Imp(Call("IsGF", V("A")), All("n", Naturals(),
            Some("m", Integers(), Some("z", Integers(), And(
                Equal(Call("coeff", V("n"), V("A")), Cast(V("m"), Rationals())), And(
                    Equal(Call("quotient", V("n")), Cast(V("z"), Rationals())),
                    new Formula.Apply(Qualified("Int", "ModEq"), [D(2), V("m"), V("z")])))))))));
}
