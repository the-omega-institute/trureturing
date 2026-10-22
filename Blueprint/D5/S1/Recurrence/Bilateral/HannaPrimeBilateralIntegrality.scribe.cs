using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Bilateral;

internal sealed class HannaPrimeBilateralIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a380681");
    private const string Quotation = "Conjecture: if F(x) satisfies p*x = Sum_{n=-oo..+oo} (-1)^n * x^(p*n) * (F(x) + x^n)^(p*n) with F(0) = 1 for some fixed integer p, then F(x) is an integer series in x iff p is prime. The g.f. A(x) of this sequence is the case when p = 2; other cases include A380682 (p=3), A380683 (p=5), A380684 (p=7), A380685 (p=11), and A380686 (p=13).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized bilateral equation has an integral solution exactly at prime parameters.",
        H("Hanna's Prime Bilateral Integrality Conjecture"),
        Blocks(
            Paragraph(Text("PowerSeries and LaurentSeries are formal series over the rationals. "
                + "The parameter p and coefficient indices N, K, n are natural numbers; j is an integer. "
                + "HahnSeries.ofPowerSeries embeds power series in Laurent series, where powers "
                + "have integer exponents. Natural numbers and integers in rational expressions "
                + "are cast to the rationals. The parameter range is p at least two.")),
            Node("term", "The Laurent-series summand", Disp(TermFormula()),
                "The unpaginated Comments of OEIS A380681 state: \"" + Quotation + "\" "
                + "Here x is the embedded indeterminate and G is the embedded F. The sign "
                + "and the two remaining factors use the source's integer exponents.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSolution", "The coefficientwise bilateral equation", Disp(SolutionFormula()),
                "The unpaginated Comments of OEIS A380681 state: \"" + Quotation + "\" "
                + "The constant coefficient is one. At degree N, the sum is over every integer "
                + "j in [-K,K], for every K at least N+1. Thus the right side is p at degree "
                + "one and zero at every other degree.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Existence and the prime criterion", Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "The unpaginated Comments of OEIS A380681 state: \"" + Quotation + "\" "
                + "For each natural p at least two a normalized rational solution exists, "
                + "and each normalized rational solution has all coefficients in the integers "
                + "if and only if p is prime. Parameters at most zero are outside this statement.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Prime parameters characterize integral solutions", Disp(ClaimBody()),
                "Factoring the negative Laurent powers gives finite coefficient sums. "
                + "At parameter one, a reindexing pairs the positive and negative binomial "
                + "terms with opposite signs. Frobenius then makes every coefficient of "
                + "the parameter-p sum divisible by p when p is prime. Removing its linear "
                + "term gives a contraction by one coefficient degree; compatible iterates "
                + "construct the normalized rational solution and prove its integrality at "
                + "prime p. Below degree p, the equation reduces to the binomial expansion "
                + "of (1-pX) to exponent -1/p. At a composite p, the least prime divisor "
                + "divides the coefficient's factorial denominator and none of its numerator "
                + "factors, contradicting integrality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("hanna-prime-bilateral-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Laurent() => Call("LaurentSeries", Rationals());
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula AtMost(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Negative(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Equiv(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Embed(Formula f) => App(Qualified("HahnSeries", "ofPowerSeries"), Integers(), Rationals(), f);
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(Named("let"), Sp, F.Id(name), Colon, Sp, type, Sp, Eq, Sp, value,
            Semi, Sp, body);
    private static Formula TermFormula()
    {
        var p = F.Id("p"); var f = F.Id("F"); var n = F.Id("n");
        var x = F.Id("x"); var g = F.Id("G"); var exponent = Mul(Cast(p, Integers()), n);
        return All("p", Naturals(), All("F", Series(), All("n", Integers(),
            Equal(Call("term", p, f, n), Parenthesized(
                Let("x", Laurent(), Embed(F.Id("X")), Let("G", Laurent(), Embed(f),
                    Mul(Mul(Pow(Cast(Negative(D(1)), Laurent()), n), Pow(x, exponent)),
                        Pow(Parenthesized(Add(g, Pow(x, n))), exponent)))))))));
    }
    private static Formula SolutionFormula()
    {
        var p = F.Id("p"); var f = F.Id("F"); var n = F.Id("N");
        var k = F.Id("K"); var j = F.Id("j");
        var set = App(Qualified("Finset", "Icc"), Negative(Cast(k, Integers())), Cast(k, Integers()));
        var summand = App(Qualified("HahnSeries", "coeff"), Call("term", p, f, j), Cast(n, Integers()));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(j, Sp, InMacro, Sp, set)), Sp, Parenthesized(summand));
        var target = Seq(Named("if"), Sp, Parenthesized(Equal(n, D(1))), Sp,
            Named("then"), Sp, Cast(p, Rationals()), Sp, Named("else"), Sp, D(0));
        return All("p", Naturals(), All("F", Series(), Equal(Call("IsSolution", p, f),
            Parenthesized(And(Equal(Call("constantCoeff", f), D(1)),
                All("N", Naturals(), All("K", Naturals(), Arrow(AtMost(Add(n, D(1)), k), Equal(sum, target)))))))));
    }
    private static Formula ClaimBody()
    {
        var p = F.Id("p"); var f = F.Id("F"); var n = F.Id("n"); var z = F.Id("z");
        var integral = All("n", Naturals(), Some("z", Integers(),
            Equal(Call("coeff", n, f), Cast(z, Rationals()))));
        return All("p", Naturals(), Arrow(AtMost(D(2), p),
            And(Some("F", Series(), Call("IsSolution", p, f)),
                All("F", Series(), Arrow(Call("IsSolution", p, f),
                    Equiv(integral, App(Qualified("Nat", "Prime"), p)))))));
    }
}
