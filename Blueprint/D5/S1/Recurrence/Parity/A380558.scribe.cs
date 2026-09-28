using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class A380558Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/A380558.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2025a380558");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized A380558 series has odd coefficients exactly at twice the stated binary-prefix indices.",
        H("Parity of the A380558 Square-Reversion Series"),
        Blocks(
            Paragraph(Text(
                "Paul D. Hanna's A380558 entry defines A by A(x-A(x))=x^2/(1-x^2) "
                + "and labels its parity characterization a conjecture. The source also "
                + "gives A=B^2/(1-B^2), where B(x-A(x))=x. The earlier project "
                + "formalization of A380678 supplies B; this result identifies A with "
                + "the unique normalized integral solution before proving parity.")),
            Paragraph(Text(
                "A and B are integral formal power series, X is the indeterminate, "
                + "and all indices and exponents are natural. Rational expressions "
                + "mean formal inverses of denominators with constant coefficient one. "
                + "The notation coeff(n,A) extracts degree n. The uniqueness clause "
                + "quantifies over every integral series F whose constant and linear "
                + "coefficients vanish; the parity clause covers every natural n.")),
            Describe.Lean(
                DescribeId.Create("a380558-generating-series"),
                DeclarationHandle.Create(Prefix + "generatingSeries"),
                H("The source generating series"),
                StatementSource.FromAuthor(GeneratingFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the transform in A380558's formula field, applied to "
                    + "the previously constructed integral reversion series B. The "
                    + "denominator 1-B^2 is a unit because B has zero constant term."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a380558-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Source identity, uniqueness, and complete parity support"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Compositional inversion proves that the transformed series "
                    + "satisfies the source equation and is its only normalized "
                    + "integral solution. Modulo two, write L for the previously "
                    + "proved lacunary reduction of B and T=L/(1-L). Algebra gives "
                    + "T=X+X^2+(1+X)T^2. Frobenius and strong induction show that "
                    + "the coefficient of T is one exactly at 1 and in the dyadic "
                    + "half-open intervals [3*2^j,4*2^j). The reduction of A is T^2, "
                    + "which doubles those degrees. The exceptional value 1 in "
                    + "A004760 gives n=2; odd degrees and the upper endpoints are "
                    + "excluded. This settles the full bidirectional A380558 comment "
                    + "with its natural zero extension at degrees zero and one."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a380558-parity"),
                    ResolutionKind.Proved)))));

    private static Formula A() => F.Id("A");
    private static Formula B() => F.Id("B");
    private static Formula X() => F.Id("X");
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula J() => F.Id("j");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Subtract(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Cdot, Sp, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula ImpliesFormula(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Rational(Formula f) =>
        Seq(Frac, Grp(Power(f, D(2))), Grp(Subtract(D(1), Power(f, D(2)))));
    private static Formula SourceEquation(Formula f) =>
        Equal(Call("subst", f, Subtract(X(), f)), Rational(X()));
    private static Formula ZeroLinear(Formula f) => And(
        Equal(Call("constantCoeff", f), D(0)),
        Equal(Call("coeff", D(1), f), D(0)));

    private static Formula GeneratingFormula() => Disp(Equal(A(), Rational(B())));

    private static Formula ResultFormula()
    {
        var f = F.Id("F");
        var parity = Seq(
            Call("Odd", Call("coeff", N(), A())), Sp, Iff, Sp,
            Parenthesized(Seq(Equal(N(), D(2)), Sp, Lor, Sp,
                Exists, Sp, M(), Comma, Sp, J(), Colon, Sp, Naturals(), Comma, Sp,
                And(Equal(N(), Mul(D(2), M())),
                    And(Seq(Mul(D(3), Power(D(2), J())), Sp, Le, Sp, M()),
                        Seq(M(), Sp, Lt, Sp, Mul(D(4), Power(D(2), J()))))))));
        var uniqueness = Seq(Bound("F", Call("PowerSeries", Integers())),
            ImpliesFormula(And(ZeroLinear(f), SourceEquation(f)), Equal(f, A())));
        return Disp(new Formula.Aligned([
            Seq(Parenthesized(ZeroLinear(A())), Sp, Land),
            Seq(Parenthesized(SourceEquation(A())), Sp, Land),
            Seq(Parenthesized(uniqueness), Sp, Land),
            Seq(Bound("n", Naturals()), parity)
        ]));
    }
}
