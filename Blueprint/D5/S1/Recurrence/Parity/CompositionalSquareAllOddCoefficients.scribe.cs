using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class CompositionalSquareAllOddCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Parity/CompositionalSquareAllOddCoefficients.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a396843");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-index coefficient in the series of OEIS A396843 is odd.",
        H("All Coefficients of the A396843 Series Are Odd"),
        Blocks(
            Paragraph(Text("Let A be an integer formal power series with constant coefficient "
                + "zero satisfying A(x A(x)-3x A(x)^2)=x^2. Reducing coefficients modulo two "
                + "gives F(H)=x^2, where H=x(F+F^2).")),
            Describe.Lean(
                DescribeId.Create("a396843-hanna-conjecture"),
                DeclarationHandle.Create(Prefix + "hanna_conjecture"),
                H("Hanna's A396843 parity conjecture"),
                StatementSource.FromAuthor(HannaFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The coefficient of x^2 first gives coeff(1,F)=1. "
                    + "If two solutions agree below degree d, their inner series agree "
                    + "through degree d, while powers of either inner series from the "
                    + "second power onward cannot affect the next comparison. Hence the "
                    + "equation determines each coefficient successively. The series "
                    + "S=x/(1+x) satisfies x(S+S^2)=x^2/(1+x)^2 and therefore "
                    + "S(x(S+S^2))=x^2. Uniqueness gives F=S, whose every positive-degree "
                    + "coefficient is one modulo two."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a396843-compositional-square-all-odd-coefficients"),
                    ResolutionKind.Proved)))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));

    private static Formula HannaFormula()
    {
        Formula a = F.Id("A");
        Formula x = F.Id("X");
        Formula n = F.Id("n");
        Formula argument = Subtract(Mul(x, a), Mul(Mul(D(3), x), Power(a, D(2))));
        Formula equation = Equal(Call("subst", a, argument), Power(x, D(2)));
        Formula conclusion = Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Le, Sp, n), Call("Odd", Call("coeff", n, a))));
        return Disp(Seq(Bound("A", Series()),
            Implication(Equal(Call("constantCoeff", a), D(0)),
                Implication(equation, conclusion))));
    }
}
