using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class ArtinSchreierQuadraticRootUniquenessDocument :
    IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Arith/ArtinSchreierQuadraticRootUniqueness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Roots of one Artin-Schreier equation with equal constant coefficients coincide.",
        H("Artin-Schreier Quadratic Root Uniqueness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("artin-schreier-quadratic-root-uniqueness"),
                DeclarationHandle.Create(Gid + "eq_of_square_add_eq_square_add"),
                H("Equal constant coefficients determine the root"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let R be a commutative ring of characteristic two and let F, G, "
                            + "and f be formal power series over R. If F squared plus F and "
                            + "G squared plus G both equal f, and F and G have the same "
                            + "constant coefficient, then F equals G. The right-hand side "
                            + "and both candidate roots remain arbitrary.")),
                    Paragraph(Text(
                        "Set D=F+G. Characteristic two turns the two equations into "
                            + "D squared plus D=0, hence D times D+1 is zero. The constant "
                            + "coefficient of D is zero, so D+1 has constant coefficient one "
                            + "and is a unit in the power-series ring. Cancelling that factor "
                            + "gives D=0 and therefore F=G. This is a symbolic ring argument; "
                            + "it uses no finite search or numerical certificate."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula ring = F.Id("R");
        Formula left = F.Id("F");
        Formula right = F.Id("G");
        Formula rhs = F.Id("f");
        Formula series = Call("PowerSeries", ring);
        Formula hypotheses = And(
            Equal(Add(Pow(left, D(2)), left), rhs),
            And(
                Equal(Add(Pow(right, D(2)), right), rhs),
                Equal(Call("constantCoeff", left), Call("constantCoeff", right))));
        Formula conclusion = Equal(left, right);

        return Disp(Seq(
            Forall, Sp, ring, Comma, Sp,
            Call("CommRing", ring), Sp, Land, Sp,
            Equal(Call("characteristic", ring), D(2)), Sp, Rightarrow, Sp,
            Forall, Sp, left, Comma, Sp, right, Comma, Sp, rhs,
            Sp, InMacro, Sp, series, Comma, Sp,
            Parenthesized(hypotheses), Sp, Rightarrow, Sp, conclusion));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
