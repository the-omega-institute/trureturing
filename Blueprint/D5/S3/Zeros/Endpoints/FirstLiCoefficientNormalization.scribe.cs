using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Endpoints;

internal sealed class FirstLiCoefficientNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first Li coefficient normalizes the completed-zeta logarithmic derivative at one.",
        H("First Li Coefficient Normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-li-coefficient-normalization"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Endpoints/FirstLiCoefficientNormalization."
                        + "first_li_coefficient_normalization"),
                H("The first Li coefficient gives unit normalization"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public first coefficient is the source's explicit real constant "
                            + "one plus one half of the Euler-Mascheroni constant minus the "
                            + "logarithm of twice the square root of pi. The first conjunct "
                            + "identifies it with the logarithmic derivative of the canonical "
                            + "xi reading at one.")),
                    Paragraph(Text(
                        "The proof differentiates the frozen pole-removed xi formula and reuses "
                            + "the frozen endpoint value xiReading(1) = 1/2. Certified rational "
                            + "bounds for the Euler-Mascheroni constant, pi, and the exponential "
                            + "series prove that the coefficient is positive, so reciprocal "
                            + "cancellation yields the second public conjunct."))),
                DescribeRole.Theorem)),
        []));

    private static Formula TheoremFormula()
    {
        Formula lambdaOne = new Formula.Subscript(F.Id("lambda"), D(1));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula firstCoefficient = Subtract(
            Add(
                D(1),
                new Formula.Fraction(Call("eulerMascheroniConstant"), D(2))),
            Call("log", Multiply(D(2), Call("sqrt", Pi))));
        Formula lambdaComplex = Call("complex", lambdaOne);
        Formula ratio = new Formula.Fraction(
            Call("deriv", F.Id("xiReading"), D(1)),
            Call("xiReading", D(1)));
        Formula identification = Equal(ratio, lambdaComplex);
        Formula normalization = Equal(
            Multiply(new Formula.Fraction(D(1), lambdaComplex), ratio),
            D(1));

        return Disp(Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            lambdaOne, Colon, Sp, real, Colon, Eq, firstCoefficient,
            Semi, Sp,
            new Formula.Logic(
                identification,
                FormulaLogicOperator.And,
                normalization)));
    }
}
