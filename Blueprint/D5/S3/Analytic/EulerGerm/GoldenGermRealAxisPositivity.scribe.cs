using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermRealAxisPositivityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden Euler germ prime product is a strictly positive real number "
            + "throughout its full real convergence ray.",
        H("Golden Germ Real-Axis Positivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-germ-real-axis-positivity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/EulerGerm/GoldenGermRealAxisPositivity."
                        + "golden_germ_real_axis_positivity"),
                H("The golden germ product is positive on the convergence ray"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is the real-axis sign step in the golden Euler-germ "
                            + "extraction ladder of OACTC Parts 580 and 581, on the "
                            + "RH-route O-5 control line. It advances the previously "
                            + "unclosed boundary from positivity of the normalized "
                            + "factor to positivity of the original prime product on "
                            + "the entire real convergence ray.")),
                    Paragraph(Text(
                        "For sigma greater than one over phi squared, the frozen "
                            + "multipliability theorem carries the prime product and "
                            + "the frozen factorization writes it as zeta at phi "
                            + "squared times sigma multiplied by the normalized factor. "
                            + "The zeta argument is greater than one, so both factors "
                            + "are positive real numbers.")),
                    Paragraph(Text(
                        "The conclusion is confined to real sigma strictly inside the "
                            + "convergence ray. It does not assert positivity at the "
                            + "boundary, a complex zero-free region, the O-5 control "
                            + "statement, or the Riemann hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula threshold = Fraction(F.D(1), Power(F.Varphi, F.D(2)));
        Formula product = PrimeProduct(sigma);
        Formula conclusion = F.Seq(
            F.Open,
            ImaginaryPart(product), F.Sp, F.Eq, F.Sp, F.D(0),
            F.Sp, F.Land, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, RealPart(product),
            F.Close);

        return F.Disp(F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(),
            F.Comma, F.Sp,
            threshold, F.Sp, F.Lt, F.Sp, sigma,
            F.Sp, F.Rightarrow, F.Sp, conclusion, F.Dot));
    }

    private static Formula LocalFactor(Formula sigma, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, sigma, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula PrimeProduct(Formula sigma) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            LocalFactor(sigma, F.Id("p")));

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Open, value, F.Close);

    private static Formula ImaginaryPart(Formula value) =>
        Call("Im", value);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
