using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermZetaFactorizationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden germ product factors through the Riemann zeta function, with an "
        + "absolutely convergent normalized product that is positive on its real ray.",
        H("Golden Germ Zeta Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-germ-zeta-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/EulerGerm/GoldenGermZetaFactorization."
                    + "golden_germ_zeta_factorization"),
                H("The golden germ has a positive zeta-normalized factor"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The normalized factor is the source-defined Euler product itself: "
                        + "each prime-local golden germ series is multiplied by the inverse "
                        + "of its first zeta mode.")),
                    Paragraph(Text(
                        "First-order cancellation leaves the beta-two tail and the square of "
                        + "the beta-one mode. Their prime sums converge above one over phi "
                        + "cubed, which proves absolute convergence of the displayed product.")),
                    Paragraph(Text(
                        "On the real ray every local series and every cancelling factor is "
                        + "positive. The real infinite product is nonzero by summable "
                        + "deviations, and its complex embedding has positive real part and "
                        + "zero imaginary part. The source's numerical window certificate is "
                        + "an empirical remark outside the named theorem."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula sigma = F.Id("sigma");
        Formula p = F.Id("p");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula thresholdSquared = Fraction(F.D(1), phiSquared);
        Formula thresholdCubed = Fraction(F.D(1), Power(F.Varphi, F.D(3)));
        Formula local = LocalFactor(s, p);
        Formula normalized = NormalizedFactor(s, p, local, phiSquared);
        Formula germProduct = PrimeProduct(local);
        Formula gAtS = Call("G", s);
        Formula gDefinition = F.Seq(
            gAtS, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(normalized));
        Formula factorization = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdSquared, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            germProduct, F.Sp, F.Eq, F.Sp,
            Call("riemannZeta", F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s)),
            F.Sp, F.Times, F.Sp, gAtS);
        Formula absoluteConvergence = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdCubed, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Summable", F.Seq(
                p, F.Mapsto, F.Sp, F.Lvert, F.Sp,
                normalized, F.Sp, F.Minus, F.Sp, F.D(1),
                F.Sp, F.Rvert)));
        Formula gAtSigma = Call("G", sigma);
        Formula positivity = F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(), F.Comma, F.Sp,
            thresholdCubed, F.Sp, F.Lt, F.Sp, sigma,
            F.Sp, F.Rightarrow, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, F.Re, F.Open, gAtSigma, F.Close,
            F.Sp, F.Land, F.Sp,
            Call("Im", gAtSigma), F.Sp, F.Eq, F.Sp, F.D(0));

        return F.Disp(F.Seq(
            gDefinition, F.Comma, F.Sp,
            F.Open, factorization, F.Close,
            F.Sp, F.Land, F.Sp,
            F.Open, absoluteConvergence, F.Close,
            F.Sp, F.Land, F.Sp,
            F.Open, positivity, F.Close, F.Dot));
    }

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore, F.Grp(F.Id("v"), F.Ge, F.D(0)),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula NormalizedFactor(
        Formula s,
        Formula p,
        Formula local,
        Formula phiSquared) =>
        F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Close, F.Sp, F.Times, F.Sp, local);

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.Sp, F.Text, F.Grp(F.Id("prime"))),
            body);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

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
