using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GermProductNonvanishingExactThresholdDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GermProductNonvanishingExactThreshold."
            + "germ_product_nonvanishing_exact_threshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime-2 majorant has a unique unit crossing below three fifths, and the "
            + "prime-2 factor and full golden Euler product are nonzero above it.",
        H("Exact Prime-Two Majorant Threshold"),
        Blocks(Describe.Lean(
            DescribeId.Create("germ-product-nonvanishing-exact-threshold"),
            DeclarationHandle.Create(Declaration),
            H("The majorant threshold gives a sharper zero-free half-plane"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem sits in the golden Euler-germ extraction ladder of "
                        + "OACTC Parts 580 and 581, on the RH-route O-5 control line. It "
                        + "replaces the rational endpoint three fifths by the unique unit "
                        + "crossing of the explicit two-term prime-2 majorant.")),
                Paragraph(Text(
                    "The majorant is continuous and strictly decreasing on the positive "
                        + "ray. Exact endpoint estimates put its crossing strictly between "
                        + "one over phi squared and three fifths. Above that crossing, the "
                        + "parameterized geometric-tail estimate has norm below one, so it "
                        + "cannot cancel the vacuum term of the prime-2 local factor.")),
                Paragraph(Text(
                    "Odd-prime local factors are already nonzero throughout the open "
                        + "convergence half-plane. The frozen infinite-product bridge then "
                        + "turns pointwise local nonvanishing into nonvanishing of the full "
                        + "t-product; convergence is carried by its separate frozen input.")),
                Paragraph(Text(
                    "The threshold here belongs only to this explicit majorant method. The "
                        + "theorem does not identify the actual boundary of the local zero "
                        + "set, does not assert a zero below the threshold, and does not "
                        + "establish O-5 or the Riemann hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GermProductNonvanishingAboveThreeFifths")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula tau = F.Id("tau");
        Formula sigmaStar = F.Id("sigmaStar");
        Formula f = F.Id("f");
        Formula s = F.Id("s");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula convergenceBoundary = Fraction(F.D(1), phiSquared);
        Formula interval = F.Seq(
            F.Open, convergenceBoundary, F.Comma, F.Sp,
            Fraction(F.D(3), F.D(5)), F.Close);
        Formula positiveRay = F.Seq(F.Open, F.D(0), F.Comma, F.Sp, F.Infty, F.Close);
        Formula two = F.Seq(F.Open, F.D(2), F.Close);
        Formula value = F.Seq(
            Power(two, F.Seq(
                F.Minus, sigma, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Sp, F.Plus, F.Sp,
            Power(two, F.Seq(F.Minus, sigma)));
        Formula fDefinition = F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(), F.Comma, F.Sp,
            Call("f", sigma), F.Sp, F.Colon, F.Eq, F.Sp, value);
        Formula thresholdDefinition = F.Seq(
            sigmaStar, F.Sp, F.Colon, F.Eq, F.Sp, F.Id("primeTwoThreshold"));
        Formula thresholdSpec = F.Seq(
            sigmaStar, F.InMacro, F.Sp, interval,
            F.Sp, F.Land, F.Sp,
            Call("f", sigmaStar), F.Sp, F.Eq, F.Sp, F.D(1),
            F.Sp, F.Land, F.Sp,
            F.Forall, F.Sp, tau, F.InMacro, F.Sp, interval, F.Comma, F.Sp,
            Call("f", tau), F.Sp, F.Eq, F.Sp, F.D(1),
            F.Sp, F.Rightarrow, F.Sp, tau, F.Sp, F.Eq, F.Sp, sigmaStar);
        Formula localNonvanishing = ForallComplex(s, F.Seq(
            sigmaStar, F.Sp, F.Lt, F.Sp, RealPart(s),
            F.Sp, F.Rightarrow, F.Sp,
            LocalFactor(s, F.D(2)), F.Sp, F.Neq, F.Sp, F.D(0)));
        Formula productNonvanishing = ForallComplex(s, F.Seq(
            sigmaStar, F.Sp, F.Lt, F.Sp, RealPart(s),
            F.Sp, F.Rightarrow, F.Sp,
            PrimeProduct(s), F.Sp, F.Neq, F.Sp, F.D(0)));

        return F.Disp(new Formula.Aligned([
            F.Seq(fDefinition, F.Comma),
            F.Seq(thresholdDefinition, F.Comma),
            F.Seq(Call("ContinuousOn", f, positiveRay), F.Sp, F.Land),
            F.Seq(Call("StrictAntiOn", f, positiveRay), F.Sp, F.Land),
            F.Seq(F.Open, thresholdSpec, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, localNonvanishing, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, productNonvanishing, F.Close, F.Dot),
        ]));
    }

    private static Formula ForallComplex(Formula variable, Formula body) =>
        F.Seq(
            F.Forall, F.Sp, variable, F.InMacro, F.Sp, ComplexNumbers(),
            F.Comma, F.Sp, body);

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula PrimeProduct(Formula s) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            LocalFactor(s, F.Id("p")));

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Open, value, F.Close);

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

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
