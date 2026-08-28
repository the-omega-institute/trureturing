using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermSecondOrderFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization."
            + "golden_germ_second_order_factorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden germ has a canonical second-order continuation with two direct zeta "
            + "factors, one reciprocal zeta factor, and an absolutely convergent tail.",
        H("Golden Germ Second-Order Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-second-order-factorization"),
            DeclarationHandle.Create(Declaration),
            H("The signed second-order factors continue the canonical golden germ"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The continuation is uniquely determined by its displayed computation "
                        + "rule and agrees with the canonical prime product on the original "
                        + "absolute-convergence half-plane.")),
                Paragraph(Text(
                    "The normalized local factor cancels the phi-cubed mode and divides by "
                        + "one plus the phi-squared mode. Its deviation is absolutely "
                        + "summable above one over phi to the fourth power.")),
                Paragraph(Text(
                    "The reciprocal zeta factor is public in the formula. Fitted slopes, "
                        + "decimal thresholds, and finite-window error comparisons are "
                        + "empirical remarks outside the named theorem."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermZetaFactorization")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula continuation = F.Id("Zqc2");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula thresholdSquared = Fraction(F.D(1), phiSquared);
        Formula thresholdFourth = Fraction(F.D(1), Power(F.Varphi, F.D(4)));
        Formula local = LocalFactor(s, p);
        Formula normalized = NormalizedFactor(s, p, local, phiSquared, phiCubed);
        Formula germProduct = PrimeProduct(local);
        Formula gAtS = Call("G3", s);
        Formula gType = F.Seq(
            F.Id("G3"), F.Colon, F.Sp, ComplexNumbers(),
            F.Sp, F.To, F.Sp, ComplexNumbers());
        Formula gDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            gAtS, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(normalized));
        Formula continuationDomain = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, ComplexNumbers(), F.Sp, F.Mid, F.Sp,
            thresholdFourth, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.CloseBrace);
        Formula agreement = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdSquared, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Zqc2", s), F.Sp, F.Eq, F.Sp, germProduct);
        Formula zetaSquared = Call("riemannZeta",
            F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s));
        Formula zetaCubed = Call("riemannZeta",
            F.Seq(phiCubed, F.Sp, F.Times, F.Sp, s));
        Formula zetaDoubleSquared = Call("riemannZeta",
            F.Seq(F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
                F.Sp, F.Times, F.Sp, s));
        Formula factorization = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdFourth, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Zqc2", s), F.Sp, F.Eq, F.Sp,
            zetaSquared, F.Sp, F.Times, F.Sp,
            zetaCubed, F.Sp, F.Times, F.Sp,
            Power(zetaDoubleSquared, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, gAtS);
        Formula absoluteConvergence = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdFourth, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Summable", F.Seq(
                p, F.Colon, F.Sp, Call("Primes", NaturalNumbers()), F.Sp,
                F.Mapsto, F.Sp, F.Lvert, F.Sp,
                normalized, F.Sp, F.Minus, F.Sp, F.D(1), F.Sp, F.Rvert)));

        return F.Disp(new Formula.Aligned([
            F.Seq(gType, F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(
                F.Open, F.Exists, F.Bang, F.Sp, continuation, F.Colon, F.Sp,
                continuationDomain, F.Sp, F.To, F.Sp, ComplexNumbers(), F.Comma),
            F.Seq(F.Open, agreement, F.Close, F.Sp, F.Land, F.Sp,
                F.Open, factorization, F.Close, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, absoluteConvergence, F.Close, F.Dot),
        ]));
    }

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula NormalizedFactor(
        Formula s,
        Formula p,
        Formula local,
        Formula phiSquared,
        Formula phiCubed)
    {
        Formula cubedMode = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed));
        Formula squaredMode = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared));

        return F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, cubedMode, F.Close,
            F.Sp, F.Times, F.Sp,
            Power(F.Seq(F.Open, F.D(1), F.Sp, F.Plus, F.Sp,
                squaredMode, F.Close), F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, local);
    }

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            body);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

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
