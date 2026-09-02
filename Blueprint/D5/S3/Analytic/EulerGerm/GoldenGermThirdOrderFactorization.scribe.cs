using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermThirdOrderFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization."
            + "golden_germ_third_order_factorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third-order golden Euler factors give a unique continuation as a function "
            + "above one over phi to the fifth power and retain the canonical germ on its "
            + "original convergence half-plane.",
        H("Golden Germ Third-Order Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-third-order-factorization"),
            DeclarationHandle.Create(Declaration),
            H("Third-order factorization continues the golden germ past the phi-fifth line"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The frozen third-order ledger supplies the displayed local factor Kp "
                        + "and proves that its deviation from one is norm-summable when the "
                        + "real part exceeds one over phi to the fifth power. Consequently its "
                        + "prime product G3 is carried by a genuine Multipliable family.")),
                Paragraph(Text(
                    "On the original half-plane, the frozen second-order factorization is "
                        + "continued by extracting the Euler factors for twice phi-cubed and "
                        + "for two phi-squared plus phi-cubed. HasProd uniqueness identifies "
                        + "the resulting five-zeta expression with the canonical germ product. "
                        + "The displayed computation rule then determines the function uniquely "
                        + "throughout the larger half-plane.")),
                Paragraph(Text(
                    "This is the global third-order step in the golden Euler germ extraction "
                        + "staircase used in OACTC parts 580 and 581 and on the RH-route O-5 "
                        + "control line. It advances the previously open continuation boundary "
                        + "from one over phi to the fourth power to one over phi to the fifth "
                        + "power. The theorem asserts neither holomorphy nor meromorphic "
                        + "continuation on that region, and it does not assert nonvanishing, "
                        + "O-5, or the Riemann Hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderLedger")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula continuation = F.Id("Zphi");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula thresholdSquared = Fraction(F.D(1), phiSquared);
        Formula thresholdFifth = Fraction(F.D(1), Power(F.Varphi, F.D(5)));
        Formula xAtP = Call("x", p);
        Formula yAtP = Call("y", p);
        Formula kpAtSP = Call("Kp", s, p);
        Formula gAtS = Call("G3", s);
        Formula local = LocalFactor(s, p);
        Formula xDefinition = F.Seq(
            xAtP, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)));
        Formula yDefinition = F.Seq(
            yAtP, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed)));
        Formula kpDefinition = F.Seq(
            kpAtSP, F.Sp, F.Colon, F.Eq, F.Sp,
            NormalizedFactor(local, xAtP, yAtP));
        Formula gDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            gAtS, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(kpAtSP));
        Formula absoluteConvergence = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdFifth, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Summable", F.Seq(
                p, F.Colon, F.Sp, Call("Primes", NaturalNumbers()), F.Sp,
                F.Mapsto, F.Sp, F.Lvert,
                kpAtSP, F.Sp, F.Minus, F.Sp, F.D(1), F.Rvert)));
        Formula continuationDomain = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, ComplexNumbers(), F.Sp, F.Mid, F.Sp,
            thresholdFifth, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.CloseBrace);
        Formula agreement = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdSquared, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Zphi", s), F.Sp, F.Eq, F.Sp, PrimeProduct(local));
        Formula factorization = Factorization(
            s,
            thresholdFifth,
            continuation,
            phiSquared,
            phiCubed,
            gAtS);

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma,
                F.Sp, p, F.InMacro, F.Sp, Call("Primes", NaturalNumbers()),
                F.Comma),
            F.Seq(
                xDefinition, F.Comma, F.Sp, yDefinition, F.Comma, F.Sp,
                kpDefinition, F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(F.Open, absoluteConvergence, F.Close, F.Sp, F.Land),
            F.Seq(
                F.Open, F.Exists, F.Bang, F.Sp, continuation, F.Colon, F.Sp,
                continuationDomain, F.Sp, F.To, F.Sp, ComplexNumbers(), F.Comma),
            F.Seq(F.Open, agreement, F.Close, F.Sp, F.Land, F.Sp,
                F.Open, factorization, F.Close, F.Close, F.Dot),
        ]));
    }

    private static Formula Factorization(
        Formula s,
        Formula thresholdFifth,
        Formula continuation,
        Formula phiSquared,
        Formula phiCubed,
        Formula gAtS)
    {
        Formula zetaSquared = Call("riemannZeta",
            F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s));
        Formula zetaCubed = Call("riemannZeta",
            F.Seq(phiCubed, F.Sp, F.Times, F.Sp, s));
        Formula zetaDoubleSquared = Call("riemannZeta",
            F.Seq(F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
                F.Sp, F.Times, F.Sp, s));
        Formula zetaDoubleCubed = Call("riemannZeta",
            F.Seq(F.D(2), F.Sp, F.Times, F.Sp, phiCubed,
                F.Sp, F.Times, F.Sp, s));
        Formula mixedWeight = F.Seq(
            F.Open,
            F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Plus, F.Sp, phiCubed,
            F.Close);
        Formula zetaMixed = Call("riemannZeta",
            F.Seq(mixedWeight, F.Sp, F.Times, F.Sp, s));

        return F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdFifth, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Zphi", s), F.Sp, F.Eq, F.Sp,
            zetaSquared, F.Sp, F.Times, F.Sp,
            zetaCubed, F.Sp, F.Times, F.Sp,
            Power(zetaDoubleSquared, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp,
            Power(zetaDoubleCubed, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp,
            zetaMixed, F.Sp, F.Times, F.Sp, gAtS);
    }

    private static Formula NormalizedFactor(
        Formula local,
        Formula x,
        Formula y)
    {
        Formula oneMinusYSquared = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, Power(y, F.D(2)), F.Close);
        Formula oneMinusXSquaredY = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(x, F.D(2)), F.Sp, F.Times, F.Sp, y, F.Close);
        Formula oneMinusY = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, y, F.Close);
        Formula onePlusX = F.Seq(
            F.Open, F.D(1), F.Sp, F.Plus, F.Sp, x, F.Close);

        return F.Seq(
            Power(oneMinusYSquared, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, oneMinusXSquaredY,
            F.Sp, F.Times, F.Sp, oneMinusY,
            F.Sp, F.Times, F.Sp,
            Power(onePlusX, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, local);
    }

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

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
