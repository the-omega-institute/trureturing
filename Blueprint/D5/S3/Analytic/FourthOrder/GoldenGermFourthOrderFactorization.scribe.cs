using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.FourthOrder;

internal sealed class GoldenGermFourthOrderFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/FourthOrder/GoldenGermFourthOrderFactorization."
            + "golden_germ_fourth_order_factorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth-order normalized golden Euler factors give a unique seven-zeta "
            + "continuation as a function above the reciprocal beta-six boundary.",
        H("Golden Germ Fourth-Order Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-fourth-order-factorization"),
            DeclarationHandle.Create(Declaration),
            H("Fourth-order extraction gives the unique seven-zeta germ formula"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The frozen fourth-order ledger supplies the exact correction of the "
                        + "third-order local factor and proves norm summability of K4 minus "
                        + "one whenever the real part exceeds one over beta six. Thus G4 is "
                        + "represented by a genuine Multipliable prime family, not merely by "
                        + "the totalized notation for an infinite product.")),
                Paragraph(Text(
                    "On the original convergence half-plane, Euler products for the weights "
                        + "A and B identify the old normalized product with zeta of A s times "
                        + "the inverse of zeta of B s times G4. Substitution into the frozen "
                        + "third-order continuation gives the displayed seven-zeta formula. "
                        + "Defining the continued function by that formula also makes its "
                        + "uniqueness pointwise and explicit on the beta-six half-plane.")),
                Paragraph(Text(
                    "This is the fourth-order global step in the golden Euler germ extraction "
                        + "ladder of OACTC parts 580 and 581. It advances the previously open "
                        + "continuation boundary from one over phi to the fifth power to one "
                        + "over beta six. The theorem asserts neither holomorphy nor meromorphic "
                        + "continuation on that region, and it does not assert nonvanishing, "
                        + "O-5, the Riemann Hypothesis, or an all-order extraction."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderLedger")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderExponentCensus")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula continuation = F.Id("continuedGerm");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula betaSix = Call("o5Beta", F.D(6));
        Formula thresholdSquared = Fraction(F.D(1), phiSquared);
        Formula thresholdBetaSix = Fraction(F.D(1), betaSix);
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula x = Call("x", s, p);
        Formula y = Call("y", s, p);
        Formula k4 = Call("K4", s, p);
        Formula g4 = Call("G4", s);
        Formula local = Call("germLocalFactor", s, p);

        Formula aDefinition = F.Seq(
            a, F.Sp, F.Colon, F.Eq, F.Sp,
            phiSquared, F.Sp, F.Plus, F.Sp,
            F.D(2), F.Sp, F.Times, F.Sp, phiCubed);
        Formula bDefinition = F.Seq(
            b, F.Sp, F.Colon, F.Eq, F.Sp,
            F.D(3), F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Plus, F.Sp, phiCubed);
        Formula xDefinition = F.Seq(
            x, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)));
        Formula yDefinition = F.Seq(
            y, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed)));
        Formula k4Definition = F.Seq(
            k4, F.Sp, F.Colon, F.Eq, F.Sp,
            FourthNormalizedFactor(local, x, y));
        Formula g4Definition = F.Seq(
            g4, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(k4));
        Formula absoluteConvergence = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdBetaSix, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Summable", F.Seq(
                p, F.Colon, F.Sp, PrimeNumbers(), F.Sp, F.Mapsto, F.Sp,
                F.Lvert, k4, F.Sp, F.Minus, F.Sp, F.D(1), F.Rvert)));
        Formula continuationDomain = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, ComplexNumbers(), F.Sp, F.Mid, F.Sp,
            thresholdBetaSix, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.CloseBrace);
        Formula agreement = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdSquared, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("continuedGerm", s), F.Sp, F.Eq, F.Sp, PrimeProduct(local));
        Formula factorization = Factorization(
            s, thresholdBetaSix, phiSquared, phiCubed, a, b, g4);

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma,
                F.Sp, p, F.InMacro, F.Sp, PrimeNumbers(), F.Comma),
            F.Seq(aDefinition, F.Comma, F.Sp, bDefinition, F.Comma),
            F.Seq(xDefinition, F.Comma, F.Sp, yDefinition, F.Comma),
            F.Seq(k4Definition, F.Comma, F.Sp, g4Definition, F.Comma),
            F.Seq(F.Open, absoluteConvergence, F.Close, F.Sp, F.Land),
            F.Seq(
                F.Open, F.Exists, F.Bang, F.Sp, continuation, F.Colon, F.Sp,
                continuationDomain, F.Sp, F.To, F.Sp, ComplexNumbers(), F.Comma),
            F.Seq(
                F.Open, agreement, F.Close, F.Sp, F.Land, F.Sp,
                F.Open, factorization, F.Close, F.Close, F.Dot),
        ]));
    }

    private static Formula Factorization(
        Formula s,
        Formula threshold,
        Formula phiSquared,
        Formula phiCubed,
        Formula a,
        Formula b,
        Formula g4)
    {
        Formula zetaSquared = Zeta(F.Seq(
            phiSquared, F.Sp, F.Times, F.Sp, s));
        Formula zetaCubed = Zeta(F.Seq(
            phiCubed, F.Sp, F.Times, F.Sp, s));
        Formula zetaDoubleSquared = Zeta(F.Seq(
            F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Times, F.Sp, s));
        Formula zetaDoubleCubed = Zeta(F.Seq(
            F.D(2), F.Sp, F.Times, F.Sp, phiCubed,
            F.Sp, F.Times, F.Sp, s));
        Formula thirdMixedWeight = Parenthesize(F.Seq(
            F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Plus, F.Sp, phiCubed));
        Formula zetaThirdMixed = Zeta(F.Seq(
            thirdMixedWeight, F.Sp, F.Times, F.Sp, s));
        Formula zetaA = Zeta(F.Seq(a, F.Sp, F.Times, F.Sp, s));
        Formula zetaB = Zeta(F.Seq(b, F.Sp, F.Times, F.Sp, s));

        return F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            threshold, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("continuedGerm", s), F.Sp, F.Eq, F.Sp,
            zetaSquared, F.Sp, F.Times, F.Sp,
            zetaCubed, F.Sp, F.Times, F.Sp,
            Power(zetaDoubleSquared, NegativeOne()),
            F.Sp, F.Times, F.Sp,
            Power(zetaDoubleCubed, NegativeOne()),
            F.Sp, F.Times, F.Sp,
            zetaThirdMixed, F.Sp, F.Times, F.Sp,
            zetaA, F.Sp, F.Times, F.Sp,
            Power(zetaB, NegativeOne()),
            F.Sp, F.Times, F.Sp, g4);
    }

    private static Formula FourthNormalizedFactor(
        Formula local,
        Formula x,
        Formula y)
    {
        Formula oneMinusXYSquared = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp,
            x, F.Sp, F.Times, F.Sp, Power(y, F.D(2))));
        Formula oneMinusXCubedY = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp,
            Power(x, F.D(3)), F.Sp, F.Times, F.Sp, y));
        Formula oneMinusYSquared = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp, Power(y, F.D(2))));
        Formula oneMinusXSquaredY = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp,
            Power(x, F.D(2)), F.Sp, F.Times, F.Sp, y));
        Formula oneMinusY = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp, y));
        Formula onePlusX = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Plus, F.Sp, x));

        return F.Seq(
            oneMinusXYSquared, F.Sp, F.Times, F.Sp,
            Power(oneMinusXCubedY, NegativeOne()),
            F.Sp, F.Times, F.Sp,
            Power(oneMinusYSquared, NegativeOne()),
            F.Sp, F.Times, F.Sp, oneMinusXSquaredY,
            F.Sp, F.Times, F.Sp, oneMinusY,
            F.Sp, F.Times, F.Sp,
            Power(onePlusX, NegativeOne()),
            F.Sp, F.Times, F.Sp, local);
    }

    private static Formula Zeta(Formula argument) =>
        Call("riemannZeta", argument);

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, PrimeNumbers()),
            body);

    private static Formula Parenthesize(Formula body) =>
        F.Seq(F.Open, body, F.Close);

    private static Formula NegativeOne() =>
        F.Seq(F.Minus, F.D(1));

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula PrimeNumbers() =>
        Call("Primes", NaturalNumbers());

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
