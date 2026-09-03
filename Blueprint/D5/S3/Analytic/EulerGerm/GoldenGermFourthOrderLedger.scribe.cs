using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermFourthOrderLedgerDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderLedger."
            + "golden_fourth_normalized_factor_deviation_norm_summable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite signed fourth-order correction cancels the two surviving local modes "
            + "below beta six and leaves a norm-summable prime deviation.",
        H("Golden Germ Fourth-Order Ledger"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-fourth-order-ledger"),
            DeclarationHandle.Create(Declaration),
            H("Fourth-order local cancellation reaches the beta-six boundary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The frozen fourth-order exponent census identifies x y-squared and "
                        + "x-cubed y as the two surviving correction modes below beta six. "
                        + "The signed factor C4 is therefore one minus x y-squared times the "
                        + "inverse of one minus x-cubed y. The displayed twelve-term "
                        + "polynomial H4 has no monomial below beta six; x-squared y-squared "
                        + "is its boundary term.")),
                Paragraph(Text(
                    "The theorem reuses the frozen third-order local factor K3 and records "
                        + "the exact rational identity C4 K3 equals one plus R4. Its shifted "
                        + "seventh-mode tail starts above beta six, and every factor arising "
                        + "from the numerator and denominator expansions adds a nonnegative "
                        + "mixed weight. Prime rpow summability and uniform geometric "
                        + "denominator bounds then prove norm summability whenever the real "
                        + "part of s is greater than one over beta six.")),
                Paragraph(Text(
                    "This is the next finite certificate in the golden Euler germ extraction "
                        + "ladder of OACTC parts 580 and 581. It advances the open local "
                        + "summability boundary from one over phi to the fifth power to one "
                        + "over beta six. It does not assert O-5, the Riemann Hypothesis, a "
                        + "global continuation or nonvanishing theorem, or an all-order "
                        + "extraction."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderLedger")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderExponentCensus")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula x = Call("x", p);
        Formula y = Call("y", p);
        Formula tail = Call("T7", p);
        Formula k3 = Call("K3", p);
        Formula c4 = Call("C4", p);
        Formula h4 = Call("H4", p);
        Formula r4 = Call("R4", p);
        Formula betaSix = Call("o5Beta", F.D(6));
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));

        Formula xDefinition = F.Seq(
            x, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)));
        Formula yDefinition = F.Seq(
            y, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed)));
        Formula tailDefinition = F.Seq(
            tail, F.Sp, F.Colon, F.Eq, F.Sp, Tail(s, p));
        Formula k3Definition = F.Seq(
            k3, F.Sp, F.Colon, F.Eq, F.Sp,
            ThirdNormalizedFactor(s, p, x, y));
        Formula c4Definition = F.Seq(
            c4, F.Sp, F.Colon, F.Eq, F.Sp, Correction(x, y));
        Formula h4Definition = F.Seq(
            h4, F.Sp, F.Colon, F.Eq, F.Sp, RemainderPolynomial(x, y));
        Formula r4Definition = F.Seq(
            r4, F.Sp, F.Colon, F.Eq, F.Sp,
            Remainder(x, y, tail, h4));

        Formula firstCorrectionWeight = MixedWeight(
            F.D(1), F.D(2), phiSquared, phiCubed);
        Formula secondCorrectionWeight = MixedWeight(
            F.D(3), F.D(1), phiSquared, phiCubed);
        Formula supportCertificate = SupportCertificate(
            betaSix, phiSquared, phiCubed);
        Formula identity = F.Seq(
            F.Forall, F.Sp, p, F.InMacro, F.Sp, PrimeNumbers(), F.Comma,
            F.Sp, c4, F.Sp, F.Times, F.Sp, k3,
            F.Sp, F.Eq, F.Sp, F.D(1), F.Sp, F.Plus, F.Sp, r4);
        Formula summable = Call("Summable", F.Seq(
            p, F.Colon, F.Sp, PrimeNumbers(), F.Sp, F.Mapsto, F.Sp,
            F.Lvert, c4, F.Sp, F.Times, F.Sp, k3,
            F.Sp, F.Minus, F.Sp, F.D(1), F.Rvert));

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma),
            F.Seq(
                Fraction(F.D(1), betaSix), F.Sp, F.Lt, F.Sp,
                F.Re, F.Open, s, F.Close, F.Sp, F.Rightarrow),
            F.Seq(xDefinition, F.Comma, F.Sp, yDefinition, F.Comma),
            F.Seq(tailDefinition, F.Comma),
            F.Seq(k3Definition, F.Comma),
            F.Seq(c4Definition, F.Comma),
            F.Seq(h4Definition, F.Comma),
            F.Seq(r4Definition, F.Comma),
            F.Seq(
                firstCorrectionWeight, F.Sp, F.Lt, F.Sp, betaSix,
                F.Sp, F.Land, F.Sp,
                secondCorrectionWeight, F.Sp, F.Lt, F.Sp, betaSix,
                F.Comma),
            F.Seq(supportCertificate, F.Comma),
            F.Seq(identity, F.Comma, F.Sp, summable, F.Dot),
        ]));
    }

    private static Formula ThirdNormalizedFactor(
        Formula s,
        Formula p,
        Formula x,
        Formula y)
    {
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
            Power(oneMinusYSquared, NegativeOne()),
            F.Sp, F.Times, F.Sp, oneMinusXSquaredY,
            F.Sp, F.Times, F.Sp, oneMinusY,
            F.Sp, F.Times, F.Sp, Power(onePlusX, NegativeOne()),
            F.Sp, F.Times, F.Sp, Call("germLocalFactor", s, p));
    }

    private static Formula Correction(Formula x, Formula y)
    {
        Formula first = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp,
            x, F.Sp, F.Times, F.Sp, Power(y, F.D(2))));
        Formula second = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp,
            Power(x, F.D(3)), F.Sp, F.Times, F.Sp, y));
        return F.Seq(
            first, F.Sp, F.Times, F.Sp, Power(second, NegativeOne()));
    }

    private static Formula Remainder(
        Formula x,
        Formula y,
        Formula tail,
        Formula h4)
    {
        Formula xDenominator = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp,
            Power(x, F.D(3)), F.Sp, F.Times, F.Sp, y));
        Formula yDenominator = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp, Power(y, F.D(2))));
        Formula linearDenominator = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Plus, F.Sp, x));
        Formula firstTailFactor = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp,
            x, F.Sp, F.Times, F.Sp, Power(y, F.D(2))));
        Formula secondTailFactor = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp,
            Power(x, F.D(2)), F.Sp, F.Times, F.Sp, y));
        Formula thirdTailFactor = Parenthesize(F.Seq(
            F.D(1), F.Sp, F.Minus, F.Sp, y));
        Formula numerator = Parenthesize(F.Seq(
            h4, F.Sp, F.Plus, F.Sp,
            firstTailFactor, F.Sp, F.Times, F.Sp,
            secondTailFactor, F.Sp, F.Times, F.Sp,
            thirdTailFactor, F.Sp, F.Times, F.Sp, tail));

        return F.Seq(
            Power(xDenominator, NegativeOne()), F.Sp, F.Times, F.Sp,
            Power(yDenominator, NegativeOne()), F.Sp, F.Times, F.Sp,
            Power(linearDenominator, NegativeOne()), F.Sp, F.Times, F.Sp,
            numerator);
    }

    private static Formula RemainderPolynomial(Formula x, Formula y) =>
        F.Seq(
            F.Minus, Monomial(x, 5, y, 6),
            F.Sp, F.Plus, F.Sp, Monomial(x, 5, y, 4),
            F.Sp, F.Minus, F.Sp, Monomial(x, 4, y, 6),
            F.Sp, F.Plus, F.Sp, Monomial(x, 4, y, 4),
            F.Sp, F.Minus, F.Sp, Monomial(x, 4, y, 2),
            F.Sp, F.Plus, F.Sp, Monomial(x, 4, y, 1),
            F.Sp, F.Plus, F.Sp, Monomial(x, 3, y, 4),
            F.Sp, F.Minus, F.Sp, Monomial(x, 3, y, 3),
            F.Sp, F.Plus, F.Sp, Monomial(x, 2, y, 5),
            F.Sp, F.Minus, F.Sp, Monomial(x, 2, y, 2),
            F.Sp, F.Plus, F.Sp, Monomial(x, 1, y, 4),
            F.Sp, F.Minus, F.Sp, Monomial(x, 1, y, 3));

    private static Formula SupportCertificate(
        Formula betaSix,
        Formula phiSquared,
        Formula phiCubed)
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula support = F.Seq(
            F.OpenBrace,
            Pair(5, 6), F.Comma, F.Sp, Pair(5, 4), F.Comma, F.Sp,
            Pair(4, 6), F.Comma, F.Sp, Pair(4, 4), F.Comma, F.Sp,
            Pair(4, 2), F.Comma, F.Sp, Pair(4, 1), F.Comma, F.Sp,
            Pair(3, 4), F.Comma, F.Sp, Pair(3, 3), F.Comma, F.Sp,
            Pair(2, 5), F.Comma, F.Sp, Pair(2, 2), F.Comma, F.Sp,
            Pair(1, 4), F.Comma, F.Sp, Pair(1, 3),
            F.CloseBrace);
        return F.Seq(
            F.Forall, F.Sp, a, F.Comma, F.Sp, b,
            F.InMacro, F.Sp, NaturalNumbers(), F.Comma, F.Sp,
            Parenthesize(F.Seq(a, F.Comma, F.Sp, b)),
            F.InMacro, F.Sp, support, F.Sp, F.Rightarrow, F.Sp,
            betaSix, F.Sp, F.Leq, F.Sp,
            MixedWeight(a, b, phiSquared, phiCubed));
    }

    private static Formula Tail(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Seq(F.Id("k"), F.Geq, F.D(7))),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("k")))));

    private static Formula Monomial(
        Formula x,
        byte xExponent,
        Formula y,
        byte yExponent) =>
        F.Seq(
            Power(x, F.D(xExponent)), F.Sp, F.Times, F.Sp,
            Power(y, F.D(yExponent)));

    private static Formula Pair(byte first, byte second) =>
        Parenthesize(F.Seq(F.D(first), F.Comma, F.Sp, F.D(second)));

    private static Formula MixedWeight(
        Formula a,
        Formula b,
        Formula phiSquared,
        Formula phiCubed) =>
        F.Seq(
            a, F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Plus, F.Sp,
            b, F.Sp, F.Times, F.Sp, phiCubed);

    private static Formula Parenthesize(Formula body) =>
        F.Seq(F.Open, body, F.Close);

    private static Formula NegativeOne() =>
        F.Seq(F.Minus, F.D(1));

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula PrimeNumbers() =>
        Call("Primes", NaturalNumbers());

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
