using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Regularity;

internal sealed class GoldenGermThirdNormalizedFactorRegularityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRegularity."
            + "golden_germ_third_normalized_factor_regularity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third normalized golden germ product is holomorphic above one over phi "
            + "to the fifth, is zero-free on the established complex half-plane, and "
            + "is continuous and nonzero at one over phi to the fourth.",
        H("Golden Germ Third Normalized Factor Regularity"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-third-normalized-factor-regularity"),
            DeclarationHandle.Create(Declaration),
            H("The third normalized factor is regular beyond the phi-fifth threshold"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem is the regularity step after the third-order ledger and "
                        + "factorization in the golden Euler germ extraction ladder of OACTC "
                        + "Parts 580 and 581, on the RH-route O-5 control line. It advances "
                        + "the previously open analytic boundary by upgrading frozen "
                        + "pointwise deviation summability to a locally uniform product.")),
                Paragraph(Text(
                    "For every real sigma strictly above one over phi to the fifth, the "
                        + "proof splits the local series after six modes. Boundary-line "
                        + "norms for the retained mixed modes and tail form a prime-summable "
                        + "majorant valid simultaneously whenever the real part is at least "
                        + "sigma. The same estimates keep one plus x and one minus y-squared "
                        + "away from zero.")),
                Paragraph(Text(
                    "Each fixed-prime factor is holomorphic: its complex powers are entire "
                        + "in s, the two denominators are nonzero, and the germ-local series "
                        + "uses the frozen positive-half-plane analyticity theorem. Pinned "
                        + "Mathlib's locally uniform infinite-product theorem then makes the "
                        + "prime product holomorphic throughout the open target half-plane.")),
                Paragraph(Text(
                    "Complex nonvanishing is asserted only when the real part is at least "
                        + "three fifths, where the frozen germ product theorem forces every "
                        + "local germ factor to be nonzero. On the wider target region, every "
                        + "positive real point is nonzero because each real local series is a "
                        + "convergent sum of nonnegative terms with vacuum term one. This "
                        + "includes one over phi to the fourth, whose continuity follows from "
                        + "being an interior point of the holomorphy region.")),
                Paragraph(Text(
                    "The theorem does not assert complex nonvanishing on all of the half-plane "
                        + "above one over phi to the fifth, regularity on its boundary, a "
                        + "fourth or all-order extraction, O-5, or the Riemann hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderLedger")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GermProductNonvanishingAboveThreeFifths")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor")),
            // SL-008 split audit: orchestrator adds the Majorant document edge
            // after that prerequisite document has landed and frozen first.
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula sigma = F.Id("sigma");
        Formula p = F.Id("p");
        Formula u = F.Id("u");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula thresholdFourth = Fraction(F.D(1), Power(F.Varphi, F.D(4)));
        Formula thresholdFifth = Fraction(F.D(1), Power(F.Varphi, F.D(5)));
        Formula threeFifths = Fraction(F.D(3), F.D(5));
        Formula primes = Call("Primes", NaturalNumbers());
        Formula xAtSP = Call("x", s, p);
        Formula yAtSP = Call("y", s, p);
        Formula kpAtSP = Call("Kp", s, p);
        Formula gAtS = Call("G3", s);
        Formula xDefinition = F.Seq(
            xAtSP, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)));
        Formula yDefinition = F.Seq(
            yAtSP, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed)));
        Formula kpDefinition = F.Seq(
            kpAtSP, F.Sp, F.Colon, F.Eq, F.Sp,
            NormalizedFactor(LocalFactor(s, p), xAtSP, yAtSP));
        Formula gDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            gAtS, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(kpAtSP));
        Formula region = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, ComplexNumbers(), F.Sp, F.Mid, F.Sp,
            thresholdFifth, F.Sp, F.Lt, F.Sp,
            F.Re, F.Open, s, F.Close, F.CloseBrace);
        Formula deviationBound = F.Seq(
            new Formula.Norm(F.Seq(
                kpAtSP, F.Sp, F.Minus, F.Sp, F.D(1))),
            F.Sp, F.Leq, F.Sp, Call("u", p));
        Formula uniformBound = F.Seq(
            F.Forall, F.Sp, p, F.InMacro, F.Sp, primes, F.Comma, F.Sp,
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            sigma, F.Sp, F.Leq, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp, deviationBound);
        Formula majorant = F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(), F.Comma, F.Sp,
            thresholdFifth, F.Sp, F.Lt, F.Sp, sigma,
            F.Sp, F.Rightarrow, F.Sp,
            F.Exists, F.Sp, u, F.Colon, F.Sp, primes, F.Sp, F.To, F.Sp,
            RealNumbers(), F.Comma, F.Sp,
            Call("Summable", u), F.Sp, F.Land, F.Sp, uniformBound);
        Formula analytic = Call(
            "AnalyticOnNhd", ComplexNumbers(), F.Id("G3"), region);
        Formula complexNonzero = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            threeFifths, F.Sp, F.Leq, F.Sp,
            F.Re, F.Open, s, F.Close, F.Sp, F.Rightarrow, F.Sp,
            Call("G3", s), F.Sp, F.Neq, F.Sp, F.D(0));
        Formula realNonzero = F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(), F.Comma, F.Sp,
            thresholdFifth, F.Sp, F.Lt, F.Sp, sigma,
            F.Sp, F.Rightarrow, F.Sp,
            Call("G3", sigma), F.Sp, F.Neq, F.Sp, F.D(0));
        Formula continuity = Call("ContinuousAt", F.Id("G3"), thresholdFourth);
        Formula pointNonzero = F.Seq(
            Call("G3", thresholdFourth), F.Sp, F.Neq, F.Sp, F.D(0));

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma,
                F.Sp, p, F.InMacro, F.Sp, primes, F.Comma),
            F.Seq(
                xDefinition, F.Comma, F.Sp, yDefinition, F.Comma, F.Sp,
                kpDefinition, F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(F.Open, majorant, F.Close, F.Sp, F.Land),
            F.Seq(analytic, F.Sp, F.Land),
            F.Seq(F.Open, complexNonzero, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, realNonzero, F.Close, F.Sp, F.Land),
            F.Seq(continuity, F.Sp, F.Land),
            F.Seq(pointNonzero, F.Dot),
        ]));
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
