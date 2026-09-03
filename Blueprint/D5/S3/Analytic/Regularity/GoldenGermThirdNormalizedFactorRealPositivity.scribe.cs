using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Regularity;

internal sealed class GoldenGermThirdNormalizedFactorRealPositivityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRealPositivity."
            + "golden_germ_third_normalized_factor_real_axis_positivity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third normalized golden germ product is real and strictly positive "
            + "at every real point above one over phi to the fifth.",
        H("Golden Germ Third Normalized Factor Real Positivity"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-third-normalized-factor-real-axis-positivity"),
            DeclarationHandle.Create(Declaration),
            H("The third normalized factor is positive on the full real ray"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem is the next real-axis sign step in the golden Euler germ "
                        + "extraction ladder of OACTC parts 580 and 581. It closes the "
                        + "remaining sign boundary for the third normalized factor by "
                        + "strengthening frozen real-point nonvanishing to strict positivity "
                        + "on the entire ray above one over phi to the fifth.")),
                Paragraph(Text(
                    "For a positive real sigma, each prime-local factor is represented over "
                        + "the reals. Both prime powers x and y lie strictly between zero and "
                        + "one. Consequently the inverse factor one minus y-squared, the "
                        + "mixed factor one minus x-squared times y, the factor one minus y, "
                        + "and the inverse factor one plus x are all strictly positive. The "
                        + "local germ series is also positive because it is a convergent sum "
                        + "of nonnegative terms whose vacuum term is one.")),
                Paragraph(Text(
                    "The frozen third-order factorization supplies summability of the local "
                        + "deviations from one. This yields a genuine real Multipliable "
                        + "family and nonnegativity of its product through finite positive "
                        + "subproducts. Frozen real-point nonvanishing from the regularity "
                        + "theorem rules out zero local factors, so the summable one-plus "
                        + "product theorem makes the infinite product nonzero and hence "
                        + "strictly positive.")),
                Paragraph(Text(
                    "Real powers and the real local series are transported to their complex "
                        + "counterparts before the real infinite product is mapped into the "
                        + "complex numbers. The resulting product therefore has imaginary "
                        + "part zero and strictly positive real part.")),
                Paragraph(Text(
                    "The conclusion concerns only positive real points above the displayed "
                        + "threshold and only the third normalized product. It does not assert "
                        + "O-5, RH, complex nonvanishing on the whole half-plane, boundary "
                        + "regularity, or any all-order extraction statement."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRegularity")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula thresholdFifth = Fraction(F.D(1), Power(F.Varphi, F.D(5)));
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
        Formula conclusion = And(
            Equal(ImaginaryPart(Call("G3", sigma)), F.D(0)),
            LessThan(F.D(0), RealPart(Call("G3", sigma))));
        Formula positivity = F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(), F.Comma, F.Sp,
            thresholdFifth, F.Sp, F.Lt, F.Sp, sigma,
            F.Sp, F.Rightarrow, F.Sp, conclusion);

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma,
                F.Sp, p, F.InMacro, F.Sp, primes, F.Comma),
            F.Seq(
                xDefinition, F.Comma, F.Sp, yDefinition, F.Comma, F.Sp,
                kpDefinition, F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(positivity, F.Dot),
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

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Open, value, F.Close);

    private static Formula ImaginaryPart(Formula value) =>
        Call("Im", value);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

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
