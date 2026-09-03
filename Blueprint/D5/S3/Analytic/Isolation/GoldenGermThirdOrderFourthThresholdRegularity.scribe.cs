using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenGermThirdOrderFourthThresholdRegularityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenGermThirdOrderFourthThresholdRegularity."
            + "golden_germ_third_order_fourth_threshold_regularity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit third golden continuation is analytic, nonzero, real, and "
            + "strictly negative at one over phi to the fourth power.",
        H("Golden Germ Third-Order Fourth-Threshold Regularity"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-third-order-fourth-threshold-regularity"),
            DeclarationHandle.Create(Declaration),
            H("The third continuation is regular and negative at the fourth threshold"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem is the pointwise sign step in the golden Euler germ "
                        + "extraction ladder of OACTC parts 580 and 581. The frozen "
                        + "third-order factorization fixes the normalized product G3 "
                        + "and the exact five-zeta continuation F3. The present node "
                        + "closes the next local boundary by evaluating that same "
                        + "continuation at one over phi to the fourth power.")),
                Paragraph(Text(
                    "At this point the five transported zeta arguments are one over "
                        + "phi squared, one over phi, two over phi squared, two over "
                        + "phi, and one plus one over phi squared. The first three lie "
                        + "strictly between zero and one, while the last two are "
                        + "strictly greater than one. The frozen positive-real sign "
                        + "theorem therefore makes exactly the first three zeta factors "
                        + "negative and the last two positive.")),
                Paragraph(Text(
                    "The frozen third normalized-factor regularity theorem supplies "
                        + "analyticity and nonvanishing of G3 at the point, and its "
                        + "real-axis positivity theorem supplies zero imaginary part "
                        + "and positive real part. Analyticity of the transported zeta "
                        + "factors follows away from their pole at one; the two "
                        + "denominator factors are nonzero before inversion. Multiplying "
                        + "three negative real factors and the remaining positive "
                        + "factors gives a nonzero negative real value.")),
                Paragraph(Text(
                    "STOPPING JUSTIFICATION: the conclusion concerns only the displayed "
                        + "third continuation at the single point one over phi to the "
                        + "fourth power. It does not assert O-5, the Riemann hypothesis, "
                        + "a zero-free complex region, or any all-order extraction."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRegularity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRealPositivity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/RiemannZetaPositiveRealSign")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula g = F.Id("G3");
        Formula continuation = F.Id("F3");
        Formula point = F.Id("a4");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula phiFourth = Power(F.Varphi, F.D(4));
        Formula xAtSP = Call("x", s, p);
        Formula yAtSP = Call("y", s, p);
        Formula kpAtSP = Call("Kp", s, p);
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
            Call("G3", s), F.Sp, F.Colon, F.Eq, F.Sp,
            PrimeProduct(kpAtSP));
        Formula zetaSquared = Call("riemannZeta",
            F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s));
        Formula zetaCubed = Call("riemannZeta",
            F.Seq(phiCubed, F.Sp, F.Times, F.Sp, s));
        Formula zetaDoubleSquared = Inverse(Call("riemannZeta",
            F.Seq(F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
                F.Sp, F.Times, F.Sp, s)));
        Formula zetaDoubleCubed = Inverse(Call("riemannZeta",
            F.Seq(F.D(2), F.Sp, F.Times, F.Sp, phiCubed,
                F.Sp, F.Times, F.Sp, s)));
        Formula mixedCoefficient = F.Seq(
            F.Open, F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Plus, F.Sp, phiCubed, F.Close);
        Formula zetaMixed = Call("riemannZeta",
            F.Seq(mixedCoefficient, F.Sp, F.Times, F.Sp, s));
        Formula continuationAtS = F.Seq(
            zetaSquared, F.Sp, F.Times, F.Sp,
            zetaCubed, F.Sp, F.Times, F.Sp,
            zetaDoubleSquared, F.Sp, F.Times, F.Sp,
            F.Open,
            zetaDoubleCubed, F.Sp, F.Times, F.Sp,
            zetaMixed, F.Sp, F.Times, F.Sp, Call("G3", s),
            F.Close);
        Formula continuationDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            Call("F3", s), F.Sp, F.Colon, F.Eq, F.Sp, continuationAtS);
        Formula pointDefinition = F.Seq(
            point, F.Sp, F.Colon, F.Eq, F.Sp,
            Fraction(F.D(1), phiFourth));
        Formula value = Call("F3", point);
        Formula conclusion = And(
            Call("AnalyticAt", continuation, point),
            And(
                NotEqual(value, F.D(0)),
                And(
                    Equal(ImaginaryPart(value), F.D(0)),
                    LessThan(RealPart(value), F.D(0)))));

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma,
                F.Sp, p, F.InMacro, F.Sp, Call("Primes", NaturalNumbers()),
                F.Comma),
            F.Seq(
                xDefinition, F.Comma, F.Sp, yDefinition, F.Comma, F.Sp,
                kpDefinition, F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(continuationDefinition, F.Comma),
            F.Seq(pointDefinition, F.Comma),
            F.Seq(conclusion, F.Dot),
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
            Inverse(oneMinusYSquared),
            F.Sp, F.Times, F.Sp, oneMinusXSquaredY,
            F.Sp, F.Times, F.Sp, oneMinusY,
            F.Sp, F.Times, F.Sp, Inverse(onePlusX),
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

    private static Formula Inverse(Formula value) =>
        Power(F.Seq(F.Open, value, F.Close), F.Seq(F.Minus, F.D(1)));

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

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

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
