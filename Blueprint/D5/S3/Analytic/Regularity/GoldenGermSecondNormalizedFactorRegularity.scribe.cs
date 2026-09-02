using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Regularity;

internal sealed class GoldenGermSecondNormalizedFactorRegularityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Regularity/GoldenGermSecondNormalizedFactorRegularity."
            + "golden_germ_second_normalized_factor_regularity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second normalized golden germ product is holomorphic above one over phi "
            + "to the fourth and is continuous and nonzero at the structural point "
            + "one over phi cubed.",
        H("Golden Germ Second Normalized Factor Regularity"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-second-normalized-factor-regularity"),
            DeclarationHandle.Create(Declaration),
            H("The second normalized factor is regular at the structural point "
                + "one over phi cubed"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem is the regularity step after the signed second-order "
                        + "factorization in the golden Euler germ extraction ladder of "
                        + "OACTC Parts 580 and 581, on the RH-route O-5 control line. It "
                        + "advances the previously open boundary by carrying the second "
                        + "normalized remainder across the structural point one over phi "
                        + "cubed.")),
                Paragraph(Text(
                    "For every real sigma above one over phi to the fourth, the proof "
                        + "splits each local series through its phi-fourth mode and builds "
                        + "a summable prime majorant for the normalized deviation. The "
                        + "locally uniform product theorem then gives holomorphy on the "
                        + "whole open half-plane.")),
                Paragraph(Text(
                    "At the structural point, each real germ-local series is a convergent "
                        + "sum of nonnegative terms with vacuum term one, hence is strictly "
                        + "positive. The two explicit real normalization factors are also "
                        + "nonzero. Frozen pointwise deviation summability then makes the "
                        + "infinite product nonzero.")),
                Paragraph(Text(
                    "The value one over phi cubed is the structural point given by "
                        + "D5.X_Frontier.Hearts.structuralPole. This theorem does not "
                        + "assert that the structural point is a pole; the pole conclusion "
                        + "is reserved for a later theorem. It does not claim regularity "
                        + "on the line with real part one over phi to the fourth, and does "
                        + "not prove or imply O-5 or the Riemann hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula h = F.Id("H");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula thresholdFourth = Fraction(F.D(1), Power(F.Varphi, F.D(4)));
        Formula structuralPole = Fraction(F.D(1), phiCubed);
        Formula local = LocalFactor(s, p);
        Formula normalized = NormalizedFactor(
            s, p, local, phiSquared, phiCubed);
        Formula hAtS = Call("H", s);
        Formula hDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            hAtS, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(normalized));
        Formula region = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, ComplexNumbers(), F.Sp, F.Mid, F.Sp,
            thresholdFourth, F.Sp, F.Lt, F.Sp,
            F.Re, F.Open, s, F.Close, F.CloseBrace);
        Formula analytic = Call(
            "AnalyticOnNhd", ComplexNumbers(), h, region);
        Formula continuous = Call("ContinuousAt", h, structuralPole);
        Formula nonzero = F.Seq(
            Call("H", structuralPole), F.Sp, F.Neq, F.Sp, F.D(0));

        return F.Disp(new Formula.Aligned([
            F.Seq(h, F.Colon, F.Sp, ComplexNumbers(), F.Sp, F.To, F.Sp,
                ComplexNumbers(), F.Comma),
            F.Seq(hDefinition, F.Comma),
            F.Seq(analytic, F.Sp, F.Land),
            F.Seq(continuous, F.Sp, F.Land),
            F.Seq(nonzero, F.Dot),
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
