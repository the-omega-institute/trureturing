using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenGermFirstPoleAsymptoticDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenGermFirstPoleAsymptotic."
            + "golden_germ_first_pole_asymptotic";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden Euler germ has a positive right-hand first-pole asymptotic.",
        H("Golden Germ First-Pole Asymptotic"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-first-pole-asymptotic"),
            DeclarationHandle.Create(Declaration),
            H("The first golden pole has a positive quantitative asymptotic"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem is the next real-boundary node in the golden "
                        + "Euler germ extraction ladder of OACTC parts 580 and 581. "
                        + "It advances the remaining "
                        + "boundary from an explicit complex residue and real-axis "
                        + "positivity to a directional quantitative asymptotic.")),
                Paragraph(Text(
                    "Let a be one over phi squared, P the golden Euler prime "
                        + "product, and c equal G(a) over phi squared. Pulling the "
                        + "frozen punctured complex residue limit back along the real "
                        + "embedding and applying the frozen factorization gives real "
                        + "part convergence of (sigma-a)P(sigma) to the positive c. "
                        + "The frozen real-axis theorem makes the scaled imaginary "
                        + "part identically zero on the right-hand ray.")),
                Paragraph(Text(
                    "Since sigma-a approaches zero through positive values, its "
                        + "reciprocal tends to positive infinity. Multiplying that "
                        + "reciprocal by the scaled real part, whose limit c.re is "
                        + "strictly positive, proves that Re(P(sigma)) tends to "
                        + "positive infinity.")),
                Paragraph(Text(
                    "STOPPING JUSTIFICATION: this is only a local, right-hand real-axis "
                        + "statement at the first golden pole. It does not assert a "
                        + "Tauberian theorem, coefficient asymptotics, O-5, the Riemann "
                        + "hypothesis, a complex zero-free region, or behavior at any "
                        + "other boundary point."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenGermZetaResidue")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermZetaFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermRealAxisPositivity")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula productName = F.Id("P");
        Formula factorName = F.Id("G");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula a = Fraction(F.D(1), phiSquared);
        Formula productAtSigma = Call("P", sigma);
        Formula factorAtS = Call("G", s);
        Formula factorAtA = Call("G", a);
        Formula c = F.Seq(
            factorAtA, F.Sp, F.Slash, F.Sp, phiSquared);
        Formula normalized = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Close, F.Sp, F.Times, F.Sp, LocalFactor(s, p));
        Formula productDefinition = F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(),
            F.Comma, F.Sp, productAtSigma, F.Sp, F.Colon, F.Eq, F.Sp,
            PrimeProduct(LocalFactor(sigma, p)));
        Formula factorDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(),
            F.Comma, F.Sp, factorAtS, F.Sp, F.Colon, F.Eq, F.Sp,
            PrimeProduct(normalized));
        Formula scaledProduct = F.Seq(
            F.Open, sigma, F.Sp, F.Minus, F.Sp, a, F.Close,
            F.Sp, F.Times, F.Sp, productAtSigma);
        Formula rightNhood = Call("nhdsWithin", a, Call("Ioi", a));
        Formula realLimit = Call(
            "Tendsto",
            RealLambda(sigma, RealPart(scaledProduct)),
            rightNhood,
            Call("nhds", RealPart(c)));
        Formula imaginaryLimit = Call(
            "Tendsto",
            RealLambda(sigma, ImaginaryPart(scaledProduct)),
            rightNhood,
            Call("nhds", F.D(0)));
        Formula positiveBlowup = Call(
            "Tendsto",
            RealLambda(sigma, RealPart(productAtSigma)),
            rightNhood,
            F.Id("atTop"));

        return F.Disp(new Formula.Aligned([
            F.Seq(productName, F.Colon, F.Sp, RealNumbers(), F.Sp,
                F.To, F.Sp, ComplexNumbers(), F.Comma),
            F.Seq(productDefinition, F.Comma),
            F.Seq(factorName, F.Colon, F.Sp, ComplexNumbers(), F.Sp,
                F.To, F.Sp, ComplexNumbers(), F.Comma),
            F.Seq(factorDefinition, F.Comma),
            F.Seq(F.Id("a"), F.Sp, F.Colon, F.Eq, F.Sp, a, F.Comma),
            F.Seq(F.Id("c"), F.Sp, F.Colon, F.Eq, F.Sp, c, F.Comma),
            F.Seq(realLimit, F.Sp, F.Land),
            F.Seq(imaginaryLimit, F.Sp, F.Land),
            F.Seq(positiveBlowup, F.Dot),
        ]));
    }

    private static Formula RealLambda(Formula variable, Formula body) =>
        F.Seq(
            F.Open, variable, F.Colon, F.Sp, RealNumbers(), F.Close,
            F.Sp, F.Mapsto, F.Sp, body);

    private static Formula LocalFactor(Formula variable, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, variable, F.Sp, F.Times, F.Sp,
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
