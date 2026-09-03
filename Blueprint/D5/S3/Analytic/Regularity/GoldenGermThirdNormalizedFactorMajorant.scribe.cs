using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Regularity;

internal sealed class GoldenGermThirdNormalizedFactorMajorantDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorMajorant."
            + "golden_germ_third_normalized_factor_majorant";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third normalized golden germ factors admit a summable uniform "
            + "prime majorant and a locally uniformly convergent product.",
        H("Golden Germ Third Normalized Factor Majorant"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-third-normalized-factor-majorant"),
            DeclarationHandle.Create(Declaration),
            H("The third normalized factors satisfy a locally uniform M-test"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each real sigma strictly above one over phi to the fifth, "
                        + "the six retained modes and the remaining local tail are "
                        + "bounded by one prime-summable real family uniformly on the "
                        + "closed half-plane with real part at least sigma.")),
                Paragraph(Text(
                    "The same estimates keep both inverse factors away from zero. "
                        + "Consequently every deviation is differentiable on the open "
                        + "half-plane and the finite prime products converge there "
                        + "locally uniformly to the canonical infinite product.")),
                Paragraph(Text(
                    "This theorem supplies convergence and regularity infrastructure. "
                        + "It asserts no product nonvanishing, no boundary convergence, "
                        + "no all-order extraction, O-5, or the Riemann hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula sigma = F.Id("sigma");
        Formula p = F.Id("p");
        Formula u = F.Id("u");
        Formula f = F.Id("f");
        Formula g = F.Id("G3");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula threshold = Fraction(F.D(1), Power(F.Varphi, F.D(5)));
        Formula primes = Call("Primes", NaturalNumbers());
        Formula x = Call("x", s, p);
        Formula y = Call("y", s, p);
        Formula kp = Call("Kp", s, p);
        Formula xDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            F.Forall, F.Sp, p, F.InMacro, F.Sp, primes, F.Comma, F.Sp,
            x, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)));
        Formula yDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            F.Forall, F.Sp, p, F.InMacro, F.Sp, primes, F.Comma, F.Sp,
            y, F.Sp, F.Colon, F.Eq, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed)));
        Formula kpDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            F.Forall, F.Sp, p, F.InMacro, F.Sp, primes, F.Comma, F.Sp,
            kp, F.Sp, F.Colon, F.Eq, F.Sp,
            NormalizedFactor(LocalFactor(s, p), x, y));
        Formula fDefinition = F.Seq(
            Call("f", p, s), F.Sp, F.Colon, F.Eq, F.Sp,
            kp, F.Sp, F.Minus, F.Sp, F.D(1));
        Formula gDefinition = F.Seq(
            Call("G3", s), F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(kp));
        Formula region = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, ComplexNumbers(), F.Sp, F.Mid, F.Sp,
            sigma, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close, F.CloseBrace);
        Formula bound = F.Seq(
            F.Forall, F.Sp, p, F.InMacro, F.Sp, primes, F.Comma, F.Sp,
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            sigma, F.Sp, F.Leq, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            new Formula.Norm(Call("f", p, s)), F.Sp, F.Leq, F.Sp, Call("u", p));
        Formula majorant = F.Seq(
            F.Exists, F.Sp, u, F.Colon, F.Sp, primes, F.Sp, F.To, F.Sp,
            RealNumbers(), F.Comma, F.Sp,
            Call("Summable", u), F.Sp, F.Land, F.Sp, bound);
        Formula differentiable = F.Seq(
            F.Forall, F.Sp, p, F.InMacro, F.Sp, primes, F.Comma, F.Sp,
            Call("DifferentiableOn", ComplexNumbers(), Call("f", p), region));
        Formula onePlusF = F.Seq(
            F.Open, p, F.Comma, F.Sp, s, F.Close, F.Sp, F.Mapsto, F.Sp,
            F.D(1), F.Sp, F.Plus, F.Sp, Call("f", p, s));
        Formula locallyUniform = Call(
            "HasProdLocallyUniformlyOn", onePlusF, g, region);

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(), F.Comma,
                F.Sp, threshold, F.Sp, F.Lt, F.Sp, sigma,
                F.Sp, F.Rightarrow),
            F.Seq(xDefinition, F.Comma, F.Sp, yDefinition, F.Comma),
            F.Seq(kpDefinition, F.Comma),
            F.Seq(fDefinition, F.Comma, F.Sp, gDefinition, F.Comma),
            F.Seq(F.Open, majorant, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, differentiable, F.Close, F.Sp, F.Land),
            F.Seq(locallyUniform, F.Dot),
        ]));
    }

    private static Formula NormalizedFactor(Formula local, Formula x, Formula y)
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
